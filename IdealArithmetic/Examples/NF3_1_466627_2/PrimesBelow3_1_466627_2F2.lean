
import IdealArithmetic.Examples.NF3_1_466627_2.RI3_1_466627_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![14, -32, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![14, -32, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![14, 51, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![14, -32, 1], ![133, 28, -32], ![-4256, -315, 28]]]
  hmulB := by decide  
  f := ![![![-13, 32, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -51, 83]], ![![0, -1, 1], ![7, 20, -32], ![-56, -21, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [77, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 82], [0, 1]]
 g := ![![[50, 69], [21, 64], [36], [16], [48, 28], [1]], ![[0, 14], [48, 19], [36], [16], [65, 55], [1]]]
 h' := ![![[51, 82], [43, 61], [73, 75], [40, 6], [39, 79], [6, 51], [0, 1]], ![[0, 1], [0, 22], [80, 8], [14, 77], [1, 4], [34, 32], [51, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [76, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [77, 32, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343, 129, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 12, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![32, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![32, 1, 0]] 
 ![![83, 0, 0], ![32, 1, 0], ![55, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![32, 1, 0], ![0, 32, 1], ![133, 14, 32]]]
  hmulB := by decide  
  f := ![![![353, 11, 0], ![-913, 0, 0]], ![![96, 3, 0], ![-248, 0, 0]], ![![237, 7, 0], ![-613, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 83, 0], ![-55, 0, 83]], ![![0, 1, 0], ![-13, 32, 1], ![-25, 14, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![14, -32, 1]] ![![83, 0, 0], ![32, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2656, 83, 0]], ![![1162, -2656, 83], ![581, -996, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![32, 1, 0]]], ![![![14, -32, 1]], ![![7, -12, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![16, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![16, 1, 0]] 
 ![![89, 0, 0], ![16, 1, 0], ![11, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![16, 1, 0], ![0, 16, 1], ![133, 14, 16]]]
  hmulB := by decide  
  f := ![![![529, 33, 0], ![-2937, 0, 0]], ![![80, 5, 0], ![-444, 0, 0]], ![![51, 3, 0], ![-283, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 89, 0], ![-11, 0, 89]], ![![0, 1, 0], ![-3, 16, 1], ![-3, 14, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-8, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-8, 1, 0]] 
 ![![89, 0, 0], ![81, 1, 0], ![25, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-8, 1, 0], ![0, -8, 1], ![133, 14, -8]]]
  hmulB := by decide  
  f := ![![![641, -80, 0], ![7120, 0, 0]], ![![585, -73, 0], ![6498, 0, 0]], ![![193, -24, 0], ![2144, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 89, 0], ![-25, 0, 89]], ![![-1, 1, 0], ![7, -8, 1], ![-9, 14, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![16, 1, 0]] ![![89, 0, 0], ![-8, 1, 0]]
  ![![89, 0, 0], ![-39, 8, 1]] where
 M := ![![![7921, 0, 0], ![-712, 89, 0]], ![![1424, 89, 0], ![-128, 8, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![31, -7, -1], ![89, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-39, 8, 1]] ![![89, 0, 0], ![-8, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-712, 89, 0]], ![![-3471, 712, 89], ![445, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-8, 1, 0]]], ![![![-39, 8, 1]], ![![5, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![17, -15, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![17, -15, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![17, 82, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![17, -15, 1], ![133, 31, -15], ![-1995, -77, 31]]]
  hmulB := by decide  
  f := ![![![-16, 15, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -82, 97]], ![![0, -1, 1], ![4, 13, -15], ![-26, -27, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 41, 1] where
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
 g := ![![[48, 96], [50], [66], [48], [95], [56, 1]], ![[89, 1], [50], [66], [48], [95], [15, 96]]]
 h' := ![![[56, 96], [20, 22], [73, 70], [44, 58], [52, 40], [33, 17], [0, 1]], ![[0, 1], [88, 75], [16, 27], [91, 39], [61, 57], [15, 80], [56, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [95, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [15, 41, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1621, 951, 247]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -199, 247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![15, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![15, 1, 0]] 
 ![![97, 0, 0], ![15, 1, 0], ![66, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![15, 1, 0], ![0, 15, 1], ![133, 14, 15]]]
  hmulB := by decide  
  f := ![![![166, 11, 0], ![-1067, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![108, 7, 0], ![-694, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 97, 0], ![-66, 0, 97]], ![![0, 1, 0], ![-3, 15, 1], ![-11, 14, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![17, -15, 1]] ![![97, 0, 0], ![15, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1455, 97, 0]], ![![1649, -1455, 97], ![388, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![15, 1, 0]]], ![![![17, -15, 1]], ![![4, -2, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-33, 48, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-33, 48, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![68, 48, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-33, 48, 1], ![133, -19, 48], ![6384, 805, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -48, 101]], ![![-1, 0, 1], ![-31, -23, 48], ![76, 17, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [53, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 100], [0, 1]]
 g := ![![[69, 20], [36], [99, 49], [95], [54], [80, 1]], ![[53, 81], [36], [80, 52], [95], [54], [59, 100]]]
 h' := ![![[80, 100], [36, 11], [5, 6], [6, 94], [71, 14], [2, 85], [0, 1]], ![[0, 1], [7, 90], [81, 95], [52, 7], [80, 87], [35, 16], [80, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [89, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [53, 21, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2539, -2, 122]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -58, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-48, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-48, 1, 0]] 
 ![![101, 0, 0], ![53, 1, 0], ![19, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-48, 1, 0], ![0, -48, 1], ![133, 14, -48]]]
  hmulB := by decide  
  f := ![![![2881, -60, 0], ![6060, 0, 0]], ![![1489, -31, 0], ![3132, 0, 0]], ![![599, -12, 0], ![1260, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 101, 0], ![-19, 0, 101]], ![![-1, 1, 0], ![25, -48, 1], ![3, 14, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-33, 48, 1]] ![![101, 0, 0], ![-48, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4848, 101, 0]], ![![-3333, 4848, 101], ![1717, -2323, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-48, 1, 0]]], ![![![-33, 48, 1]], ![![17, -23, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [54, 1, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 0, 19], [46, 102, 84], [0, 1]]
 g := ![![[92, 68, 26], [39, 72, 100], [77, 63, 76], [81, 15], [98, 72], [1]], ![[74, 35, 35, 93], [42, 96, 36, 93], [4, 12, 91, 59], [62, 38], [62, 33], [38, 72, 3, 61]], ![[27, 34, 25, 35], [100, 54, 30, 90], [86, 51, 19, 78], [99, 30], [93, 52], [90, 77, 47, 42]]]
 h' := ![![[79, 0, 19], [57, 92, 51], [65, 24, 93], [1, 47, 30], [96, 36, 18], [49, 102, 22], [0, 1]], ![[46, 102, 84], [21, 19, 49], [81, 71, 54], [84, 96, 39], [41, 37, 48], [89, 91, 62], [79, 0, 19]], ![[0, 1], [22, 95, 3], [83, 8, 59], [65, 63, 34], [40, 30, 37], [85, 13, 19], [46, 102, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 18], []]
 b := ![[], [44, 58, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [54, 1, 81, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-494091, -2781, 8343]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4797, -27, 81]
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


def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![25, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![25, 1, 0]] 
 ![![107, 0, 0], ![25, 1, 0], ![17, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![25, 1, 0], ![0, 25, 1], ![133, 14, 25]]]
  hmulB := by decide  
  f := ![![![651, 26, 0], ![-2782, 0, 0]], ![![125, 5, 0], ![-534, 0, 0]], ![![81, 3, 0], ![-346, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 107, 0], ![-17, 0, 107]], ![![0, 1, 0], ![-6, 25, 1], ![-6, 14, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![41, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![41, 1, 0]] 
 ![![107, 0, 0], ![41, 1, 0], ![31, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![41, 1, 0], ![0, 41, 1], ![133, 14, 41]]]
  hmulB := by decide  
  f := ![![![1354, 33, 0], ![-3531, 0, 0]], ![![492, 12, 0], ![-1283, 0, 0]], ![![344, 8, 0], ![-897, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 107, 0], ![-31, 0, 107]], ![![0, 1, 0], ![-16, 41, 1], ![-16, 14, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![25, 1, 0]] ![![107, 0, 0], ![41, 1, 0]]
  ![![107, 0, 0], ![-45, -41, 1]] where
 M := ![![![11449, 0, 0], ![4387, 107, 0]], ![![2675, 107, 0], ![1025, 66, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![41, 1, 0], ![0, 0, 0]]], ![![![25, 1, 0], ![0, 0, 0]], ![![10, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-45, -41, 1]] ![![107, 0, 0], ![41, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4387, 107, 0]], ![![-4815, -4387, 107], ![-1712, -1712, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![41, 1, 0]]], ![![![-45, -41, 1]], ![![-16, -16, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-57, 34, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-57, 34, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![52, 34, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-57, 34, 1], ![133, -43, 34], ![4522, 609, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -34, 109]], ![![-1, 0, 1], ![-15, -11, 34], ![62, 19, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [7, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 108], [0, 1]]
 g := ![![[52, 78], [82], [14, 34], [28, 93], [82], [72, 1]], ![[0, 31], [82], [64, 75], [75, 16], [82], [35, 108]]]
 h' := ![![[72, 108], [92, 29], [11, 55], [22, 19], [17, 86], [41, 54], [0, 1]], ![[0, 1], [0, 80], [47, 54], [82, 90], [105, 23], [5, 55], [72, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [22, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [7, 37, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![273, 124, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 8, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-34, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-34, 1, 0]] 
 ![![109, 0, 0], ![75, 1, 0], ![43, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-34, 1, 0], ![0, -34, 1], ![133, 14, -34]]]
  hmulB := by decide  
  f := ![![![3435, -101, 0], ![11009, 0, 0]], ![![2381, -70, 0], ![7631, 0, 0]], ![![1405, -41, 0], ![4503, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 109, 0], ![-43, 0, 109]], ![![-1, 1, 0], ![23, -34, 1], ![5, 14, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-57, 34, 1]] ![![109, 0, 0], ![-34, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3706, 109, 0]], ![![-6213, 3706, 109], ![2071, -1199, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-34, 1, 0]]], ![![![-57, 34, 1]], ![![19, -11, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![113, 0, 0], ![2, 1, 0], ![109, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![133, 14, 2]]]
  hmulB := by decide  
  f := ![![![-10, -2, 1]], ![![1, 0, 0]], ![![-12, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 14, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![23, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![23, 1, 0]] 
 ![![113, 0, 0], ![23, 1, 0], ![36, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![23, 1, 0], ![0, 23, 1], ![133, 14, 23]]]
  hmulB := by decide  
  f := ![![![1036, 45, 0], ![-5085, 0, 0]], ![![184, 8, 0], ![-903, 0, 0]], ![![304, 13, 0], ![-1492, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 113, 0], ![-36, 0, 113]], ![![0, 1, 0], ![-5, 23, 1], ![-9, 14, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-25, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-25, 1, 0]] 
 ![![113, 0, 0], ![88, 1, 0], ![53, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-25, 1, 0], ![0, -25, 1], ![133, 14, -25]]]
  hmulB := by decide  
  f := ![![![2701, -108, 0], ![12204, 0, 0]], ![![2126, -85, 0], ![9606, 0, 0]], ![![1281, -51, 0], ![5788, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 113, 0], ![-53, 0, 113]], ![![-1, 1, 0], ![19, -25, 1], ![2, 14, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0]] ![![113, 0, 0], ![23, 1, 0]]
  ![![113, 0, 0], ![46, 25, 1]] where
 M := ![![![226, 113, 0], ![46, 25, 1]]]
 hmul := by decide  
 g := ![![![![-44, -24, -1], ![113, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![46, 25, 1]] ![![113, 0, 0], ![-25, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2825, 113, 0]], ![![5198, 2825, 113], ![-1017, -565, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-25, 1, 0]]], ![![![46, 25, 1]], ![![-9, -5, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [121, 66, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 114, 126], [118, 12, 1], [0, 1]]
 g := ![![[49, 5, 13], [84, 97, 124], [115, 57, 69], [10, 92, 104], [101, 45, 72], [1]], ![[85, 89, 95, 75], [25, 53, 85, 90], [2, 36, 99, 53], [119, 2, 62, 45], [31, 4, 49, 53], [71, 49, 57, 126]], ![[83, 25, 83, 13], [11, 15, 77, 26], [30, 82, 124, 71], [126, 70, 23, 99], [64, 75, 48, 124], [59, 3, 67, 1]]]
 h' := ![![[40, 114, 126], [123, 95, 34], [55, 35, 39], [60, 98, 14], [98, 117, 55], [6, 61, 31], [0, 1]], ![[118, 12, 1], [101, 39, 59], [104, 80, 52], [53, 35, 70], [82, 2, 35], [37, 10, 57], [40, 114, 126]], ![[0, 1], [34, 120, 34], [21, 12, 36], [106, 121, 43], [60, 8, 37], [6, 56, 39], [118, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 26], []]
 b := ![[], [79, 55, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [121, 66, 96, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1536700, 325755, 60325]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12100, 2565, 475]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-24, -11, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-24, -11, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![107, 120, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-24, -11, 1], ![133, -10, -11], ![-1463, -21, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -120, 131]], ![![-1, -1, 1], ![10, 10, -11], ![-3, 9, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [110, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 130], [0, 1]]
 g := ![![[87, 108], [46, 59], [33], [60], [62], [49], [1]], ![[117, 23], [26, 72], [33], [60], [62], [49], [1]]]
 h' := ![![[124, 130], [49, 34], [77, 94], [63, 66], [47, 86], [29, 18], [21, 124], [0, 1]], ![[0, 1], [73, 97], [74, 37], [125, 65], [100, 45], [34, 113], [70, 7], [124, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [62, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [110, 7, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-694, 64, 18]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -16, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![11, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![11, 1, 0]] 
 ![![131, 0, 0], ![11, 1, 0], ![10, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![11, 1, 0], ![0, 11, 1], ![133, 14, 11]]]
  hmulB := by decide  
  f := ![![![111, 10, 0], ![-1310, 0, 0]], ![![-11, -1, 0], ![132, 0, 0]], ![![-10, -1, 0], ![120, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 131, 0], ![-10, 0, 131]], ![![0, 1, 0], ![-1, 11, 1], ![-1, 14, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-24, -11, 1]] ![![131, 0, 0], ![11, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![1441, 131, 0]], ![![-3144, -1441, 131], ![-131, -131, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![11, 1, 0]]], ![![![-24, -11, 1]], ![![-1, -1, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![3, -47, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![3, -47, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![3, 90, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![3, -47, 1], ![133, 17, -47], ![-6251, -525, 17]]]
  hmulB := by decide  
  f := ![![![-2, 47, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -90, 137]], ![![0, -1, 1], ![2, 31, -47], ![-46, -15, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [47, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 136], [0, 1]]
 g := ![![[51, 14], [105], [118], [59, 36], [123], [103], [1]], ![[58, 123], [105], [118], [77, 101], [123], [103], [1]]]
 h' := ![![[69, 136], [120, 39], [64, 70], [104, 114], [129, 6], [108, 73], [90, 69], [0, 1]], ![[0, 1], [71, 98], [99, 67], [24, 23], [132, 131], [76, 64], [56, 68], [69, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [83, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [47, 68, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![579, 656, 193]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -122, 193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![47, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![47, 1, 0]] 
 ![![137, 0, 0], ![47, 1, 0], ![120, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![47, 1, 0], ![0, 47, 1], ![133, 14, 47]]]
  hmulB := by decide  
  f := ![![![1364, 29, 0], ![-3973, 0, 0]], ![![470, 10, 0], ![-1369, 0, 0]], ![![1192, 25, 0], ![-3472, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 137, 0], ![-120, 0, 137]], ![![0, 1, 0], ![-17, 47, 1], ![-45, 14, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![3, -47, 1]] ![![137, 0, 0], ![47, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![6439, 137, 0]], ![![411, -6439, 137], ![274, -2192, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![47, 1, 0]]], ![![![3, -47, 1]], ![![2, -16, 0]]]]
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


lemma PB194I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB194I2 : PrimesBelowBoundCertificateInterval O 79 137 194 where
  m := 11
  g := ![2, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB194I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![17161, 131]
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
      exact NI89N1
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I97N1, I101N1, I107N0, I107N1, I109N1, I113N0, I113N1, I113N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N1], [I97N1], [I101N1], [], [I107N0, I107N1, I107N1], [I109N1], [I113N0, I113N1, I113N2], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
