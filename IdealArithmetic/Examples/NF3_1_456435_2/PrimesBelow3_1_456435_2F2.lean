
import IdealArithmetic.Examples.NF3_1_456435_2.RI3_1_456435_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2518, -542, -239]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2518, -542, -239]] 
 ![![83, 0, 0], ![19, 1, 0], ![31, 0, 1]] where
  M :=![![![-2518, -542, -239], ![-38129, -8207, -3619], ![-57242, -12321, -5433]]]
  hmulB := by decide  
  f := ![![![1068, -33, -25]], ![![197, -1, -8]], ![![371, -23, -1]]]
  g := ![![![183, -542, -239], ![2771, -8207, -3619], ![4160, -12321, -5433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-16, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-16, 1, 0]] 
 ![![83, 0, 0], ![67, 1, 0], ![78, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-16, 1, 0], ![2, -13, 8], ![155, 17, -19]]]
  hmulB := by decide  
  f := ![![![7157, -48883, 30096], ![-1909, -312246, 0]], ![![5769, -39449, 24288], ![-1576, -251988, 0]], ![![6722, -45938, 28283], ![-1814, -293436, 0]]]
  g := ![![![1, 0, 0], ![-67, 83, 0], ![-78, 0, 83]], ![![-1, 1, 0], ![3, -13, 8], ![6, 17, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-3, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-3, 1, 0]] 
 ![![83, 0, 0], ![80, 1, 0], ![21, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-3, 1, 0], ![2, 0, 8], ![155, 17, -6]]]
  hmulB := by decide  
  f := ![![![4725, 2, 18920], ![-166, -196295, 0]], ![![4556, 1, 18232], ![-82, -189157, 0]], ![![1197, 0, 4787], ![0, -49665, 0]]]
  g := ![![![1, 0, 0], ![-80, 83, 0], ![-21, 0, 83]], ![![-1, 1, 0], ![-2, 0, 8], ![-13, 17, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2518, -542, -239]] ![![83, 0, 0], ![-16, 1, 0]]
  ![![83, 0, 0], ![-17, -20, 1]] where
 M := ![![![-208994, -44986, -19837], ![2159, 465, 205]]]
 hmul := by decide  
 g := ![![![![-2382, -382, -247], ![664, 0, 0]], ![![34, 15, 2], ![39, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-17, -20, 1]] ![![83, 0, 0], ![-3, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-249, 83, 0]], ![![-1411, -1660, 83], ![166, 0, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-3, 1, 0]]], ![![![-17, -20, 1]], ![![2, 0, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-7, -33, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-7, -33, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![82, 56, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-7, -33, 1], ![89, -89, -267], ![-5227, -548, 111]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -56, 89]], ![![-1, -1, 1], ![247, 167, -267], ![-161, -76, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [34, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 88], [0, 1]]
 g := ![![[47, 55], [79], [10], [52, 73], [59, 16], [1]], ![[0, 34], [79], [10], [77, 16], [34, 73], [1]]]
 h' := ![![[4, 88], [41, 12], [71, 48], [12, 30], [41, 47], [55, 4], [0, 1]], ![[0, 1], [0, 77], [85, 41], [43, 59], [51, 42], [71, 85], [4, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [86, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [34, 85, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2310, 3592, 1628]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1474, -984, 1628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![0, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![0, 1, 0]] 
 ![![89, 0, 0], ![0, 1, 0], ![67, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![0, 1, 0], ![2, 3, 8], ![155, 17, -3]]]
  hmulB := by decide  
  f := ![![![-89, -135, -360], ![0, 4005, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-67, -102, -271], ![33, 3015, 0]]]
  g := ![![![1, 0, 0], ![0, 89, 0], ![-67, 0, 89]], ![![0, 1, 0], ![-6, 3, 8], ![4, 17, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-7, -33, 1]] ![![89, 0, 0], ![0, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![0, 89, 0]], ![![-623, -2937, 89], ![89, -89, -267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![0, 1, 0]]], ![![![-7, -33, 1]], ![![1, -1, -3]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![8, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![8, 1, 0]] 
 ![![97, 0, 0], ![8, 1, 0], ![62, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![8, 1, 0], ![2, 11, 8], ![155, 17, 5]]]
  hmulB := by decide  
  f := ![![![10251, 57020, 41480], ![1455, -502945, 0]], ![![838, 4695, 3416], ![195, -41419, 0]], ![![6546, 36445, 26513], ![1005, -321470, 0]]]
  g := ![![![1, 0, 0], ![-8, 97, 0], ![-62, 0, 97]], ![![0, 1, 0], ![-6, 11, 8], ![-3, 17, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -6, 8]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-91, -6, 8]] 
 ![![97, 0, 0], ![10, 1, 0], ![81, 0, 1]] where
  M :=![![![-91, -6, 8], ![1228, 27, -72], ![-1826, 2, 79]]]
  hmulB := by decide  
  f := ![![![2277, 490, 216]], ![![590, 127, 56]], ![![2435, 524, 231]]]
  g := ![![![-7, -6, 8], ![70, 27, -72], ![-85, 2, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-18, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-18, 1, 0]] 
 ![![97, 0, 0], ![79, 1, 0], ![15, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-18, 1, 0], ![2, -15, 8], ![155, 17, -21]]]
  hmulB := by decide  
  f := ![![![683, -5249, 2800], ![-97, -33950, 0]], ![![553, -4274, 2280], ![-96, -27645, 0]], ![![111, -812, 433], ![14, -5250, 0]]]
  g := ![![![1, 0, 0], ![-79, 97, 0], ![-15, 0, 97]], ![![-1, 1, 0], ![11, -15, 8], ![-9, 17, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![8, 1, 0]] ![![-91, -6, 8]]
  ![![97, 0, 0], ![-14, 39, 1]] where
 M := ![![![-8827, -582, 776]], ![![500, -21, -8]]]
 hmul := by decide  
 g := ![![![![-77, -45, 7], ![97, 0, 0]]], ![![![18, -36, -1], ![89, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-14, 39, 1]] ![![97, 0, 0], ![-18, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1746, 97, 0]], ![![-1358, 3783, 97], ![485, -582, 291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-18, 1, 0]]], ![![![-14, 39, 1]], ![![5, -6, 3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![30, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![30, 1, 0]] 
 ![![101, 0, 0], ![30, 1, 0], ![28, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![30, 1, 0], ![2, 33, 8], ![155, 17, 27]]]
  hmulB := by decide  
  f := ![![![-9401, -177363, -43008], ![-4545, 542976, 0]], ![![-2802, -52655, -12768], ![-1312, 161196, 0]], ![![-2608, -49170, -11923], ![-1254, 150528, 0]]]
  g := ![![![1, 0, 0], ![-30, 101, 0], ![-28, 0, 101]], ![![0, 1, 0], ![-12, 33, 8], ![-11, 17, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![34, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![34, 1, 0]] 
 ![![101, 0, 0], ![34, 1, 0], ![45, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![34, 1, 0], ![2, 37, 8], ![155, 17, 31]]]
  hmulB := by decide  
  f := ![![![427, 9765, 2112], ![303, -26664, 0]], ![![142, 3255, 704], ![102, -8888, 0]], ![![165, 4350, 941], ![210, -11880, 0]]]
  g := ![![![1, 0, 0], ![-34, 101, 0], ![-45, 0, 101]], ![![0, 1, 0], ![-16, 37, 8], ![-18, 17, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![37, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![37, 1, 0]] 
 ![![101, 0, 0], ![37, 1, 0], ![93, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![37, 1, 0], ![2, 40, 8], ![155, 17, 34]]]
  hmulB := by decide  
  f := ![![![11611, 283930, 56800], ![7070, -717100, 0]], ![![4238, 103974, 20800], ![2627, -262600, 0]], ![![10673, 261440, 52301], ![6560, -660300, 0]]]
  g := ![![![1, 0, 0], ![-37, 101, 0], ![-93, 0, 101]], ![![0, 1, 0], ![-22, 40, 8], ![-36, 17, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![30, 1, 0]] ![![101, 0, 0], ![34, 1, 0]]
  ![![101, 0, 0], ![-49, 21, 1]] where
 M := ![![![10201, 0, 0], ![3434, 101, 0]], ![![3030, 101, 0], ![1022, 67, 8]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![34, 1, 0], ![0, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![14, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-49, 21, 1]] ![![101, 0, 0], ![37, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![3737, 101, 0]], ![![-4949, 2121, 101], ![-1616, 808, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![37, 1, 0]]], ![![![-49, 21, 1]], ![![-16, 8, 2]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [6, 37, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 8, 96], [72, 94, 7], [0, 1]]
 g := ![![[60, 39, 15], [71, 38, 9], [96, 9, 13], [6, 7], [85, 29], [1]], ![[58, 100, 58, 87], [71, 80, 1, 87], [12, 96, 41, 90], [39, 82], [38, 59], [40, 59, 50, 69]], ![[80, 42, 2, 13], [4, 97, 90, 61], [21, 46, 5, 72], [78, 23], [95, 41], [24, 92, 9, 34]]]
 h' := ![![[52, 8, 96], [89, 42, 85], [42, 8, 100], [100, 62, 61], [41, 9, 78], [97, 66, 21], [0, 1]], ![[72, 94, 7], [4, 60, 74], [97, 18, 74], [21, 58, 47], [7, 32, 59], [82, 26, 70], [52, 8, 96]], ![[0, 1], [12, 1, 47], [84, 77, 32], [75, 86, 98], [50, 62, 69], [38, 11, 12], [72, 94, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 91], []]
 b := ![[], [75, 42, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [6, 37, 82, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1018773, 628918, 323729]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9891, 6106, 3143]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [2, 21, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 7, 38], [93, 99, 69], [0, 1]]
 g := ![![[30, 21, 79], [6, 65, 62], [61, 83], [14, 2, 64], [97, 19], [1]], ![[65, 36, 80, 88], [20, 93, 92, 46], [93, 3], [96, 58, 73, 58], [38, 64], [13, 71, 58, 88]], ![[52, 4, 47, 100], [23, 52, 104, 10], [77, 35], [102, 67, 21, 57], [81, 76], [55, 38, 104, 19]]]
 h' := ![![[47, 7, 38], [95, 37, 20], [20, 105, 94], [79, 64, 61], [24, 42, 8], [105, 86, 33], [0, 1]], ![[93, 99, 69], [35, 15, 69], [20, 59, 28], [45, 89, 18], [80, 68, 34], [7, 71, 8], [47, 7, 38]], ![[0, 1], [60, 55, 18], [39, 50, 92], [73, 61, 28], [100, 104, 65], [35, 57, 66], [93, 99, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 64], []]
 b := ![[], [39, 10, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [2, 21, 74, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329525120782, -83477050878, -33434542092]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3079674026, -780159354, -312472356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-5, 33, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-5, 33, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![104, 33, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-5, 33, 1], ![221, 111, 261], ![5003, 574, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -33, 109]], ![![-1, 0, 1], ![-247, -78, 261], ![127, 31, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [78, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 108], [0, 1]]
 g := ![![[39, 7], [61], [93, 34], [9, 102], [48], [10, 1]], ![[0, 102], [61], [106, 75], [48, 7], [48], [20, 108]]]
 h' := ![![[10, 108], [41, 94], [49, 37], [61, 90], [33, 59], [92, 22], [0, 1]], ![[0, 1], [0, 15], [92, 72], [89, 19], [78, 50], [94, 87], [10, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [38, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [78, 99, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2986, 3641, 1818]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1762, -517, 1818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-43, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-43, 1, 0]] 
 ![![109, 0, 0], ![66, 1, 0], ![85, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-43, 1, 0], ![2, -40, 8], ![155, 17, -46]]]
  hmulB := by decide  
  f := ![![![1927, -47110, 9424], ![-1090, -128402, 0]], ![![1169, -28514, 5704], ![-653, -77717, 0]], ![![1496, -36737, 7349], ![-867, -100130, 0]]]
  g := ![![![1, 0, 0], ![-66, 109, 0], ![-85, 0, 109]], ![![-1, 1, 0], ![18, -40, 8], ![27, 17, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-5, 33, 1]] ![![109, 0, 0], ![-43, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4687, 109, 0]], ![![-545, 3597, 109], ![436, -1308, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-43, 1, 0]]], ![![![-5, 33, 1]], ![![4, -12, 2]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [29, 15, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 20, 16], [1, 92, 97], [0, 1]]
 g := ![![[62, 90, 106], [77, 18], [5, 98], [17, 106], [82, 97, 8], [1]], ![[65, 16, 31, 4], [102, 106], [38, 11], [19, 61], [93, 103, 73, 13], [78, 41, 74, 28]], ![[5, 21, 105, 112], [94, 31], [97, 69], [36, 44], [73, 40, 9, 106], [31, 25, 62, 85]]]
 h' := ![![[10, 20, 16], [31, 108, 85], [111, 34, 73], [97, 102, 95], [108, 75, 85], [84, 98, 11], [0, 1]], ![[1, 92, 97], [36, 100, 56], [13, 94, 28], [95, 70, 89], [9, 5, 93], [94, 25, 94], [10, 20, 16]], ![[0, 1], [22, 18, 85], [107, 98, 12], [35, 54, 42], [66, 33, 48], [6, 103, 8], [1, 92, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 8], []]
 b := ![[], [77, 69, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [29, 15, 102, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5754525, -1132938, -348492]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50925, -10026, -3084]
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

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-46, -10, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-46, -10, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![81, 117, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-46, -10, 1], ![135, -59, -83], ![-1662, -157, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -117, 127]], ![![-1, -1, 1], ![54, 76, -83], ![-15, -4, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [18, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 126], [0, 1]]
 g := ![![[44, 120], [52, 61], [42, 103], [48, 68], [114, 49], [97, 1]], ![[0, 7], [0, 66], [0, 24], [40, 59], [41, 78], [67, 126]]]
 h' := ![![[97, 126], [80, 45], [6, 51], [25, 22], [107, 24], [32, 120], [0, 1]], ![[0, 1], [0, 82], [0, 76], [0, 105], [22, 103], [115, 7], [97, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [115, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [18, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![318877, 252941, 155719]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96806, -141466, 155719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-44, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-44, 1, 0]] 
 ![![127, 0, 0], ![83, 1, 0], ![124, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-44, 1, 0], ![2, -41, 8], ![155, 17, -47]]]
  hmulB := by decide  
  f := ![![![17709, -430589, 84032], ![-9525, -1334008, 0]], ![![11573, -281375, 54912], ![-6222, -871728, 0]], ![![17308, -420418, 82047], ![-9250, -1302496, 0]]]
  g := ![![![1, 0, 0], ![-83, 127, 0], ![-124, 0, 127]], ![![-1, 1, 0], ![19, -41, 8], ![36, 17, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-46, -10, 1]] ![![127, 0, 0], ![-44, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-5588, 127, 0]], ![![-5842, -1270, 127], ![2159, 381, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-44, 1, 0]]], ![![![-46, -10, 1]], ![![17, 3, -1]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [17, 31, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 29, 89], [16, 101, 42], [0, 1]]
 g := ![![[46, 108, 125], [85, 65, 28], [50, 33], [116, 11], [45, 52], [20, 1], []], ![[79, 52, 84, 35], [130, 56, 54, 35], [89, 63], [99, 84], [30, 117], [100, 114], [94, 61]], ![[70, 71, 10, 8], [31, 75, 31, 76], [93, 25], [82, 4], [97, 63], [128, 55], [10, 61]]]
 h' := ![![[4, 29, 89], [127, 42, 115], [101, 129, 91], [77, 86, 65], [79, 22, 81], [53, 18, 107], [0, 0, 1], [0, 1]], ![[16, 101, 42], [62, 69, 26], [100, 17, 105], [33, 96, 71], [12, 44, 52], [103, 43, 95], [121, 80, 101], [4, 29, 89]], ![[0, 1], [78, 20, 121], [35, 116, 66], [100, 80, 126], [61, 65, 129], [111, 70, 60], [86, 51, 29], [16, 101, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 120], []]
 b := ![[], [13, 110, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [17, 31, 111, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-105717, 0, 13362]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-807, 0, 102]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![29, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![29, 1, 0]] 
 ![![137, 0, 0], ![29, 1, 0], ![124, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![29, 1, 0], ![2, 32, 8], ![155, 17, 26]]]
  hmulB := by decide  
  f := ![![![-5729, -98162, -24544], ![-1918, 420316, 0]], ![![-1240, -20766, -5192], ![-273, 88913, 0]], ![![-5204, -88848, -22215], ![-1648, 380432, 0]]]
  g := ![![![1, 0, 0], ![-29, 137, 0], ![-124, 0, 137]], ![![0, 1, 0], ![-14, 32, 8], ![-26, 17, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![33, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![33, 1, 0]] 
 ![![137, 0, 0], ![33, 1, 0], ![23, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![33, 1, 0], ![2, 36, 8], ![155, 17, 30]]]
  hmulB := by decide  
  f := ![![![-5843, -114680, -25488], ![-2192, 436482, 0]], ![![-1435, -27609, -6136], ![-410, 105079, 0]], ![![-986, -19253, -4279], ![-347, 73278, 0]]]
  g := ![![![1, 0, 0], ![-33, 137, 0], ![-23, 0, 137]], ![![0, 1, 0], ![-10, 36, 8], ![-8, 17, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-62, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-62, 1, 0]] 
 ![![137, 0, 0], ![75, 1, 0], ![91, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-62, 1, 0], ![2, -59, 8], ![155, 17, -65]]]
  hmulB := by decide  
  f := ![![![1595, -61647, 8360], ![-1096, -143165, 0]], ![![897, -33744, 4576], ![-547, -78364, 0]], ![![1059, -40948, 5553], ![-729, -95095, 0]]]
  g := ![![![1, 0, 0], ![-75, 137, 0], ![-91, 0, 137]], ![![-1, 1, 0], ![27, -59, 8], ![35, 17, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![29, 1, 0]] ![![137, 0, 0], ![33, 1, 0]]
  ![![137, 0, 0], ![0, -9, 1]] where
 M := ![![![18769, 0, 0], ![4521, 137, 0]], ![![3973, 137, 0], ![959, 65, 8]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![33, 1, 0], ![0, 0, 0]]], ![![![29, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![0, -9, 1]] ![![137, 0, 0], ![-62, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-8494, 137, 0]], ![![0, -1233, 137], ![137, 548, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-62, 1, 0]]], ![![![0, -9, 1]], ![![1, 4, -1]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB192I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB192I2 : PrimesBelowBoundCertificateInterval O 79 137 192 where
  m := 11
  g := ![3, 2, 3, 3, 1, 1, 2, 1, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB192I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
      exact NI137N2
  β := ![I83N0, I83N1, I83N2, I89N1, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I109N1, I127N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [], [], [I109N1], [], [I127N1], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
