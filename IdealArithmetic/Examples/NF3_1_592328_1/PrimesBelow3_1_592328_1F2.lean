
import IdealArithmetic.Examples.NF3_1_592328_1.RI3_1_592328_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![19, -24, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![19, -24, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![19, 59, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![19, -24, 1], ![-265, -6, -145], ![4740, -588, 66]]]
  hmulB := by decide  
  f := ![![![-18, 24, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -59, 83]], ![![0, -1, 1], ![30, 103, -145], ![42, -54, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [69, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 82], [0, 1]]
 g := ![![[27, 77], [5, 31], [40], [70], [20, 41], [1]], ![[0, 6], [20, 52], [40], [70], [80, 42], [1]]]
 h' := ![![[46, 82], [70, 49], [7, 23], [32, 17], [31, 30], [14, 46], [0, 1]], ![[0, 1], [0, 34], [69, 60], [67, 66], [0, 53], [55, 37], [46, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [27, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [69, 37, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2388, -1269, 1246]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-314, -901, 1246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-21, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-21, 1, 0]] 
 ![![83, 0, 0], ![62, 1, 0], ![17, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-21, 1, 0], ![3, -19, 6], ![-193, 23, -22]]]
  hmulB := by decide  
  f := ![![![15526, -106509, 33654], ![-5146, -465547, 0]], ![![11602, -79545, 25134], ![-3817, -347687, 0]], ![![3178, -21815, 6893], ![-1062, -95353, 0]]]
  g := ![![![1, 0, 0], ![-62, 83, 0], ![-17, 0, 83]], ![![-1, 1, 0], ![13, -19, 6], ![-15, 23, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![19, -24, 1]] ![![83, 0, 0], ![-21, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1743, 83, 0]], ![![1577, -1992, 83], ![-664, 498, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-21, 1, 0]]], ![![![19, -24, 1]], ![![-8, 6, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-3, 39, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-3, 39, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![86, 39, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-3, 39, 1], ![-76, 98, 233], ![-7419, 861, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -39, 89]], ![![-1, 0, 1], ![-226, -101, 233], ![-65, 18, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [87, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 88], [0, 1]]
 g := ![![[59, 44], [88], [55], [84, 2], [30, 40], [1]], ![[0, 45], [88], [55], [53, 87], [33, 49], [1]]]
 h' := ![![[29, 88], [43, 20], [32, 55], [79, 77], [60, 64], [2, 29], [0, 1]], ![[0, 1], [0, 69], [25, 34], [87, 12], [47, 25], [42, 60], [29, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [21, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [87, 60, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![769, -2610, 3541]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3413, -1581, 3541]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![34, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![34, 1, 0]] 
 ![![89, 0, 0], ![34, 1, 0], ![19, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![34, 1, 0], ![3, 36, 6], ![-193, 23, 33]]]
  hmulB := by decide  
  f := ![![![2723, 39583, 6600], ![1513, -97900, 0]], ![![1022, 15113, 2520], ![624, -37380, 0]], ![![571, 8450, 1409], ![350, -20900, 0]]]
  g := ![![![1, 0, 0], ![-34, 89, 0], ![-19, 0, 89]], ![![0, 1, 0], ![-15, 36, 6], ![-18, 23, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-3, 39, 1]] ![![89, 0, 0], ![34, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3026, 89, 0]], ![![-267, 3471, 89], ![-178, 1424, 267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![34, 1, 0]]], ![![![-3, 39, 1]], ![![-2, 16, 3]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-23, 49, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-23, 49, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![74, 49, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-23, 49, 1], ![-46, 98, 293], ![-9349, 1091, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -49, 97]], ![![-1, 0, 1], ![-224, -147, 293], ![-59, 36, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [23, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 96], [0, 1]]
 g := ![![[80, 66], [93], [27], [4], [2], [3, 1]], ![[84, 31], [93], [27], [4], [2], [6, 96]]]
 h' := ![![[3, 96], [4, 58], [94, 53], [91, 67], [59, 95], [28, 83], [0, 1]], ![[0, 1], [81, 39], [59, 44], [1, 30], [53, 2], [83, 14], [3, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [21, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [23, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-751334, -777696, 915974]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-706530, -470726, 915974]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-2, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-2, 1, 0]] 
 ![![97, 0, 0], ![95, 1, 0], ![49, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-2, 1, 0], ![3, 0, 6], ![-193, 23, -3]]]
  hmulB := by decide  
  f := ![![![4751, 1, 9504], ![-97, -153648, 0]], ![![4654, 0, 9306], ![1, -150447, 0]], ![![2401, 0, 4801], ![0, -77616, 0]]]
  g := ![![![1, 0, 0], ![-95, 97, 0], ![-49, 0, 97]], ![![-1, 1, 0], ![-3, 0, 6], ![-23, 23, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-23, 49, 1]] ![![97, 0, 0], ![-2, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-194, 97, 0]], ![![-2231, 4753, 97], ![0, 0, 291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-2, 1, 0]]], ![![![-23, 49, 1]], ![![0, 0, 3]]]]
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
 ![![101, 0, 0], ![16, 1, 0], ![3, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![16, 1, 0], ![3, 18, 6], ![-193, 23, 15]]]
  hmulB := by decide  
  f := ![![![-3152, -19488, -6498], ![-606, 109383, 0]], ![![-497, -3077, -1026], ![-100, 17271, 0]], ![![-96, -579, -193], ![-3, 3249, 0]]]
  g := ![![![1, 0, 0], ![-16, 101, 0], ![-3, 0, 101]], ![![0, 1, 0], ![-3, 18, 6], ![-6, 23, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![17, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![17, 1, 0]] 
 ![![101, 0, 0], ![17, 1, 0], ![14, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![17, 1, 0], ![3, 19, 6], ![-193, 23, 16]]]
  hmulB := by decide  
  f := ![![![2, 113, 36], ![101, -606, 0]], ![![3, 19, 6], ![1, -101, 0]], ![![-11, 15, 5], ![81, -84, 0]]]
  g := ![![![1, 0, 0], ![-17, 101, 0], ![-14, 0, 101]], ![![0, 1, 0], ![-4, 19, 6], ![-8, 23, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-34, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-34, 1, 0]] 
 ![![101, 0, 0], ![67, 1, 0], ![38, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-34, 1, 0], ![3, -32, 6], ![-193, 23, -35]]]
  hmulB := by decide  
  f := ![![![20133, -247653, 46452], ![-9191, -781942, 0]], ![![13366, -164260, 30810], ![-6059, -518635, 0]], ![![7596, -93177, 17477], ![-3395, -294196, 0]]]
  g := ![![![1, 0, 0], ![-67, 101, 0], ![-38, 0, 101]], ![![-1, 1, 0], ![19, -32, 6], ![-4, 23, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![16, 1, 0]] ![![101, 0, 0], ![17, 1, 0]]
  ![![101, 0, 0], ![29, -11, 1]] where
 M := ![![![10201, 0, 0], ![1717, 101, 0]], ![![1616, 101, 0], ![275, 35, 6]]]
 hmul := by decide  
 g := ![![![![72, 11, -1], ![101, 0, 0]], ![![-12, 12, -1], ![101, 0, 0]]], ![![![-13, 12, -1], ![101, 0, 0]], ![![1, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![29, -11, 1]] ![![101, 0, 0], ![-34, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3434, 101, 0]], ![![2929, -1111, 101], ![-1212, 404, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-34, 1, 0]]], ![![![29, -11, 1]], ![![-12, 4, -1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [64, 84, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 30, 64], [85, 72, 39], [0, 1]]
 g := ![![[77, 83, 32], [17, 91, 91], [59, 72, 33], [61, 30], [19, 4], [1]], ![[52, 74, 76, 32], [30, 9, 0, 9], [69, 17, 8, 23], [52, 16], [21, 13], [43, 45, 88, 9]], ![[11, 70, 99, 86], [59, 34, 30, 71], [3, 92, 50, 75], [4, 59], [52, 55], [40, 88, 87, 94]]]
 h' := ![![[16, 30, 64], [45, 50, 54], [35, 73, 83], [26, 36, 62], [99, 42, 37], [39, 19, 101], [0, 1]], ![[85, 72, 39], [83, 16, 84], [89, 54, 39], [59, 59, 73], [20, 41, 99], [5, 68, 42], [16, 30, 64]], ![[0, 1], [12, 37, 68], [25, 79, 84], [53, 8, 71], [0, 20, 70], [54, 16, 63], [85, 72, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 67], []]
 b := ![[], [41, 86, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [64, 84, 2, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11562780, 2647100, -1145257]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-112260, 25700, -11119]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-10, 27, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-10, 27, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![97, 27, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-10, 27, 1], ![-112, 67, 161], ![-5103, 585, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -27, 107]], ![![-1, 0, 1], ![-147, -40, 161], ![-35, 9, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [80, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 106], [0, 1]]
 g := ![![[75, 1], [48, 1], [36], [82, 47], [42], [99, 1]], ![[67, 106], [40, 106], [36], [27, 60], [42], [91, 106]]]
 h' := ![![[99, 106], [12, 106], [28, 1], [74, 101], [68, 49], [105, 91], [0, 1]], ![[0, 1], [20, 1], [20, 106], [15, 6], [104, 58], [19, 16], [99, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [97, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [80, 8, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2261, -1182, 1478]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1361, -384, 1478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![53, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![53, 1, 0]] 
 ![![107, 0, 0], ![53, 1, 0], ![14, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![53, 1, 0], ![3, 55, 6], ![-193, 23, 52]]]
  hmulB := by decide  
  f := ![![![23127, 577342, 63000], ![16906, -1123500, 0]], ![![11413, 285921, 31200], ![8454, -556400, 0]], ![![3022, 75540, 8243], ![2220, -147000, 0]]]
  g := ![![![1, 0, 0], ![-53, 107, 0], ![-14, 0, 107]], ![![0, 1, 0], ![-28, 55, 6], ![-20, 23, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-10, 27, 1]] ![![107, 0, 0], ![53, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5671, 107, 0]], ![![-1070, 2889, 107], ![-642, 1498, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![53, 1, 0]]], ![![![-10, 27, 1]], ![![-6, 14, 2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [57, 17, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 42, 47], [94, 66, 62], [0, 1]]
 g := ![![[29, 69, 89], [79, 34], [44, 60, 82], [19, 69, 104], [65, 108], [1]], ![[99, 58, 75, 17], [68, 45], [77, 94, 79, 79], [36, 35, 72, 42], [107, 66], [86, 18, 95, 55]], ![[44, 57, 67, 6], [83, 83], [86, 83, 37, 85], [64, 101, 79, 98], [20, 20], [103, 96, 36, 54]]]
 h' := ![![[91, 42, 47], [76, 52, 31], [108, 23, 19], [7, 68, 54], [89, 18, 70], [52, 92, 76], [0, 1]], ![[94, 66, 62], [14, 90, 21], [82, 101, 46], [98, 105, 2], [93, 36, 16], [57, 77, 75], [91, 42, 47]], ![[0, 1], [62, 76, 57], [18, 94, 44], [33, 45, 53], [93, 55, 23], [19, 49, 67], [94, 66, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 75], []]
 b := ![[], [53, 65, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [57, 17, 33, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305274447, -102795720, 50156895]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2800683, -943080, 460155]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [102, 74, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 61, 63], [37, 51, 50], [0, 1]]
 g := ![![[76, 64, 77], [72, 41], [76, 44], [40, 57], [22, 109, 57], [1]], ![[32, 106, 18, 49], [18, 1], [89, 9], [60, 72], [79, 103, 32, 11], [65, 91, 80, 91]], ![[21, 30, 31, 22], [30, 15], [40, 2], [67, 4], [19, 30, 40, 30], [15, 53, 104, 22]]]
 h' := ![![[45, 61, 63], [110, 41, 23], [30, 33, 70], [18, 15, 48], [16, 31, 82], [11, 39, 82], [0, 1]], ![[37, 51, 50], [28, 76, 27], [13, 32, 112], [86, 99, 3], [68, 45, 33], [84, 81, 85], [45, 61, 63]], ![[0, 1], [105, 109, 63], [112, 48, 44], [89, 112, 62], [16, 37, 111], [81, 106, 59], [37, 51, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 94], []]
 b := ![[], [98, 105, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [102, 74, 31, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-230294, 36612, -12882]
  a := ![-2, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2038, 324, -114]
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


def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-45, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-45, 1, 0]] 
 ![![127, 0, 0], ![82, 1, 0], ![59, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-45, 1, 0], ![3, -43, 6], ![-193, 23, -46]]]
  hmulB := by decide  
  f := ![![![16792, -281887, 39342], ![-8128, -832739, 0]], ![![10855, -181978, 25398], ![-5206, -537591, 0]], ![![7829, -130956, 18277], ![-3697, -386863, 0]]]
  g := ![![![1, 0, 0], ![-82, 127, 0], ![-59, 0, 127]], ![![-1, 1, 0], ![25, -43, 6], ![5, 23, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1383, -224, 100]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1383, -224, 100]] 
 ![![127, 0, 0], ![89, 1, 0], ![90, 0, 1]] where
  M :=![![![1383, -224, 100], ![-19972, 3235, -1444], ![54032, -8752, 3907]]]
  hmulB := by decide  
  f := ![![![1257, -32, -44]], ![![947, -21, -32]], ![![902, -16, -29]]]
  g := ![![![97, -224, 100], ![-1401, 3235, -1444], ![3790, -8752, 3907]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-45, 1, 0]] ![![127, 0, 0], ![-45, 1, 0]]
  ![![1257, -32, -44]] where
 M := ![![![16129, 0, 0], ![-5715, 127, 0]], ![![-5715, 127, 0], ![2028, -88, 6]]]
 hmul := by decide  
 g := ![![![![175641, -28448, 12700]], ![![-82207, 13315, -5944]]], ![![![-82207, 13315, -5944]], ![![38476, -6232, 2782]]]]
 hle2 := by decide  
def MulI127N1 : IdealMulLeCertificate' Table 
  ![![1257, -32, -44]] ![![1383, -224, 100]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![40, -62, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![40, -62, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![40, 69, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![40, -62, 1], ![-379, -61, -373], ![12074, -1462, 125]]]
  hmulB := by decide  
  f := ![![![-39, 62, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -69, 131]], ![![0, -1, 1], ![111, 196, -373], ![54, -77, 125]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [116, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 130], [0, 1]]
 g := ![![[113, 58], [83, 58], [5], [39], [108], [64], [1]], ![[42, 73], [12, 73], [5], [39], [108], [64], [1]]]
 h' := ![![[123, 130], [66, 53], [90, 78], [43, 108], [84, 68], [6, 34], [15, 123], [0, 1]], ![[0, 1], [35, 78], [121, 53], [96, 23], [64, 63], [127, 97], [79, 8], [123, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [76, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [116, 8, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5556, -3676, 4826]
  a := ![7, 5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1516, -2570, 4826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-20, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-20, 1, 0]] 
 ![![131, 0, 0], ![111, 1, 0], ![6, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-20, 1, 0], ![3, -18, 6], ![-193, 23, -21]]]
  hmulB := by decide  
  f := ![![![24533, -151595, 50544], ![-4847, -1103544, 0]], ![![20792, -128435, 42822], ![-4060, -934947, 0]], ![![1138, -6944, 2315], ![-128, -50544, 0]]]
  g := ![![![1, 0, 0], ![-111, 131, 0], ![-6, 0, 131]], ![![-1, 1, 0], ![15, -18, 6], ![-20, 23, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![40, -62, 1]] ![![131, 0, 0], ![-20, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-2620, 131, 0]], ![![5240, -8122, 131], ![-1179, 1179, -393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-20, 1, 0]]], ![![![40, -62, 1]], ![![-9, 9, -3]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [75, 82, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 25, 53], [121, 111, 84], [0, 1]]
 g := ![![[88, 17, 72], [116, 99], [67, 74], [58, 78, 88], [47, 121], [97, 1], []], ![[125, 34, 129, 90], [82, 64], [71, 115], [1, 70, 13, 108], [128, 44], [94, 128], [27, 69]], ![[80, 16, 8, 113], [68, 63], [15, 44], [14, 67, 44, 43], [55, 119], [26, 77], [133, 69]]]
 h' := ![![[113, 25, 53], [61, 3, 49], [104, 63, 28], [34, 117, 99], [96, 81, 122], [123, 54, 11], [0, 0, 1], [0, 1]], ![[121, 111, 84], [91, 78, 118], [79, 11, 8], [91, 96, 65], [22, 25, 25], [13, 31, 110], [58, 42, 111], [113, 25, 53]], ![[0, 1], [131, 56, 107], [5, 63, 101], [50, 61, 110], [50, 31, 127], [32, 52, 16], [8, 95, 25], [121, 111, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 6], []]
 b := ![[], [67, 5, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [75, 82, 40, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16681120, 3811340, -1563855]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121760, 27820, -11415]
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



lemma PB218I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB218I2 : PrimesBelowBoundCertificateInterval O 79 137 218 where
  m := 11
  g := ![2, 2, 2, 3, 1, 2, 1, 1, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB218I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N0, I127N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I107N1, I127N0, I127N1, I131N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [], [], [I127N0, I127N0, I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
