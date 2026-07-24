
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![19, -13, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![19, -13, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![19, 70, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![19, -13, 1], ![29, 2, -64], ![-705, 395, -24]]]
  hmulB := by decide  
  f := ![![![-18, 13, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -70, 83]], ![![0, -1, 1], ![15, 54, -64], ![-3, 25, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [3, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 82], [0, 1]]
 g := ![![[52, 28], [4, 75], [17], [26], [27, 17], [1]], ![[0, 55], [7, 8], [17], [26], [31, 66], [1]]]
 h' := ![![[10, 82], [71, 51], [30, 18], [9, 10], [2, 62], [80, 10], [0, 1]], ![[0, 1], [0, 32], [44, 65], [26, 73], [41, 21], [14, 73], [10, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [2, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [3, 73, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111, 125, -1095]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, 925, -1095]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-19, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-19, 1, 0]] 
 ![![83, 0, 0], ![64, 1, 0], ![24, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-19, 1, 0], ![2, -20, 5], ![55, -30, -18]]]
  hmulB := by decide  
  f := ![![![462, -4799, 1200], ![-83, -19920, 0]], ![![352, -3699, 925], ![-82, -15355, 0]], ![![140, -1388, 347], ![4, -5760, 0]]]
  g := ![![![1, 0, 0], ![-64, 83, 0], ![-24, 0, 83]], ![![-1, 1, 0], ![14, -20, 5], ![29, -30, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![19, -13, 1]] ![![83, 0, 0], ![-19, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1577, 83, 0]], ![![1577, -1079, 83], ![-332, 249, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-19, 1, 0]]], ![![![19, -13, 1]], ![![-4, 3, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![29, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![29, 1, 0]] 
 ![![89, 0, 0], ![29, 1, 0], ![16, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![29, 1, 0], ![2, 28, 5], ![55, -30, 30]]]
  hmulB := by decide  
  f := ![![![-4892, -79437, -14190], ![-2403, 252582, 0]], ![![-1587, -25863, -4620], ![-800, 82236, 0]], ![![-885, -14281, -2551], ![-415, 45408, 0]]]
  g := ![![![1, 0, 0], ![-29, 89, 0], ![-16, 0, 89]], ![![0, 1, 0], ![-10, 28, 5], ![5, -30, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![31, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![31, 1, 0]] 
 ![![89, 0, 0], ![31, 1, 0], ![28, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![31, 1, 0], ![2, 30, 5], ![55, -30, 32]]]
  hmulB := by decide  
  f := ![![![-1514, -26901, -4485], ![-801, 79833, 0]], ![![-531, -9357, -1560], ![-266, 27768, 0]], ![![-500, -8464, -1411], ![-184, 25116, 0]]]
  g := ![![![1, 0, 0], ![-31, 89, 0], ![-28, 0, 89]], ![![0, 1, 0], ![-12, 30, 5], ![1, -30, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![29, 1, 0]] ![![89, 0, 0], ![29, 1, 0]]
  ![![89, 0, 0], ![44, -42, 1]] where
 M := ![![![7921, 0, 0], ![2581, 89, 0]], ![![2581, 89, 0], ![843, 57, 5]]]
 hmul := by decide  
 g := ![![![![45, 42, -1], ![89, 0, 0]], ![![-15, 43, -1], ![89, 0, 0]]], ![![![-15, 43, -1], ![89, 0, 0]], ![![7, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![44, -42, 1]] ![![89, 0, 0], ![31, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2759, 89, 0]], ![![3916, -3738, 89], ![1335, -1246, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![31, 1, 0]]], ![![![44, -42, 1]], ![![15, -14, -2]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-23, -33, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-23, -33, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![74, 64, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-23, -33, 1], ![-11, -20, -164], ![-1805, 995, -86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -64, 97]], ![![-1, -1, 1], ![125, 108, -164], ![47, 67, -86]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [76, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 96], [0, 1]]
 g := ![![[93, 65], [89], [12], [35], [16], [13, 1]], ![[65, 32], [89], [12], [35], [16], [26, 96]]]
 h' := ![![[13, 96], [23, 68], [26, 63], [29, 77], [78, 61], [79, 93], [0, 1]], ![[0, 1], [34, 29], [69, 34], [60, 20], [95, 36], [27, 4], [13, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [89, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [76, 84, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4889, 4250, -3853]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2889, 2586, -3853]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-30, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-30, 1, 0]] 
 ![![97, 0, 0], ![67, 1, 0], ![86, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-30, 1, 0], ![2, -31, 5], ![55, -30, -29]]]
  hmulB := by decide  
  f := ![![![5131, -91115, 14700], ![-2425, -285180, 0]], ![![3551, -62913, 10150], ![-1648, -196910, 0]], ![![4538, -80782, 13033], ![-2186, -252840, 0]]]
  g := ![![![1, 0, 0], ![-67, 97, 0], ![-86, 0, 97]], ![![-1, 1, 0], ![17, -31, 5], ![47, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-23, -33, 1]] ![![97, 0, 0], ![-30, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2910, 97, 0]], ![![-2231, -3201, 97], ![679, 970, -194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-30, 1, 0]]], ![![![-23, -33, 1]], ![![7, 10, -2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [53, 11, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 62, 69], [41, 38, 32], [0, 1]]
 g := ![![[75, 39, 30], [72, 19], [75, 7, 37], [70, 9], [15, 25], [1]], ![[13, 25, 58, 15], [65, 87], [35, 92, 69, 72], [76, 82], [43, 56], [84, 14, 61, 57]], ![[96, 48, 61, 12], [30, 64], [22, 21, 86, 62], [84, 76], [82, 47], [53, 68, 99, 44]]]
 h' := ![![[65, 62, 69], [5, 40, 63], [65, 46, 25], [63, 15, 21], [95, 80, 98], [48, 90, 5], [0, 1]], ![[41, 38, 32], [76, 94, 3], [17, 100, 84], [94, 0, 15], [48, 14, 53], [99, 20, 37], [65, 62, 69]], ![[0, 1], [20, 68, 35], [14, 56, 93], [69, 86, 65], [28, 7, 51], [58, 92, 59], [41, 38, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 83], []]
 b := ![[], [25, 94, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [53, 11, 96, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130162740, 791105326, -2098829288]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1288740, 7832726, -20780488]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![5, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![5, 1, 0]] 
 ![![103, 0, 0], ![5, 1, 0], ![17, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![5, 1, 0], ![2, 4, 5], ![55, -30, 6]]]
  hmulB := by decide  
  f := ![![![740, 1487, 1860], ![103, -38316, 0]], ![![31, 71, 90], ![104, -1854, 0]], ![![120, 245, 307], ![61, -6324, 0]]]
  g := ![![![1, 0, 0], ![-5, 103, 0], ![-17, 0, 103]], ![![0, 1, 0], ![-1, 4, 5], ![1, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![36, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![36, 1, 0]] 
 ![![103, 0, 0], ![36, 1, 0], ![78, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![36, 1, 0], ![2, 35, 5], ![55, -30, 37]]]
  hmulB := by decide  
  f := ![![![1503, 31946, 4565], ![927, -94039, 0]], ![![530, 11162, 1595], ![310, -32857, 0]], ![![1134, 24192, 3457], ![714, -71214, 0]]]
  g := ![![![1, 0, 0], ![-36, 103, 0], ![-78, 0, 103]], ![![0, 1, 0], ![-16, 35, 5], ![-17, -30, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-41, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-41, 1, 0]] 
 ![![103, 0, 0], ![62, 1, 0], ![68, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-41, 1, 0], ![2, -42, 5], ![55, -30, -40]]]
  hmulB := by decide  
  f := ![![![22, 419, -50], ![103, 1030, 0]], ![![30, 251, -30], ![104, 618, 0]], ![![-1, 277, -33], ![29, 680, 0]]]
  g := ![![![1, 0, 0], ![-62, 103, 0], ![-68, 0, 103]], ![![-1, 1, 0], ![22, -42, 5], ![45, -30, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![5, 1, 0]] ![![103, 0, 0], ![36, 1, 0]]
  ![![103, 0, 0], ![57, 8, 1]] where
 M := ![![![10609, 0, 0], ![3708, 103, 0]], ![![515, 103, 0], ![182, 40, 5]]]
 hmul := by decide  
 g := ![![![![46, -8, -1], ![103, 0, 0]], ![![-21, -7, -1], ![103, 0, 0]]], ![![![-52, -7, -1], ![103, 0, 0]], ![![-1, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![57, 8, 1]] ![![103, 0, 0], ![-41, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4223, 103, 0]], ![![5871, 824, 103], ![-2266, -309, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-41, 1, 0]]], ![![![57, 8, 1]], ![![-22, -3, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![41, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![41, 1, 0]] 
 ![![107, 0, 0], ![41, 1, 0], ![79, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![41, 1, 0], ![2, 40, 5], ![55, -30, 42]]]
  hmulB := by decide  
  f := ![![![-187, -3760, -470], ![0, 10058, 0]], ![![-72, -1440, -180], ![1, 3852, 0]], ![![-135, -2776, -347], ![-8, 7426, 0]]]
  g := ![![![1, 0, 0], ![-41, 107, 0], ![-79, 0, 107]], ![![0, 1, 0], ![-19, 40, 5], ![-19, -30, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-30, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-30, 1, 0]] 
 ![![107, 0, 0], ![77, 1, 0], ![7, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-30, 1, 0], ![2, -31, 5], ![55, -30, -29]]]
  hmulB := by decide  
  f := ![![![9059, -157567, 25420], ![-3959, -543988, 0]], ![![6537, -113372, 18290], ![-2781, -391406, 0]], ![![619, -10309, 1663], ![-165, -35588, 0]]]
  g := ![![![1, 0, 0], ![-77, 107, 0], ![-7, 0, 107]], ![![-1, 1, 0], ![22, -31, 5], ![24, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-11, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-11, 1, 0]] 
 ![![107, 0, 0], ![96, 1, 0], ![81, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-11, 1, 0], ![2, -12, 5], ![55, -30, -10]]]
  hmulB := by decide  
  f := ![![![8040, -48949, 20400], ![-1177, -436560, 0]], ![![7211, -43910, 18300], ![-1069, -391620, 0]], ![![6088, -37055, 15443], ![-875, -330480, 0]]]
  g := ![![![1, 0, 0], ![-96, 107, 0], ![-81, 0, 107]], ![![-1, 1, 0], ![7, -12, 5], ![35, -30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![41, 1, 0]] ![![107, 0, 0], ![-30, 1, 0]]
  ![![107, 0, 0], ![54, 2, 1]] where
 M := ![![![11449, 0, 0], ![-3210, 107, 0]], ![![4387, 107, 0], ![-1228, 10, 5]]]
 hmul := by decide  
 g := ![![![![53, -2, -1], ![107, 0, 0]], ![![-30, 1, 0], ![0, 0, 0]]], ![![![-13, -1, -1], ![107, 0, 0]], ![![-14, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![54, 2, 1]] ![![107, 0, 0], ![-11, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1177, 107, 0]], ![![5778, 214, 107], ![-535, 0, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-11, 1, 0]]], ![![![54, 2, 1]], ![![-5, 0, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [5, 104, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 71, 64], [93, 37, 45], [0, 1]]
 g := ![![[40, 26, 38], [16, 7], [89, 101, 87], [92, 46, 21], [28, 4], [1]], ![[35, 9, 38, 35], [74, 49], [82, 75, 10, 84], [3, 18, 6, 80], [87, 20], [24, 99, 10, 108]], ![[64, 88, 68, 20], [37, 48], [44, 35, 17, 25], [24, 93, 52, 20], [99, 74], [56, 22, 19, 1]]]
 h' := ![![[18, 71, 64], [1, 22, 93], [100, 80, 15], [85, 48, 14], [103, 70, 81], [104, 5, 2], [0, 1]], ![[93, 37, 45], [71, 88, 53], [88, 45, 7], [8, 38, 102], [84, 47, 65], [44, 76, 67], [18, 71, 64]], ![[0, 1], [78, 108, 72], [46, 93, 87], [18, 23, 102], [88, 101, 72], [93, 28, 40], [93, 37, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 75], []]
 b := ![[], [55, 1, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [5, 104, 107, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3616184, 2810456, -2384484]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33176, 25784, -21876]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-11, -19, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-11, -19, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![102, 94, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-11, -19, 1], ![17, -22, -94], ![-1035, 575, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -94, 113]], ![![-1, -1, 1], ![85, 78, -94], ![45, 55, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [94, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 112], [0, 1]]
 g := ![![[89, 53], [57], [16], [30], [63, 95], [109, 1]], ![[103, 60], [57], [16], [30], [22, 18], [105, 112]]]
 h' := ![![[109, 112], [79, 77], [76, 31], [87, 109], [67, 97], [37, 35], [0, 1]], ![[0, 1], [110, 36], [65, 82], [103, 4], [18, 16], [10, 78], [109, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [54, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [94, 4, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![340, 125, -750]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![680, 625, -750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-19, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-19, 1, 0]] 
 ![![113, 0, 0], ![94, 1, 0], ![60, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-19, 1, 0], ![2, -20, 5], ![55, -30, -18]]]
  hmulB := by decide  
  f := ![![![2883, -29954, 7490], ![-678, -169274, 0]], ![![2398, -24915, 6230], ![-564, -140798, 0]], ![![1535, -15905, 3977], ![-335, -89880, 0]]]
  g := ![![![1, 0, 0], ![-94, 113, 0], ![-60, 0, 113]], ![![-1, 1, 0], ![14, -20, 5], ![35, -30, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-11, -19, 1]] ![![113, 0, 0], ![-19, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2147, 113, 0]], ![![-1243, -2147, 113], ![226, 339, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-19, 1, 0]]], ![![![-11, -19, 1]], ![![2, 3, -1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [83, 86, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 37, 118], [93, 89, 9], [0, 1]]
 g := ![![[104, 65, 41], [124, 38, 50], [89, 9, 103], [107, 55, 70], [7, 4, 11], [1]], ![[33, 104, 39, 114], [27, 53, 116, 126], [5, 110, 32, 96], [14, 79, 77, 92], [60, 50, 32, 33], [70, 33, 0, 33]], ![[61, 81, 75, 31], [33, 52, 97, 42], [13, 53, 120, 35], [74, 72, 30, 99], [118, 90, 64, 32], [109, 87, 11, 94]]]
 h' := ![![[4, 37, 118], [122, 85, 101], [106, 62, 80], [9, 71, 105], [54, 113, 109], [44, 41, 97], [0, 1]], ![[93, 89, 9], [94, 54, 96], [60, 111, 85], [50, 119, 70], [7, 97, 48], [96, 2, 9], [4, 37, 118]], ![[0, 1], [8, 115, 57], [17, 81, 89], [110, 64, 79], [117, 44, 97], [36, 84, 21], [93, 89, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 40], []]
 b := ![[], [89, 76, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [83, 86, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2204339, 1515999, -695452]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17357, 11937, -5476]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![63, -13, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![63, -13, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![63, 118, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![63, -13, 1], ![29, 46, -64], ![-705, 395, 20]]]
  hmulB := by decide  
  f := ![![![-62, 13, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -118, 131]], ![![0, -1, 1], ![31, 58, -64], ![-15, -15, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [65, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 130], [0, 1]]
 g := ![![[48, 129], [97, 117], [114], [61], [3], [52], [1]], ![[0, 2], [23, 14], [114], [61], [3], [52], [1]]]
 h' := ![![[24, 130], [114, 28], [117, 36], [86, 30], [11, 42], [59, 93], [66, 24], [0, 1]], ![[0, 1], [0, 103], [64, 95], [20, 101], [102, 89], [64, 38], [118, 107], [24, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [15, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [65, 107, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2805, 2313, -2153]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1014, 1957, -2153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![64, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![64, 1, 0]] 
 ![![131, 0, 0], ![64, 1, 0], ![111, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![64, 1, 0], ![2, 63, 5], ![55, -30, 65]]]
  hmulB := by decide  
  f := ![![![-3493, -154391, -12255], ![-2882, 321081, 0]], ![![-1754, -75401, -5985], ![-1309, 156807, 0]], ![![-2969, -130820, -10384], ![-2423, 272061, 0]]]
  g := ![![![1, 0, 0], ![-64, 131, 0], ![-111, 0, 131]], ![![0, 1, 0], ![-35, 63, 5], ![-40, -30, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![63, -13, 1]] ![![131, 0, 0], ![64, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![8384, 131, 0]], ![![8253, -1703, 131], ![4061, -786, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![64, 1, 0]]], ![![![63, -13, 1]], ![![31, -6, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![6, 36, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![6, 36, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![6, 36, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![6, 36, 1], ![127, -60, 181], ![1990, -1075, 12]]]
  hmulB := by decide  
  f := ![![![-5, -36, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -36, 137]], ![![0, 0, 1], ![-7, -48, 181], ![14, -11, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [15, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 136], [0, 1]]
 g := ![![[8, 64], [64], [73], [98, 99], [87], [15], [1]], ![[0, 73], [64], [73], [0, 38], [87], [15], [1]]]
 h' := ![![[17, 136], [136, 129], [0, 129], [37, 22], [65, 109], [0, 19], [122, 17], [0, 1]], ![[0, 1], [0, 8], [1, 8], [0, 115], [0, 28], [49, 118], [0, 120], [17, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [94, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [15, 120, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![413, 971, -1735]
  a := ![4, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79, 463, -1735]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-44, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-44, 1, 0]] 
 ![![137, 0, 0], ![93, 1, 0], ![125, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-44, 1, 0], ![2, -45, 5], ![55, -30, -43]]]
  hmulB := by decide  
  f := ![![![-887, 23936, -2660], ![548, 72884, 0]], ![![-589, 16242, -1805], ![412, 49457, 0]], ![![-791, 21839, -2427], ![557, 66500, 0]]]
  g := ![![![1, 0, 0], ![-93, 137, 0], ![-125, 0, 137]], ![![-1, 1, 0], ![26, -45, 5], ![60, -30, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![6, 36, 1]] ![![137, 0, 0], ![-44, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6028, 137, 0]], ![![822, 4932, 137], ![-137, -1644, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-44, 1, 0]]], ![![![6, 36, 1]], ![![-1, -12, 1]]]]
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


lemma PB218I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB218I2 : PrimesBelowBoundCertificateInterval O 79 137 218 where
  m := 11
  g := ![2, 3, 2, 1, 3, 3, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB218I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
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
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I97N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N0, I89N1], [I97N1], [], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
