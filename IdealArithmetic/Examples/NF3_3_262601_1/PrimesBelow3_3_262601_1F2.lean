
import IdealArithmetic.Examples.NF3_3_262601_1.RI3_3_262601_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 26, -8]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![131, 26, -8]] 
 ![![83, 0, 0], ![0, 83, 0], ![77, 59, 1]] where
  M :=![![![131, 26, -8], ![-1024, -195, 60], ![4352, 808, -255]]]
  hmulB := by decide  
  f := ![![![-15, -2, 0]], ![![0, -17, -4]], ![![-17, -15, -3]]]
  g := ![![![9, 6, -8], ![-68, -45, 60], ![289, 191, -255]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [46, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 82], [0, 1]]
 g := ![![[76, 70], [50, 27], [77], [78], [3, 17], [1]], ![[40, 13], [29, 56], [77], [78], [82, 66], [1]]]
 h' := ![![[73, 82], [24, 30], [19, 39], [18, 34], [28, 59], [37, 73], [0, 1]], ![[0, 1], [56, 53], [44, 44], [10, 49], [19, 24], [54, 10], [73, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [46, 10, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![430, 890, 371]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-339, -253, 371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 2, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![15, 2, 0]] 
 ![![83, 0, 0], ![49, 1, 0], ![20, 0, 1]] where
  M :=![![![15, 2, 0], ![0, 17, 4], ![256, 88, 13]]]
  hmulB := by decide  
  f := ![![![-131, -26, 8]], ![![-65, -13, 4]], ![![-84, -16, 5]]]
  g := ![![![-1, 2, 0], ![-11, 17, 4], ![-52, 88, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![131, 26, -8]] ![![15, 2, 0]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 23, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 23, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![78, 23, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 23, 1], ![128, 56, 45], ![2816, 1054, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -23, 89]], ![![-1, 0, 1], ![-38, -11, 45], ![22, 9, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [24, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 88], [0, 1]]
 g := ![![[52, 84], [49], [49], [17, 34], [88, 4], [1]], ![[62, 5], [49], [49], [38, 55], [80, 85], [1]]]
 h' := ![![[87, 88], [28, 23], [15, 7], [37, 82], [24, 37], [65, 87], [0, 1]], ![[0, 1], [71, 66], [1, 82], [51, 7], [39, 52], [69, 2], [87, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [60, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [24, 2, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1001, 1025, 714]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-637, -173, 714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![44, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![44, 1, 0]] 
 ![![89, 0, 0], ![44, 1, 0], ![78, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![44, 1, 0], ![0, 45, 2], ![128, 44, 43]]]
  hmulB := by decide  
  f := ![![![3741, 85, 0], ![-7565, 0, 0]], ![![1804, 41, 0], ![-3648, 0, 0]], ![![3246, 51, -1], ![-6564, 45, 0]]]
  g := ![![![1, 0, 0], ![-44, 89, 0], ![-78, 0, 89]], ![![0, 1, 0], ![-24, 45, 2], ![-58, 44, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-11, 23, 1]] ![![89, 0, 0], ![44, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3916, 89, 0]], ![![-979, 2047, 89], ![-356, 1068, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![44, 1, 0]]], ![![![-11, 23, 1]], ![![-4, 12, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [72, 28, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 45, 56], [8, 51, 41], [0, 1]]
 g := ![![[35, 66, 61], [76, 96], [90, 95], [52, 94], [52, 3], [1]], ![[91, 4, 28, 29], [69, 32], [17, 16], [5, 70], [12, 81], [25, 68, 27, 46]], ![[86, 13, 13, 84], [86, 89], [5, 53], [61, 85], [53, 70], [79, 67, 71, 51]]]
 h' := ![![[2, 45, 56], [65, 92, 35], [69, 24, 22], [70, 31, 80], [82, 32, 71], [25, 69, 10], [0, 1]], ![[8, 51, 41], [51, 69, 50], [84, 62, 41], [12, 30, 93], [88, 77, 78], [51, 85, 9], [2, 45, 56]], ![[0, 1], [17, 33, 12], [1, 11, 34], [78, 36, 21], [28, 85, 45], [62, 40, 78], [8, 51, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 85], []]
 b := ![[], [57, 11, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [72, 28, 87, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106312, -8148, -7760]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1096, -84, -80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -2, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-7, -2, 0]] 
 ![![101, 0, 0], ![54, 1, 0], ![30, 0, 1]] where
  M :=![![![-7, -2, 0], ![0, -9, -4], ![-256, -88, -5]]]
  hmulB := by decide  
  f := ![![![-307, -10, 8]], ![![-154, -5, 4]], ![![-114, -4, 3]]]
  g := ![![![1, -2, 0], ![6, -9, -4], ![46, -88, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201, -10, 6]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-201, -10, 6]] 
 ![![101, 0, 0], ![59, 1, 0], ![48, 0, 1]] where
  M :=![![![-201, -10, 6], ![768, 53, -26], ![-2048, -188, 79]]]
  hmulB := by decide  
  f := ![![![-701, -338, -58]], ![![-483, -233, -40]], ![![-688, -332, -57]]]
  g := ![![![1, -10, 6], ![-11, 53, -26], ![52, -188, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -12, -2]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-27, -12, -2]] 
 ![![101, 0, 0], ![89, 1, 0], ![35, 0, 1]] where
  M :=![![![-27, -12, -2], ![-256, -127, -22], ![-1280, -612, -105]]]
  hmulB := by decide  
  f := ![![![129, 36, -10]], ![![101, 29, -8]], ![![103, 24, -7]]]
  g := ![![![11, -12, -2], ![117, -127, -22], ![563, -612, -105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-7, -2, 0]] ![![-201, -10, 6]]
  ![![-129, -36, 10]] where
 M := ![![![-129, -36, 10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-129, -36, 10]] ![![-27, -12, -2]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![925, 172, -52]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![925, 172, -52]] 
 ![![103, 0, 0], ![0, 103, 0], ![4, 68, 1]] where
  M :=![![![925, 172, -52], ![-6656, -1191, 396], ![28672, 5384, -1587]]]
  hmulB := by decide  
  f := ![![![-2349, -68, 60]], ![![7680, 223, -196]], ![![4820, 140, -123]]]
  g := ![![![11, 36, -52], ![-80, -273, 396], ![340, 1100, -1587]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [41, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 102], [0, 1]]
 g := ![![[102, 98], [43, 9], [3, 15], [33], [64], [41, 1]], ![[0, 5], [0, 94], [0, 88], [33], [64], [82, 102]]]
 h' := ![![[41, 102], [91, 43], [83, 3], [86, 18], [10, 62], [70, 95], [0, 1]], ![[0, 1], [0, 60], [0, 100], [0, 85], [80, 41], [51, 8], [41, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [39, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [41, 62, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-536, 1806, 793]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -506, 793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2349, -68, 60]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-2349, -68, 60]] 
 ![![103, 0, 0], ![71, 1, 0], ![19, 0, 1]] where
  M :=![![![-2349, -68, 60], ![7680, 223, -196], ![-16384, -472, 419]]]
  hmulB := by decide  
  f := ![![![925, 172, -52]], ![![573, 107, -32]], ![![449, 84, -25]]]
  g := ![![![13, -68, 60], ![-43, 223, -196], ![89, -472, 419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![925, 172, -52]] ![![-2349, -68, 60]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [95, 104, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 14, 91], [5, 92, 16], [0, 1]]
 g := ![![[13, 63, 101], [61, 10, 34], [52, 64], [14, 2, 44], [70, 27], [1]], ![[29, 81, 24, 17], [29, 80, 86, 91], [77, 19], [49, 12, 6, 2], [35, 4], [69, 65, 37, 77]], ![[49, 12, 13, 102], [3, 45, 3, 49], [92, 90], [65, 58, 24, 3], [57, 29], [71, 43, 51, 30]]]
 h' := ![![[49, 14, 91], [90, 34, 23], [65, 76, 26], [61, 79, 99], [21, 71, 30], [12, 3, 54], [0, 1]], ![[5, 92, 16], [10, 37, 74], [80, 56, 106], [36, 91, 33], [27, 12, 19], [28, 72, 105], [49, 14, 91]], ![[0, 1], [90, 36, 10], [90, 82, 82], [22, 44, 82], [24, 24, 58], [14, 32, 55], [5, 92, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 66], []]
 b := ![[], [45, 105, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [95, 104, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-277665, -160500, -34454]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2595, -1500, -322]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [76, 70, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 73, 93], [23, 35, 16], [0, 1]]
 g := ![![[23, 12, 3], [61, 29], [33, 75, 36], [4, 60, 15], [57, 34], [1]], ![[63, 50, 21, 20], [80, 16], [90, 67, 67, 27], [29, 87, 105, 100], [102, 46], [53, 58, 40, 46]], ![[61, 87, 4, 84], [91, 105], [61, 95, 108, 28], [38, 86, 20, 93], [90, 3], [16, 22, 64, 63]]]
 h' := ![![[105, 73, 93], [52, 95, 60], [108, 40, 62], [23, 31, 6], [27, 33, 61], [33, 39, 19], [0, 1]], ![[23, 35, 16], [29, 28, 35], [88, 81, 4], [11, 79, 41], [89, 43, 81], [50, 73, 41], [105, 73, 93]], ![[0, 1], [98, 95, 14], [93, 97, 43], [97, 108, 62], [12, 33, 76], [51, 106, 49], [23, 35, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 1], []]
 b := ![[], [8, 91, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [76, 70, 90, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![152425709, 93872544, 22301073]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1398401, 861216, 204597]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![36, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![0, 20, 2], ![128, 44, 18]]]
  hmulB := by decide  
  f := ![![![77, 4, 0], ![-452, 0, 0]], ![![-19, -1, 0], ![114, 0, 0]], ![![2, -10, -1], ![-10, 57, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-36, 0, 113]], ![![0, 1, 0], ![-4, 20, 2], ![-12, 44, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3033, -524, 168]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-3033, -524, 168]] 
 ![![113, 0, 0], ![43, 1, 0], ![71, 0, 1]] where
  M :=![![![-3033, -524, 168], ![21504, 3835, -1216], ![-88576, -16000, 5051]]]
  hmulB := by decide  
  f := ![![![85415, 41276, 7096]], ![![40541, 19591, 3368]], ![![92385, 44644, 7675]]]
  g := ![![![67, -524, 168], ![-505, 3835, -1216], ![2131, -16000, 5051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![51, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![51, 1, 0]] 
 ![![113, 0, 0], ![51, 1, 0], ![30, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![51, 1, 0], ![0, 52, 2], ![128, 44, 50]]]
  hmulB := by decide  
  f := ![![![2755, 54, 0], ![-6102, 0, 0]], ![![1173, 23, 0], ![-2598, 0, 0]], ![![726, -12, -1], ![-1608, 57, 0]]]
  g := ![![![1, 0, 0], ![-51, 113, 0], ![-30, 0, 113]], ![![0, 1, 0], ![-24, 52, 2], ![-32, 44, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![19, 1, 0]] ![![-3033, -524, 168]]
  ![![113, 0, 0], ![13, -25, 1]] where
 M := ![![![-342729, -59212, 18984]], ![![-36123, -6121, 1976]]]
 hmul := by decide  
 g := ![![![![-3020, -549, 169], ![-113, 0, 0]]], ![![![-326, -42, 17], ![55, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![13, -25, 1]] ![![113, 0, 0], ![51, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![5763, 113, 0]], ![![1469, -2825, 113], ![791, -1243, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![51, 1, 0]]], ![![![13, -25, 1]], ![![7, -11, 0]]]]
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


lemma PB114I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 113 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 113 (by omega)

def PB114I2 : PrimesBelowBoundCertificateInterval O 79 113 114 where
  m := 8
  g := ![2, 2, 1, 3, 2, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB114I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![113, 113, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  β := ![I83N1, I89N1, I101N0, I101N1, I101N2, I103N1, I113N0, I113N1, I113N2]
  Il := ![[I83N1], [I89N1], [], [I101N0, I101N1, I101N2], [I103N1], [], [], [I113N0, I113N1, I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
