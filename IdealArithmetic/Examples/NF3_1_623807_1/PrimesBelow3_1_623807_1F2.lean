
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [18, 65, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10, 6], [78, 72, 77], [0, 1]]
 g := ![![[46, 51, 3], [19, 39, 65], [21, 23], [4, 3], [27, 80, 1], []], ![[62, 68, 71, 58], [35, 22, 24, 82], [31, 27], [2, 12], [14, 43, 63, 62], [12, 36]], ![[60, 31, 16, 69], [59, 22, 61, 16], [15, 1], [15, 27], [52, 79, 57, 64], [24, 36]]]
 h' := ![![[2, 10, 6], [73, 36, 70], [75, 51, 56], [72, 30, 43], [12, 42, 13], [0, 0, 1], [0, 1]], ![[78, 72, 77], [79, 61, 27], [8, 55, 22], [63, 44, 39], [79, 55, 26], [37, 23, 72], [2, 10, 6]], ![[0, 1], [38, 69, 69], [19, 60, 5], [17, 9, 1], [72, 69, 44], [8, 60, 10], [78, 72, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 44], []]
 b := ![[], [26, 1, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [18, 65, 3, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311582, -1494, -2241]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3754, -18, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23571201, 817476, -1488650]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![23571201, 817476, -1488650]] 
 ![![89, 0, 0], ![0, 89, 0], ![10, 17, 1]] where
  M :=![![![23571201, 817476, -1488650], ![-226274800, 24388677, 3123602], ![350531152, -113137400, 21265075]]]
  hmulB := by decide  
  f := ![![![-9798014095175, -1697059573700, -436625547018]], ![![-66367083146736, -11495073668875, -2957493600382]], ![![-15930410410134, -2759217861587, -709901424103]]]
  g := ![![![432109, 293534, -1488650], ![-2893380, -322613, 3123602], ![1549218, -5333075, 21265075]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 88], [0, 1]]
 g := ![![[70, 10], [73], [71], [41, 4], [50, 49], [1]], ![[0, 79], [73], [71], [13, 85], [63, 40], [1]]]
 h' := ![![[82, 88], [57, 59], [64, 42], [76, 58], [84, 2], [80, 82], [0, 1]], ![[0, 1], [0, 30], [37, 47], [26, 31], [70, 87], [40, 7], [82, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [20, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1213, 1222, 30]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, 8, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9798014095175, 1697059573700, 436625547018]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![9798014095175, 1697059573700, 436625547018]] 
 ![![89, 0, 0], ![56, 1, 0], ![6, 0, 1]] where
  M :=![![![9798014095175, 1697059573700, 436625547018], ![66367083146736, 11495073668875, 2957493600382], ![191585972055664, 33183541573368, 8537580068493]]]
  hmulB := by decide  
  f := ![![![-23571201, -817476, 1488650]], ![![-12288904, -788397, 901582]], ![![-5527622, 1216096, -138575]]]
  g := ![![![-987158149597, 1697059573700, 436625547018], ![-6686539369804, 11495073668875, 2957493600382], ![-19302447600718, 33183541573368, 8537580068493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![23571201, 817476, -1488650]] ![![9798014095175, 1697059573700, 436625547018]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-39, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-39, 1, 0]] 
 ![![97, 0, 0], ![58, 1, 0], ![35, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-39, 1, 0], ![0, -38, 2], ![152, 0, -40]]]
  hmulB := by decide  
  f := ![![![820, -21, 0], ![2037, 0, 0]], ![![508, -13, 0], ![1262, 0, 0]], ![![320, 11, -1], ![795, 49, 0]]]
  g := ![![![1, 0, 0], ![-58, 97, 0], ![-35, 0, 97]], ![![-1, 1, 0], ![22, -38, 2], ![16, 0, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-29, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-29, 1, 0]] 
 ![![97, 0, 0], ![68, 1, 0], ![79, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-29, 1, 0], ![0, -28, 2], ![152, 0, -30]]]
  hmulB := by decide  
  f := ![![![2640, -91, 0], ![8827, 0, 0]], ![![1828, -63, 0], ![6112, 0, 0]], ![![2180, -61, -1], ![7289, 49, 0]]]
  g := ![![![1, 0, 0], ![-68, 97, 0], ![-79, 0, 97]], ![![-1, 1, 0], ![18, -28, 2], ![26, 0, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-39, 1, 0]] ![![97, 0, 0], ![-29, 1, 0]]
  ![![97, 0, 0], ![32, 15, 1]] where
 M := ![![![9409, 0, 0], ![-2813, 97, 0]], ![![-3783, 97, 0], ![1131, -67, 2]]]
 hmul := by decide  
 g := ![![![![65, -15, -1], ![97, 0, 0]], ![![-29, 1, 0], ![0, 0, 0]]], ![![![-39, 1, 0], ![0, 0, 0]], ![![-21, -16, -1], ![99, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![32, 15, 1]] ![![97, 0, 0], ![-29, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2813, 97, 0]], ![![3104, 1455, 97], ![-776, -388, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-29, 1, 0]]], ![![![32, 15, 1]], ![![-8, -4, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![8, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![8, 1, 0]] 
 ![![101, 0, 0], ![8, 1, 0], ![65, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![8, 1, 0], ![0, 9, 2], ![152, 0, 7]]]
  hmulB := by decide  
  f := ![![![273, 34, 0], ![-3434, 0, 0]], ![![8, 1, 0], ![-100, 0, 0]], ![![173, 17, -1], ![-2176, 51, 0]]]
  g := ![![![1, 0, 0], ![-8, 101, 0], ![-65, 0, 101]], ![![0, 1, 0], ![-2, 9, 2], ![-3, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![12, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![12, 1, 0]] 
 ![![101, 0, 0], ![12, 1, 0], ![23, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![12, 1, 0], ![0, 13, 2], ![152, 0, 11]]]
  hmulB := by decide  
  f := ![![![565, 47, 0], ![-4747, 0, 0]], ![![60, 5, 0], ![-504, 0, 0]], ![![127, 4, -1], ![-1067, 51, 0]]]
  g := ![![![1, 0, 0], ![-12, 101, 0], ![-23, 0, 101]], ![![0, 1, 0], ![-2, 13, 2], ![-1, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-20, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-20, 1, 0]] 
 ![![101, 0, 0], ![81, 1, 0], ![12, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-20, 1, 0], ![0, -19, 2], ![152, 0, -21]]]
  hmulB := by decide  
  f := ![![![21, 1519, -160], ![101, 8080, 0]], ![![21, 1215, -128], ![102, 6464, 0]], ![![12, 180, -19], ![60, 960, 0]]]
  g := ![![![1, 0, 0], ![-81, 101, 0], ![-12, 0, 101]], ![![-1, 1, 0], ![15, -19, 2], ![4, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![8, 1, 0]] ![![101, 0, 0], ![12, 1, 0]]
  ![![101, 0, 0], ![48, -40, 1]] where
 M := ![![![10201, 0, 0], ![1212, 101, 0]], ![![808, 101, 0], ![96, 21, 2]]]
 hmul := by decide  
 g := ![![![![53, 40, -1], ![101, 0, 0]], ![![-36, 41, -1], ![101, 0, 0]]], ![![![-40, 41, -1], ![101, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![48, -40, 1]] ![![101, 0, 0], ![-20, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2020, 101, 0]], ![![4848, -4040, 101], ![-808, 808, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-20, 1, 0]]], ![![![48, -40, 1]], ![![-8, 8, -1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [70, 78, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 80, 58], [23, 22, 45], [0, 1]]
 g := ![![[59, 96, 93], [35, 63, 26], [37, 67, 97], [75, 58], [66, 66], [1]], ![[72, 57, 74, 14], [43, 63, 49, 68], [18, 64, 61, 36], [82, 19], [22, 19], [43, 16, 24, 30]], ![[10, 25, 4, 6], [55, 1, 0, 6], [53, 64, 49, 99], [40, 18], [25, 4], [7, 89, 81, 73]]]
 h' := ![![[93, 80, 58], [22, 89, 14], [88, 34, 52], [20, 9, 71], [74, 19, 77], [33, 25, 13], [0, 1]], ![[23, 22, 45], [15, 54, 11], [26, 3, 26], [60, 23, 24], [54, 46, 15], [7, 59, 88], [93, 80, 58]], ![[0, 1], [29, 63, 78], [32, 66, 25], [93, 71, 8], [3, 38, 11], [38, 19, 2], [23, 22, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 38], []]
 b := ![[], [22, 28, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [70, 78, 90, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105678, -7828, -721]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1026, -76, -7]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [19, 69, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 13, 65], [47, 93, 42], [0, 1]]
 g := ![![[42, 64, 49], [49, 1, 101], [61, 105], [101, 94, 76], [54, 4], [1]], ![[55, 4, 47, 59], [9, 89, 23, 38], [74, 75], [64, 74, 51, 59], [49, 85], [32, 40, 83, 63]], ![[29, 94, 29, 44], [50, 45, 4, 62], [33, 89], [49, 79, 70, 47], [47, 48], [15, 45, 82, 44]]]
 h' := ![![[58, 13, 65], [32, 19, 100], [67, 77, 84], [7, 13, 31], [84, 104, 66], [88, 38, 105], [0, 1]], ![[47, 93, 42], [97, 56, 49], [71, 83, 84], [34, 6, 90], [88, 4, 58], [85, 42, 37], [58, 13, 65]], ![[0, 1], [11, 32, 65], [102, 54, 46], [80, 88, 93], [16, 106, 90], [69, 27, 72], [47, 93, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 35], []]
 b := ![[], [84, 67, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [19, 69, 2, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1444821, 2140, 5350]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13503, 20, 50]
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


def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![20, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![20, 1, 0]] 
 ![![109, 0, 0], ![20, 1, 0], ![8, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![20, 1, 0], ![0, 21, 2], ![152, 0, 19]]]
  hmulB := by decide  
  f := ![![![1081, 54, 0], ![-5886, 0, 0]], ![![180, 9, 0], ![-980, 0, 0]], ![![72, -7, -1], ![-392, 55, 0]]]
  g := ![![![1, 0, 0], ![-20, 109, 0], ![-8, 0, 109]], ![![0, 1, 0], ![-4, 21, 2], ![0, 0, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-40, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-40, 1, 0]] 
 ![![109, 0, 0], ![69, 1, 0], ![92, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-40, 1, 0], ![0, -39, 2], ![152, 0, -41]]]
  hmulB := by decide  
  f := ![![![1521, -38, 0], ![4142, 0, 0]], ![![1001, -25, 0], ![2726, 0, 0]], ![![1308, -13, -1], ![3562, 55, 0]]]
  g := ![![![1, 0, 0], ![-69, 109, 0], ![-92, 0, 109]], ![![-1, 1, 0], ![23, -39, 2], ![36, 0, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![20, 1, 0]] ![![109, 0, 0], ![20, 1, 0]]
  ![![109, 0, 0], ![-18, -34, 1]] where
 M := ![![![11881, 0, 0], ![2180, 109, 0]], ![![2180, 109, 0], ![400, 41, 2]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-18, -34, 1]] ![![109, 0, 0], ![-40, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4360, 109, 0]], ![![-1962, -3706, 109], ![872, 1308, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-40, 1, 0]]], ![![![-18, -34, 1]], ![![8, 12, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![763, -384, 94]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![763, -384, 94]] 
 ![![113, 0, 0], ![0, 113, 0], ![55, 44, 1]] where
  M :=![![![763, -384, 94], ![14288, 379, -862], ![-72656, 7144, 1241]]]
  hmulB := by decide  
  f := ![![![58659, 10160, 2614]], ![![397328, 68819, 17706]], ![![193413, 33500, 8619]]]
  g := ![![![-39, -40, 94], ![546, 339, -862], ![-1247, -420, 1241]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [74, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 112], [0, 1]]
 g := ![![[14, 18], [57], [82], [30], [37, 105], [94, 1]], ![[11, 95], [57], [82], [30], [76, 8], [75, 112]]]
 h' := ![![[94, 112], [44, 40], [9, 31], [38, 67], [87, 16], [50, 61], [0, 1]], ![[0, 1], [75, 73], [98, 82], [8, 46], [9, 97], [21, 52], [94, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [31, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [74, 19, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![530, 650, -52]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 26, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58659, 10160, 2614]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![58659, 10160, 2614]] 
 ![![113, 0, 0], ![26, 1, 0], ![101, 0, 1]] where
  M :=![![![58659, 10160, 2614], ![397328, 68819, 17706], ![1146992, 198664, 51113]]]
  hmulB := by decide  
  f := ![![![763, -384, 94]], ![![302, -85, 14]], ![![39, -280, 95]]]
  g := ![![![-4155, 10160, 2614], ![-28144, 68819, 17706], ![-81245, 198664, 51113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![763, -384, 94]] ![![58659, 10160, 2614]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![55, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![55, 1, 0]] 
 ![![127, 0, 0], ![55, 1, 0], ![111, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![55, 1, 0], ![0, 56, 2], ![152, 0, 54]]]
  hmulB := by decide  
  f := ![![![2366, 43, 0], ![-5461, 0, 0]], ![![990, 18, 0], ![-2285, 0, 0]], ![![2048, 9, -1], ![-4727, 64, 0]]]
  g := ![![![1, 0, 0], ![-55, 127, 0], ![-111, 0, 127]], ![![0, 1, 0], ![-26, 56, 2], ![-46, 0, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-44, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-44, 1, 0]] 
 ![![127, 0, 0], ![83, 1, 0], ![70, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-44, 1, 0], ![0, -43, 2], ![152, 0, -45]]]
  hmulB := by decide  
  f := ![![![2553, -58, 0], ![7366, 0, 0]], ![![1717, -39, 0], ![4954, 0, 0]], ![![1394, -10, -1], ![4022, 64, 0]]]
  g := ![![![1, 0, 0], ![-83, 127, 0], ![-70, 0, 127]], ![![-1, 1, 0], ![27, -43, 2], ![26, 0, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-11, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-11, 1, 0]] 
 ![![127, 0, 0], ![116, 1, 0], ![72, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-11, 1, 0], ![0, -10, 2], ![152, 0, -12]]]
  hmulB := by decide  
  f := ![![![1189, -108, 0], ![13716, 0, 0]], ![![1090, -99, 0], ![12574, 0, 0]], ![![672, -56, -1], ![7752, 64, 0]]]
  g := ![![![1, 0, 0], ![-116, 127, 0], ![-72, 0, 127]], ![![-1, 1, 0], ![8, -10, 2], ![8, 0, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![55, 1, 0]] ![![127, 0, 0], ![-44, 1, 0]]
  ![![127, 0, 0], ![60, 6, 1]] where
 M := ![![![16129, 0, 0], ![-5588, 127, 0]], ![![6985, 127, 0], ![-2420, 12, 2]]]
 hmul := by decide  
 g := ![![![![67, -6, -1], ![127, 0, 0]], ![![-44, 1, 0], ![0, 0, 0]]], ![![![-5, -5, -1], ![127, 0, 0]], ![![-20, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![60, 6, 1]] ![![127, 0, 0], ![-11, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1397, 127, 0]], ![![7620, 762, 127], ![-508, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-11, 1, 0]]], ![![![60, 6, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [48, 7, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 62, 102], [101, 68, 29], [0, 1]]
 g := ![![[48, 80, 7], [2, 60, 35], [98, 123], [42, 129], [78, 60], [24, 1], []], ![[86, 59, 119, 9], [17, 27, 117, 55], [57, 44], [], [39, 5], [6, 39], [82, 55]], ![[81, 78, 94, 23], [52, 12, 83, 72], [58, 101], [78, 129], [38, 39], [40, 45], [24, 55]]]
 h' := ![![[54, 62, 102], [35, 24, 20], [125, 2, 67], [84, 33, 56], [129, 106, 103], [27, 46, 45], [0, 0, 1], [0, 1]], ![[101, 68, 29], [57, 126, 9], [13, 107, 44], [28, 14, 100], [91, 121], [103, 115, 23], [28, 76, 68], [54, 62, 102]], ![[0, 1], [39, 112, 102], [80, 22, 20], [47, 84, 106], [75, 35, 28], [14, 101, 63], [10, 55, 62], [101, 68, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 100], []]
 b := ![[], [21, 59, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [48, 7, 107, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114870363, 6266516, 1967227]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![876873, 47836, 15017]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35852821735, -6209868018, -1597697018]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-35852821735, -6209868018, -1597697018]] 
 ![![137, 0, 0], ![0, 137, 0], ![59, 61, 1]] where
  M :=![![![-35852821735, -6209868018, -1597697018], ![-242849946736, -42062689753, -10822039018], ![-701049992000, -121424973368, -31240650735]]]
  hmulB := by decide  
  f := ![![![-215663, 12238, 6790]], ![![1032080, -203425, 17686]], ![![372707, -81539, 9185]]]
  g := ![![![426359871, 666055840, -1597697018], ![2887958798, 4511545185, -10822039018], ![8336849645, 13023757091, -31240650735]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [129, 105, 1] where
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
 g := ![![[4, 17], [17], [118], [114, 109], [121], [65], [1]], ![[0, 120], [17], [118], [40, 28], [121], [65], [1]]]
 h' := ![![[32, 136], [3, 47], [2, 47], [90, 114], [72, 66], [36, 126], [8, 32], [0, 1]], ![[0, 1], [0, 90], [136, 90], [39, 23], [129, 71], [95, 11], [73, 105], [32, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [54, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [129, 105, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![481, 286, 108]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -46, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-215663, 12238, 6790]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-215663, 12238, 6790]] 
 ![![137, 0, 0], ![16, 1, 0], ![1, 0, 1]] where
  M :=![![![-215663, 12238, 6790], ![1032080, -203425, 17686], ![828096, 516040, -221111]]]
  hmulB := by decide  
  f := ![![![-35852821735, -6209868018, -1597697018]], ![![-5959818208, -1032266993, -265585338]], ![![-5378852655, -931641178, -239695969]]]
  g := ![![![-3053, 12238, 6790], ![31162, -203425, 17686], ![-52609, 516040, -221111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-35852821735, -6209868018, -1597697018]] ![![-215663, 12238, 6790]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB224I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB224I2 : PrimesBelowBoundCertificateInterval O 79 137 224 where
  m := 11
  g := ![1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB224I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N0, I97N1, I101N0, I101N1, I101N2, I109N0, I109N1, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N1], [I101N0, I101N1, I101N2], [], [], [I109N0, I109N0, I109N1], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
