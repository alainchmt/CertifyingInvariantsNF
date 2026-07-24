
import IdealArithmetic.Examples.NF3_3_783380_1.RI3_3_783380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42173, 73, -1241]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![42173, 73, -1241]] 
 ![![83, 0, 0], ![18, 1, 0], ![68, 0, 1]] where
  M :=![![![42173, 73, -1241], ![-12410, -21, 365], ![730, 0, -21]]]
  hmulB := by decide  
  f := ![![![441, 1533, 584]], ![![166, 577, 219]], ![![546, 1898, 723]]]
  g := ![![![1509, 73, -1241], ![-444, -21, 365], ![26, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8897, -8, 259]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-8897, -8, 259]] 
 ![![83, 0, 0], ![24, 1, 0], ![1, 0, 1]] where
  M :=![![![-8897, -8, 259], ![2590, -91, -40], ![-80, 246, -91]]]
  hmulB := by decide  
  f := ![![![18121, 62986, 23889]], ![![8118, 28217, 10702]], ![![7807, 27136, 10292]]]
  g := ![![![-108, -8, 259], ![58, -91, -40], ![-71, 246, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 0, 4]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-133, 0, 4]] 
 ![![83, 0, 0], ![41, 1, 0], ![29, 0, 1]] where
  M :=![![![-133, 0, 4], ![40, 3, 0], ![0, 8, 3]]]
  hmulB := by decide  
  f := ![![![9, 32, -12]], ![![3, 11, -4]], ![![7, 24, -9]]]
  g := ![![![-3, 0, 4], ![-1, 3, 0], ![-5, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![42173, 73, -1241]] ![![-8897, -8, 259]]
  ![![-374924831, -649313, 11032818]] where
 M := ![![![-374924831, -649313, 11032818]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-374924831, -649313, 11032818]] ![![-133, 0, 4]]
  ![![83, 0, 0]] where
 M := ![![![49839030003, 86314605, -1466600870]]]
 hmul := by decide  
 g := ![![![![600470241, 1039935, -17669890]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [86, 66, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 57, 47], [3, 31, 42], [0, 1]]
 g := ![![[6, 27, 17], [59, 16], [63, 81], [13, 64, 25], [19, 21, 1], []], ![[14, 41, 54, 40], [79, 69], [9, 49], [27, 57, 20, 87], [37, 16, 9, 44], [38, 73]], ![[68, 18, 16, 57], [35, 73], [69, 78], [51, 47, 69, 36], [24, 13, 62, 21], [43, 73]]]
 h' := ![![[18, 57, 47], [4, 73, 27], [19, 68, 85], [39, 2, 80], [57, 55, 84], [0, 0, 1], [0, 1]], ![[3, 31, 42], [61, 76, 85], [25, 18, 46], [49, 22, 82], [14, 48, 27], [82, 30, 31], [18, 57, 47]], ![[0, 1], [33, 29, 66], [27, 3, 47], [49, 65, 16], [66, 75, 67], [49, 59, 57], [3, 31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 6], []]
 b := ![[], [48, 33, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [86, 66, 68, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![356, 890, 890]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 10, 10]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [46, 90, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 22, 28], [62, 74, 69], [0, 1]]
 g := ![![[75, 13, 73], [92, 16], [65, 43], [64, 96], [53, 49], [1]], ![[29, 82, 88, 10], [38, 54], [45, 1], [12, 22], [55, 61], [75, 92, 59, 30]], ![[82, 88, 42, 21], [22, 35], [30, 91], [83, 18], [93, 18], [15, 8, 14, 67]]]
 h' := ![![[42, 22, 28], [80, 84, 49], [23, 46, 4], [54, 28, 72], [66, 92, 22], [51, 7, 7], [0, 1]], ![[62, 74, 69], [86, 15, 61], [66, 25, 32], [14, 19, 1], [88, 39, 33], [22, 3, 35], [42, 22, 28]], ![[0, 1], [63, 95, 84], [69, 26, 61], [73, 50, 24], [37, 63, 42], [85, 87, 55], [62, 74, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 8], []]
 b := ![[], [86, 31, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [46, 90, 90, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28615, -93508, 64893]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-295, -964, 669]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [6, 91, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 4, 31], [7, 96, 70], [0, 1]]
 g := ![![[95, 19, 20], [27, 88], [89, 95, 17], [27, 85], [72, 31], [1]], ![[66, 83, 19, 33], [53, 52], [6, 77, 40, 21], [42, 25], [85, 36], [100, 38, 48, 97]], ![[89, 48, 84, 92], [7, 54], [72, 6, 35, 20], [20, 13], [33, 56], [26, 34, 99, 4]]]
 h' := ![![[36, 4, 31], [73, 52, 90], [72, 26, 54], [3, 21, 57], [8, 10, 61], [95, 10, 43], [0, 1]], ![[7, 96, 70], [32, 33, 51], [42, 100, 31], [76, 91, 63], [96, 28, 5], [0, 63, 95], [36, 4, 31]], ![[0, 1], [72, 16, 61], [35, 76, 16], [3, 90, 82], [27, 63, 35], [86, 28, 64], [7, 96, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 94], []]
 b := ![[], [36, 100, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [6, 91, 58, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26664, 17271, -11817]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-264, 171, -117]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-839, -2916, -1102]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-839, -2916, -1102]] 
 ![![103, 0, 0], ![0, 103, 0], ![56, 92, 1]] where
  M :=![![![-839, -2916, -1102], ![-11020, -38307, -14580], ![-29160, -101348, -38307]]]
  hmulB := by decide  
  f := ![![![-99297, -172, 2922]], ![![29220, 51, -860]], ![![-27904, -48, 821]]]
  g := ![![![591, 956, -1102], ![7820, 12651, -14580], ![20544, 33232, -38307]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [22, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 102], [0, 1]]
 g := ![![[74, 56], [92, 58], [34, 93], [25], [23], [20, 1]], ![[61, 47], [16, 45], [40, 10], [25], [23], [40, 102]]]
 h' := ![![[20, 102], [36, 57], [76, 77], [102, 89], [72, 98], [75, 69], [0, 1]], ![[0, 1], [43, 46], [71, 26], [28, 14], [75, 5], [13, 34], [20, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [41, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [22, 83, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46, -101, 56]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -51, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99297, -172, 2922]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-99297, -172, 2922]] 
 ![![103, 0, 0], ![55, 1, 0], ![13, 0, 1]] where
  M :=![![![-99297, -172, 2922], ![29220, 51, -860], ![-1720, -4, 51]]]
  hmulB := by decide  
  f := ![![![-839, -2916, -1102]], ![![-555, -1929, -730]], ![![-389, -1352, -511]]]
  g := ![![![-1241, -172, 2922], ![365, 51, -860], ![-21, -4, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-839, -2916, -1102]] ![![-99297, -172, 2922]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [51, 100, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 79, 91], [71, 27, 16], [0, 1]]
 g := ![![[30, 102, 64], [92, 39, 44], [105, 47], [67, 90, 35], [52, 23], [1]], ![[45, 52, 69, 24], [91, 73, 13, 77], [2, 85], [99, 88, 8, 88], [106, 56], [61, 32, 10, 77]], ![[33, 80, 47, 89], [72, 82, 71, 44], [23, 37], [104, 0, 92, 53], [51, 75], [83, 3, 78, 30]]]
 h' := ![![[75, 79, 91], [16, 56, 99], [44, 63, 30], [7, 85, 49], [56, 82, 79], [56, 7, 39], [0, 1]], ![[71, 27, 16], [21, 33, 65], [90, 70, 16], [70, 52, 70], [30, 44, 72], [73, 91, 85], [75, 79, 91]], ![[0, 1], [80, 18, 50], [34, 81, 61], [43, 77, 95], [104, 88, 63], [43, 9, 90], [71, 27, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 32], []]
 b := ![[], [54, 41, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [51, 100, 68, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![321, 856, 856]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 8, 8]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [84, 68, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 75, 12], [42, 33, 97], [0, 1]]
 g := ![![[84, 64, 7], [66, 108], [75, 30, 22], [21, 82, 38], [0, 27], [1]], ![[90, 48, 53, 28], [48, 87], [98, 95, 54, 43], [60, 77, 57, 89], [108, 1], [43, 37, 90, 93]], ![[72, 39, 99, 16], [6, 29], [92, 95, 20, 28], [21, 78, 87, 97], [37, 61], [56, 86, 23, 16]]]
 h' := ![![[29, 75, 12], [63, 11, 15], [22, 83, 33], [89, 46, 26], [80, 0, 16], [25, 41, 71], [0, 1]], ![[42, 33, 97], [23, 48, 82], [26, 3, 14], [45, 54, 102], [104, 65, 92], [67, 73, 1], [29, 75, 12]], ![[0, 1], [12, 50, 12], [25, 23, 62], [20, 9, 90], [56, 44, 1], [60, 104, 37], [42, 33, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 25], []]
 b := ![[], [84, 93, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [84, 68, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![378121, 1298735, 261382]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3469, 11915, 2398]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [40, 81, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 93, 66], [75, 19, 47], [0, 1]]
 g := ![![[111, 2, 16], [79, 26], [21, 15], [86, 30], [9, 49, 69], [1]], ![[12, 40, 107, 23], [105, 104], [79, 31], [67, 99], [82, 28, 92, 103], [98, 41, 0, 24]], ![[106, 10, 48, 107], [30, 26], [29, 85], [15, 60], [47, 12, 23, 59], [68, 110, 40, 89]]]
 h' := ![![[80, 93, 66], [89, 112, 109], [56, 20, 34], [52, 56, 44], [92, 41, 16], [73, 32, 42], [0, 1]], ![[75, 19, 47], [63, 2, 84], [67, 92, 45], [96, 95, 12], [105, 43, 72], [32, 1, 85], [80, 93, 66]], ![[0, 1], [106, 112, 33], [96, 1, 34], [76, 75, 57], [87, 29, 25], [38, 80, 99], [75, 19, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 2], []]
 b := ![[], [97, 11, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [40, 81, 71, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![339, 678, -226]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 6, -2]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2793, -9708, -3682]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-2793, -9708, -3682]] 
 ![![127, 0, 0], ![62, 1, 0], ![44, 0, 1]] where
  M :=![![![-2793, -9708, -3682], ![-36820, -127981, -48540], ![-97080, -337436, -127981]]]
  hmulB := by decide  
  f := ![![![-7079, -196, 278]], ![![-3434, -77, 128]], ![![-2468, -116, 115]]]
  g := ![![![5993, -9708, -3682], ![79006, -127981, -48540], ![208308, -337436, -127981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3377, -1484, 660]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-3377, -1484, 660]] 
 ![![127, 0, 0], ![87, 1, 0], ![61, 0, 1]] where
  M :=![![![-3377, -1484, 660], ![6600, 19063, -7420], ![-14840, -49136, 19063]]]
  hmulB := by decide  
  f := ![![![-1191151, -4140268, -1570300]], ![![-939631, -3266021, -1238720]], ![![-898133, -3121780, -1184013]]]
  g := ![![![673, -1484, 660], ![-9443, 19063, -7420], ![24387, -49136, 19063]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 16, 6]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![7, 16, 6]] 
 ![![127, 0, 0], ![105, 1, 0], ![81, 0, 1]] where
  M :=![![![7, 16, 6], ![60, 211, 80], ![160, 556, 211]]]
  hmulB := by decide  
  f := ![![![41, -40, 14]], ![![35, -29, 10]], ![![23, -36, 13]]]
  g := ![![![-17, 16, 6], ![-225, 211, 80], ![-593, 556, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-2793, -9708, -3682]] ![![-3377, -1484, 660]]
  ![![41, -40, 14]] where
 M := ![![![41, -40, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![41, -40, 14]] ![![7, 16, 6]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -8, 3]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![1, -8, 3]] 
 ![![131, 0, 0], ![12, 1, 0], ![76, 0, 1]] where
  M :=![![![1, -8, 3], ![30, 103, -40], ![-80, -266, 103]]]
  hmulB := by decide  
  f := ![![![31, -26, -11]], ![![2, -5, -2]], ![![16, -22, -9]]]
  g := ![![![-1, -8, 3], ![14, 103, -40], ![-36, -266, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -138, -52]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-51, -138, -52]] 
 ![![131, 0, 0], ![107, 1, 0], ![42, 0, 1]] where
  M :=![![![-51, -138, -52], ![-520, -1819, -690], ![-1380, -4796, -1819]]]
  hmulB := by decide  
  f := ![![![479, 1630, -632]], ![![343, 1171, -454]], ![![278, 936, -363]]]
  g := ![![![129, -138, -52], ![1703, -1819, -690], ![4490, -4796, -1819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![1, -8, 3]] ![![1, -8, 3]]
  ![![-479, -1630, 632]] where
 M := ![![![-479, -1630, 632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-479, -1630, 632]] ![![-51, -138, -52]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 45, 17]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![13, 45, 17]] 
 ![![137, 0, 0], ![83, 1, 0], ![47, 0, 1]] where
  M :=![![![13, 45, 17], ![170, 591, 225], ![450, 1564, 591]]]
  hmulB := by decide  
  f := ![![![2619, 7, -78]], ![![1581, 4, -47]], ![![899, 3, -27]]]
  g := ![![![-33, 45, 17], ![-434, 591, 225], ![-1147, 1564, 591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35887, 124738, 47310]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![35887, 124738, 47310]] 
 ![![137, 0, 0], ![87, 1, 0], ![48, 0, 1]] where
  M :=![![![35887, 124738, 47310], ![473100, 1644427, 623690], ![1247380, 4335712, 1644427]]]
  hmulB := by decide  
  f := ![![![58951, 406, -1850]], ![![37301, 229, -1160]], ![![20684, 216, -677]]]
  g := ![![![-95527, 124738, 47310], ![-1259337, 1644427, 623690], ![-3320380, 4335712, 1644427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60577, 210557, 79859]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![60577, 210557, 79859]] 
 ![![137, 0, 0], ![104, 1, 0], ![111, 0, 1]] where
  M :=![![![60577, 210557, 79859], ![798590, 2775783, 1052785], ![2105570, 7318656, 2775783]]]
  hmulB := by decide  
  f := ![![![-6129, -8373, 3352]], ![![-4408, -5569, 2239]], ![![-5577, -8813, 3503]]]
  g := ![![![-224100, 210557, 79859], ![-2954321, 2775783, 1052785], ![-7789391, 7318656, 2775783]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![13, 45, 17]] ![![35887, 124738, 47310]]
  ![![42961491, 149327913, 56636339]] where
 M := ![![![42961491, 149327913, 56636339]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![42961491, 149327913, 56636339]] ![![60577, 210557, 79859]]
  ![![137, 0, 0]] where
 M := ![![![241106032591207, 838049607231750, 317851235575911]]]
 hmul := by decide  
 g := ![![![![1759898048111, 6117150417750, 2320082011503]]]]
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


lemma PB197I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB197I2 : PrimesBelowBoundCertificateInterval O 79 137 197 where
  m := 11
  g := ![3, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB197I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N0, I131N1]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![131, 131, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N0, I83N1, I83N2, I103N1, I127N0, I127N1, I127N2, I131N0, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N2], [], [], [], [I103N1], [], [], [], [I127N0, I127N1, I127N2], [I131N0, I131N0, I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
