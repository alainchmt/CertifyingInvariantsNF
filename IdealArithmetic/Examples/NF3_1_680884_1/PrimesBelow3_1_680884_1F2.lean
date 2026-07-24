
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![32, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![32, 1, 0]] 
 ![![83, 0, 0], ![32, 1, 0], ![28, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![32, 1, 0], ![1, 32, 2], ![355, 73, 33]]]
  hmulB := by decide  
  f := ![![![328, 14556, 910], ![332, -37765, 0]], ![![111, 5598, 350], ![167, -14525, 0]], ![![96, 4910, 307], ![150, -12740, 0]]]
  g := ![![![1, 0, 0], ![-32, 83, 0], ![-28, 0, 83]], ![![0, 1, 0], ![-13, 32, 2], ![-35, 73, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-27, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-27, 1, 0]] 
 ![![83, 0, 0], ![56, 1, 0], ![51, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-27, 1, 0], ![1, -27, 2], ![355, 73, -26]]]
  hmulB := by decide  
  f := ![![![-1760, 59195, -4386], ![1328, 182019, 0]], ![![-1181, 39922, -2958], ![914, 122757, 0]], ![![-1086, 36373, -2695], ![802, 111843, 0]]]
  g := ![![![1, 0, 0], ![-56, 83, 0], ![-51, 0, 83]], ![![-1, 1, 0], ![17, -27, 2], ![-29, 73, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 27, 4]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![100, 27, 4]] 
 ![![83, 0, 0], ![77, 1, 0], ![24, 0, 1]] where
  M :=![![![100, 27, 4], ![1447, 392, 58], ![10441, 2827, 419]]]
  hmulB := by decide  
  f := ![![![282, -5, -2]], ![![253, -3, -2]], ![![55, -11, 1]]]
  g := ![![![-25, 27, 4], ![-363, 392, 58], ![-2618, 2827, 419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![32, 1, 0]] ![![83, 0, 0], ![-27, 1, 0]]
  ![![282, -5, -2]] where
 M := ![![![6889, 0, 0], ![-2241, 83, 0]], ![![2656, 83, 0], ![-863, 5, 2]]]
 hmul := by decide  
 g := ![![![![8300, 2241, 332]], ![![-1253, -337, -50]]], ![![![4647, 1256, 186]], ![![-701, -189, -28]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![282, -5, -2]] ![![100, 27, 4]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [88, 59, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 88, 9], [53, 0, 80], [0, 1]]
 g := ![![[7, 58, 73], [24, 78], [40, 42], [57, 87, 20], [70, 60, 1], []], ![[67, 1, 8, 9], [50, 5], [57, 44], [66, 58, 20, 2], [63, 10], [36, 81]], ![[67, 66, 83, 2], [76, 9], [19, 16], [54, 87, 45, 81], [44, 70, 85, 80], [54, 81]]]
 h' := ![![[7, 88, 9], [40, 79, 47], [85, 12, 73], [57, 22, 65], [70, 24, 38], [0, 0, 1], [0, 1]], ![[53, 0, 80], [49, 74, 88], [55, 59, 19], [40, 40, 20], [86, 41, 38], [85, 79], [7, 88, 9]], ![[0, 1], [37, 25, 43], [36, 18, 86], [62, 27, 4], [43, 24, 13], [15, 10, 88], [53, 0, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 46], []]
 b := ![[], [73, 39, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [88, 59, 29, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-990303, -289339, -45212]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11127, -3251, -508]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-79, -7, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-79, -7, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![18, 90, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-79, -7, 1], ![348, -6, -13], ![-2271, -297, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -90, 97]], ![![-1, -1, 1], ![6, 12, -13], ![-21, 9, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [62, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 96], [0, 1]]
 g := ![![[83, 36], [86], [2], [36], [11], [92, 1]], ![[0, 61], [86], [2], [36], [11], [87, 96]]]
 h' := ![![[92, 96], [30, 6], [67, 38], [26, 83], [67, 91], [19, 60], [0, 1]], ![[0, 1], [0, 91], [71, 59], [96, 14], [0, 6], [10, 37], [92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [47, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [62, 5, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1670, 3872, 1858]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-362, -1684, 1858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![13, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![13, 1, 0]] 
 ![![97, 0, 0], ![13, 1, 0], ![13, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![13, 1, 0], ![1, 13, 2], ![355, 73, 14]]]
  hmulB := by decide  
  f := ![![![-721, -9554, -1470], ![-97, 71295, 0]], ![![-98, -1274, -196], ![1, 9506, 0]], ![![-104, -1281, -197], ![42, 9555, 0]]]
  g := ![![![1, 0, 0], ![-13, 97, 0], ![-13, 0, 97]], ![![0, 1, 0], ![-2, 13, 2], ![-8, 73, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-79, -7, 1]] ![![97, 0, 0], ![13, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1261, 97, 0]], ![![-7663, -679, 97], ![-679, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![13, 1, 0]]], ![![![-79, -7, 1]], ![![-7, -1, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [39, 100, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 62, 66], [68, 38, 35], [0, 1]]
 g := ![![[0, 8, 65], [36, 79], [95, 44, 92], [66, 56], [54, 79], [1]], ![[63, 24, 56, 3], [79, 47], [13, 53, 22, 86], [53, 49], [67, 71], [20, 33, 61, 50]], ![[53, 31, 63, 26], [34, 81], [25, 26, 86, 57], [35, 92], [16, 81], [70, 63, 1, 51]]]
 h' := ![![[0, 62, 66], [24, 94, 41], [32, 38, 68], [89, 85, 30], [21, 26, 64], [62, 1, 68], [0, 1]], ![[68, 38, 35], [54, 97, 86], [99, 17, 42], [74, 5, 84], [90, 76, 7], [28, 46, 24], [0, 62, 66]], ![[0, 1], [11, 11, 75], [78, 46, 92], [32, 11, 88], [36, 100, 30], [16, 54, 9], [68, 38, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 73], []]
 b := ![[], [95, 5, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [39, 100, 33, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26134528205, -9059617988, -1700649514]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258757705, -89699188, -16838114]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [7, 83, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 20, 27], [30, 82, 76], [0, 1]]
 g := ![![[21, 26, 36], [56, 31, 26], [28, 30, 38], [65, 49], [95, 93], [1]], ![[13, 60, 9, 101], [81, 55, 94, 45], [83, 68, 72, 44], [80, 68], [67, 100], [40, 4, 31, 10]], ![[55, 13, 69, 79], [61, 48, 73, 33], [54, 21, 39, 34], [94, 2], [18, 16], [93, 74, 48, 93]]]
 h' := ![![[59, 20, 27], [20, 76, 97], [10, 17, 51], [64, 95, 55], [2, 42, 96], [96, 20, 89], [0, 1]], ![[30, 82, 76], [69, 80, 15], [34, 14, 6], [59, 62, 71], [1, 87, 45], [26, 27, 10], [59, 20, 27]], ![[0, 1], [66, 50, 94], [42, 72, 46], [80, 49, 80], [29, 77, 65], [84, 56, 4], [30, 82, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 4], []]
 b := ![[], [52, 43, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [7, 83, 14, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9480738, -3459049, -669912]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92046, -33583, -6504]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![19, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![19, 1, 0]] 
 ![![107, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![19, 1, 0], ![1, 19, 2], ![355, 73, 20]]]
  hmulB := by decide  
  f := ![![![-309, -5890, -620], ![0, 33170, 0]], ![![-55, -1045, -110], ![1, 5885, 0]], ![![-106, -1872, -197], ![44, 10540, 0]]]
  g := ![![![1, 0, 0], ![-19, 107, 0], ![-34, 0, 107]], ![![0, 1, 0], ![-4, 19, 2], ![-16, 73, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-19, 1, 0]] 
 ![![107, 0, 0], ![88, 1, 0], ![34, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-19, 1, 0], ![1, -19, 2], ![355, 73, -18]]]
  hmulB := by decide  
  f := ![![![-4304, 87195, -9180], ![1605, 491130, 0]], ![![-3526, 71693, -7548], ![1392, 403818, 0]], ![![-1352, 27706, -2917], ![598, 156060, 0]]]
  g := ![![![1, 0, 0], ![-88, 107, 0], ![-34, 0, 107]], ![![-1, 1, 0], ![15, -19, 2], ![-51, 73, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-1, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-1, 1, 0]] 
 ![![107, 0, 0], ![106, 1, 0], ![0, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-1, 1, 0], ![1, -1, 2], ![355, 73, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![54, 54, 0]]]
  g := ![![![1, 0, 0], ![-106, 107, 0], ![0, 0, 107]], ![![-1, 1, 0], ![1, -1, 2], ![-69, 73, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![19, 1, 0]] ![![107, 0, 0], ![-19, 1, 0]]
  ![![107, 0, 0], ![-73, 0, 1]] where
 M := ![![![11449, 0, 0], ![-2033, 107, 0]], ![![2033, 107, 0], ![-360, 0, 2]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![54, 1, -1], ![107, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-73, 0, 1]] ![![107, 0, 0], ![-1, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-107, 107, 0]], ![![-7811, 0, 107], ![428, 0, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-1, 1, 0]]], ![![![-73, 0, 1]], ![![4, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, 9, -2]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![74, 9, -2]] 
 ![![109, 0, 0], ![0, 109, 0], ![72, 50, 1]] where
  M :=![![![74, 9, -2], ![-701, -72, 16], ![2767, 229, -63]]]
  hmulB := by decide  
  f := ![![![-8, -1, 0]], ![![-1, -8, -2]], ![![-9, -5, -1]]]
  g := ![![![2, 1, -2], ![-17, -8, 16], ![67, 31, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [79, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 108], [0, 1]]
 g := ![![[101, 82], [108], [89, 28], [34, 3], [89], [87, 1]], ![[41, 27], [108], [18, 81], [77, 106], [89], [65, 108]]]
 h' := ![![[87, 108], [52, 55], [54, 76], [39, 30], [90, 49], [103, 78], [0, 1]], ![[0, 1], [41, 54], [17, 33], [33, 79], [102, 60], [22, 31], [87, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [92, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [79, 22, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2335, 1128, 258]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-149, -108, 258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![109, 0, 0], ![8, 1, 0], ![23, 0, 1]] where
  M :=![![![8, 1, 0], ![1, 8, 2], ![355, 73, 9]]]
  hmulB := by decide  
  f := ![![![-74, -9, 2]], ![![1, 0, 0]], ![![-41, -4, 1]]]
  g := ![![![0, 1, 0], ![-1, 8, 2], ![-4, 73, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![74, 9, -2]] ![![8, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-18, 51, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-18, 51, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![95, 51, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-18, 51, 1], ![406, 55, 103], ![18319, 3937, 106]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -51, 113]], ![![-1, 0, 1], ![-83, -46, 103], ![73, -13, 106]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [99, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 112], [0, 1]]
 g := ![![[48, 8], [14], [11], [52], [104, 14], [107, 1]], ![[0, 105], [14], [11], [52], [20, 99], [101, 112]]]
 h' := ![![[107, 112], [47, 102], [90, 50], [106, 24], [100, 74], [29, 50], [0, 1]], ![[0, 1], [0, 11], [16, 63], [75, 89], [108, 39], [68, 63], [107, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [81, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [99, 6, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42872, 10438, 1523]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-901, -595, 1523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![10, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![10, 1, 0]] 
 ![![113, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![10, 1, 0], ![1, 10, 2], ![355, 73, 11]]]
  hmulB := by decide  
  f := ![![![-1111, -11219, -2244], ![-113, 126786, 0]], ![![-99, -990, -198], ![1, 11187, 0]], ![![-69, -695, -139], ![-5, 7854, 0]]]
  g := ![![![1, 0, 0], ![-10, 113, 0], ![-7, 0, 113]], ![![0, 1, 0], ![-1, 10, 2], ![-4, 73, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-18, 51, 1]] ![![113, 0, 0], ![10, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![1130, 113, 0]], ![![-2034, 5763, 113], ![226, 565, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![10, 1, 0]]], ![![![-18, 51, 1]], ![![2, 5, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-7, -58, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-7, -58, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![120, 69, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-7, -58, 1], ![297, 66, -115], ![-20376, -4020, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -69, 127]], ![![-1, -1, 1], ![111, 63, -115], ![-168, -36, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [108, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 126], [0, 1]]
 g := ![![[3, 103], [69, 22], [112, 79], [23, 36], [122, 13], [57, 1]], ![[32, 24], [53, 105], [43, 48], [43, 91], [101, 114], [114, 126]]]
 h' := ![![[57, 126], [41, 105], [96, 99], [56, 98], [32, 6], [67, 93], [0, 1]], ![[0, 1], [57, 22], [24, 28], [54, 29], [120, 121], [34, 34], [57, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [8, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [108, 70, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4483, 810, 459]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-469, -243, 459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-12, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-12, 1, 0]] 
 ![![127, 0, 0], ![115, 1, 0], ![119, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-12, 1, 0], ![1, -12, 2], ![355, 73, -11]]]
  hmulB := by decide  
  f := ![![![-6971, 85237, -14208], ![1397, 902208, 0]], ![![-6311, 77174, -12864], ![1271, 816864, 0]], ![![-6535, 79868, -13313], ![1276, 845376, 0]]]
  g := ![![![1, 0, 0], ![-115, 127, 0], ![-119, 0, 127]], ![![-1, 1, 0], ![9, -12, 2], ![-53, 73, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-7, -58, 1]] ![![127, 0, 0], ![-12, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1524, 127, 0]], ![![-889, -7366, 127], ![381, 762, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-12, 1, 0]]], ![![![-7, -58, 1]], ![![3, 6, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-101, -50, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-101, -50, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![30, 81, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-101, -50, 1], ![305, -28, -99], ![-17536, -3436, -78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -81, 131]], ![![-1, -1, 1], ![25, 61, -99], ![-116, 22, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [107, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 130], [0, 1]]
 g := ![![[129, 60], [90, 28], [1], [33], [21], [77], [1]], ![[0, 71], [56, 103], [1], [33], [21], [77], [1]]]
 h' := ![![[83, 130], [64, 45], [126, 40], [44, 1], [13, 66], [66, 26], [24, 83], [0, 1]], ![[0, 1], [0, 86], [40, 91], [127, 130], [120, 65], [128, 105], [101, 48], [83, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [55, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [107, 48, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6472, 4060, 1386]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-268, -826, 1386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-32, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-32, 1, 0]] 
 ![![131, 0, 0], ![99, 1, 0], ![78, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-32, 1, 0], ![1, -32, 2], ![355, 73, -31]]]
  hmulB := by decide  
  f := ![![![-4521, 164141, -10260], ![2489, 672030, 0]], ![![-3427, 124018, -7752], ![1835, 507756, 0]], ![![-2698, 97733, -6109], ![1457, 400140, 0]]]
  g := ![![![1, 0, 0], ![-99, 131, 0], ![-78, 0, 131]], ![![-1, 1, 0], ![23, -32, 2], ![-34, 73, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-101, -50, 1]] ![![131, 0, 0], ![-32, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4192, 131, 0]], ![![-13231, -6550, 131], ![3537, 1572, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-32, 1, 0]]], ![![![-101, -50, 1]], ![![27, 12, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-19, 15, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-19, 15, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![118, 15, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-19, 15, 1], ![370, 54, 31], ![5539, 1309, 69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-118, -15, 137]], ![![-1, 0, 1], ![-24, -3, 31], ![-19, 2, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [7, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 136], [0, 1]]
 g := ![![[76, 98], [135], [7], [55, 107], [63], [119], [1]], ![[0, 39], [135], [7], [123, 30], [63], [119], [1]]]
 h' := ![![[16, 136], [90, 80], [79, 51], [26, 12], [44, 45], [38, 36], [130, 16], [0, 1]], ![[0, 1], [0, 57], [73, 86], [81, 125], [79, 92], [66, 101], [112, 121], [16, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [89, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [7, 121, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4777, 5350, 1270]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1059, -100, 1270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-31, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-31, 1, 0]] 
 ![![137, 0, 0], ![106, 1, 0], ![68, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-31, 1, 0], ![1, -31, 2], ![355, 73, -30]]]
  hmulB := by decide  
  f := ![![![-1456, 50927, -3286], ![822, 225091, 0]], ![![-1146, 39397, -2542], ![549, 174127, 0]], ![![-734, 25278, -1631], ![358, 111724, 0]]]
  g := ![![![1, 0, 0], ![-106, 137, 0], ![-68, 0, 137]], ![![-1, 1, 0], ![23, -31, 2], ![-39, 73, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-19, 15, 1]] ![![137, 0, 0], ![-31, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4247, 137, 0]], ![![-2603, 2055, 137], ![959, -411, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-31, 1, 0]]], ![![![-19, 15, 1]], ![![7, -3, 0]]]]
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


lemma PB234I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB234I2 : PrimesBelowBoundCertificateInterval O 79 137 234 where
  m := 11
  g := ![3, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB234I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I97N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
