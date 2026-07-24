
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![0, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![0, 1, 0]] 
 ![![83, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![0, 0, 1], ![-332, 73, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![0, 0, 1], ![-4, 73, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![12, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![12, 1, 0]] 
 ![![83, 0, 0], ![12, 1, 0], ![22, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![12, 1, 0], ![0, 12, 1], ![-332, 73, 13]]]
  hmulB := by decide  
  f := ![![![61, 5, 0], ![-415, 0, 0]], ![![-12, -1, 0], ![84, 0, 0]], ![![2, 0, 0], ![-12, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 83, 0], ![-22, 0, 83]], ![![0, 1, 0], ![-2, 12, 1], ![-18, 73, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-13, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-13, 1, 0]] 
 ![![83, 0, 0], ![70, 1, 0], ![80, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-13, 1, 0], ![0, -13, 1], ![-332, 73, -12]]]
  hmulB := by decide  
  f := ![![![521, -40, 0], ![3320, 0, 0]], ![![430, -33, 0], ![2740, 0, 0]], ![![484, -37, 0], ![3084, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 83, 0], ![-80, 0, 83]], ![![-1, 1, 0], ![10, -13, 1], ![-54, 73, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![0, 1, 0]] ![![83, 0, 0], ![12, 1, 0]]
  ![![83, 0, 0], ![-83, 12, 1]] where
 M := ![![![6889, 0, 0], ![996, 83, 0]], ![![0, 83, 0], ![0, 12, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![83, -11, -1], ![83, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-83, 12, 1]] ![![83, 0, 0], ![-13, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1079, 83, 0]], ![![-6889, 996, 83], ![747, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-13, 1, 0]]], ![![![-83, 12, 1]], ![![9, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-40, 34, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-40, 34, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![49, 34, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-40, 34, 1], ![-332, 33, 35], ![-11620, 2223, 68]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -34, 89]], ![![-1, 0, 1], ![-23, -13, 35], ![-168, -1, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [72, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[34, 68], [49], [47], [16, 49], [83, 67], [1]], ![[0, 21], [49], [47], [36, 40], [5, 22], [1]]]
 h' := ![![[44, 88], [27, 54], [23, 82], [5, 15], [76, 7], [17, 44], [0, 1]], ![[0, 1], [0, 35], [71, 7], [42, 74], [28, 82], [84, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [59, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [72, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924, -158, 32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -14, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-35, 1, 0]] 
 ![![89, 0, 0], ![54, 1, 0], ![21, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-35, 1, 0], ![0, -35, 1], ![-332, 73, -34]]]
  hmulB := by decide  
  f := ![![![1471, -42, 0], ![3738, 0, 0]], ![![876, -25, 0], ![2226, 0, 0]], ![![399, -11, 0], ![1014, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 89, 0], ![-21, 0, 89]], ![![-1, 1, 0], ![21, -35, 1], ![-40, 73, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-40, 34, 1]] ![![89, 0, 0], ![-35, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3115, 89, 0]], ![![-3560, 3026, 89], ![1068, -1157, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-35, 1, 0]]], ![![![-40, 34, 1]], ![![12, -13, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [60, 90, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 79, 15], [82, 17, 82], [0, 1]]
 g := ![![[62, 7, 66], [67, 64], [13, 81], [41, 72], [5, 73], [1]], ![[57, 65, 94, 5], [65, 93], [17, 93], [1, 64], [34, 73], [56, 82, 82, 77]], ![[66, 49, 37, 92], [3, 35], [38, 93], [53, 53], [78, 1], [5, 38, 19, 20]]]
 h' := ![![[63, 79, 15], [29, 3, 39], [84, 12, 89], [66, 59, 88], [2, 53, 84], [37, 7, 48], [0, 1]], ![[82, 17, 82], [73, 79, 29], [44, 90, 44], [26, 34, 53], [59, 4, 89], [16, 75, 48], [63, 79, 15]], ![[0, 1], [30, 15, 29], [4, 92, 61], [21, 4, 53], [0, 40, 21], [11, 15, 1], [82, 17, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 34], []]
 b := ![[], [42, 4, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [60, 90, 49, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3021550, -1459171, 174794]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31150, -15043, 1802]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [22, 17, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 86, 34], [82, 14, 67], [0, 1]]
 g := ![![[65], [98, 22], [98, 90, 22], [18, 80], [28, 13], [1]], ![[78, 48, 92, 66], [41, 24], [5, 89, 35, 3], [88, 45], [4, 31], [98, 99, 76, 15]], ![[17, 72, 21, 35], [26, 76], [10, 53, 26, 3], [93, 5], [23, 64], [48, 31, 92, 86]]]
 h' := ![![[85, 86, 34], [79, 60], [66, 55, 74], [60, 14, 74], [70, 87, 22], [79, 84, 66], [0, 1]], ![[82, 14, 67], [28, 9, 20], [83, 5, 78], [26, 14, 98], [12, 20, 34], [10, 89, 43], [85, 86, 34]], ![[0, 1], [50, 32, 81], [4, 41, 50], [70, 73, 30], [55, 95, 45], [64, 29, 93], [82, 14, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 57], []]
 b := ![[], [8, 35, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [22, 17, 35, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-306434, 125543, -24947]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3034, 1243, -247]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-61, -4, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-61, -4, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![42, 99, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-61, -4, 1], ![-332, 12, -3], ![996, -551, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -99, 103]], ![![-1, -1, 1], ![-2, 3, -3], ![6, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [70, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 102], [0, 1]]
 g := ![![[100, 14], [6, 14], [63, 9], [83], [32], [4, 1]], ![[53, 89], [62, 89], [99, 94], [83], [32], [8, 102]]]
 h' := ![![[4, 102], [95, 23], [19, 80], [56, 3], [43, 86], [29, 49], [0, 1]], ![[0, 1], [84, 80], [30, 23], [68, 100], [78, 17], [19, 54], [4, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [39, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [70, 99, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-826, -2668, 358]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-154, -370, 358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![3, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![3, 1, 0]] 
 ![![103, 0, 0], ![3, 1, 0], ![94, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![3, 1, 0], ![0, 3, 1], ![-332, 73, 4]]]
  hmulB := by decide  
  f := ![![![196, 65, 0], ![-6695, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![178, 59, 0], ![-6080, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 103, 0], ![-94, 0, 103]], ![![0, 1, 0], ![-1, 3, 1], ![-9, 73, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-61, -4, 1]] ![![103, 0, 0], ![3, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![309, 103, 0]], ![![-6283, -412, 103], ![-515, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![3, 1, 0]]], ![![![-61, -4, 1]], ![![-5, 0, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [46, 102, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 35, 102], [100, 71, 5], [0, 1]]
 g := ![![[24, 60, 62], [0, 77, 29], [43, 27], [63, 5, 62], [5, 76], [1]], ![[29, 93, 30, 57], [40, 65, 49, 9], [66, 100], [18, 44, 96, 105], [36, 69], [41, 104, 46, 89]], ![[91, 5, 82, 88], [22, 81, 77, 97], [20, 30], [96, 99, 62, 24], [19, 40], [106, 105, 93, 18]]]
 h' := ![![[73, 35, 102], [0, 81, 94], [29, 101, 55], [98, 80, 54], [67, 28, 13], [61, 5, 66], [0, 1]], ![[100, 71, 5], [25, 70, 63], [7, 72, 83], [49, 5, 10], [81, 0, 34], [5, 64, 60], [73, 35, 102]], ![[0, 1], [30, 63, 57], [105, 41, 76], [13, 22, 43], [23, 79, 60], [24, 38, 88], [100, 71, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 58], []]
 b := ![[], [46, 2, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [46, 102, 41, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27178, 18832, -1498]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-254, 176, -14]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![29, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![29, 1, 0]] 
 ![![109, 0, 0], ![29, 1, 0], ![31, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![29, 1, 0], ![0, 29, 1], ![-332, 73, 30]]]
  hmulB := by decide  
  f := ![![![1509, 52, 0], ![-5668, 0, 0]], ![![377, 13, 0], ![-1416, 0, 0]], ![![443, 15, 0], ![-1664, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 109, 0], ![-31, 0, 109]], ![![0, 1, 0], ![-8, 29, 1], ![-31, 73, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![39, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![39, 1, 0]] 
 ![![109, 0, 0], ![39, 1, 0], ![5, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![39, 1, 0], ![0, 39, 1], ![-332, 73, 40]]]
  hmulB := by decide  
  f := ![![![469, 12, 0], ![-1308, 0, 0]], ![![117, 3, 0], ![-326, 0, 0]], ![![-25, -1, 0], ![70, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 109, 0], ![-5, 0, 109]], ![![0, 1, 0], ![-14, 39, 1], ![-31, 73, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![40, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![40, 1, 0]] 
 ![![109, 0, 0], ![40, 1, 0], ![35, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![40, 1, 0], ![0, 40, 1], ![-332, 73, 41]]]
  hmulB := by decide  
  f := ![![![961, 24, 0], ![-2616, 0, 0]], ![![360, 9, 0], ![-980, 0, 0]], ![![255, 6, 0], ![-694, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 109, 0], ![-35, 0, 109]], ![![0, 1, 0], ![-15, 40, 1], ![-43, 73, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![29, 1, 0]] ![![109, 0, 0], ![39, 1, 0]]
  ![![109, 0, 0], ![-68, -41, 1]] where
 M := ![![![11881, 0, 0], ![4251, 109, 0]], ![![3161, 109, 0], ![1131, 68, 1]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![39, 1, 0], ![0, 0, 0]]], ![![![29, 1, 0], ![0, 0, 0]], ![![11, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-68, -41, 1]] ![![109, 0, 0], ![40, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![4360, 109, 0]], ![![-7412, -4469, 109], ![-3052, -1635, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![40, 1, 0]]], ![![![-68, -41, 1]], ![![-28, -15, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [83, 111, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 34, 39], [21, 78, 74], [0, 1]]
 g := ![![[20, 23, 18], [77, 7], [32, 8], [95, 111], [25, 12, 85], [1]], ![[18, 76, 64, 78], [21, 82], [48, 56], [95, 64], [11, 29, 35, 107], [94, 17, 109, 107]], ![[48, 8, 18, 27], [16, 83], [15, 4], [26, 26], [25, 95, 1, 20], [35, 46, 74, 6]]]
 h' := ![![[35, 34, 39], [78, 90, 73], [64, 42, 81], [11, 60, 102], [72, 67, 26], [30, 2, 56], [0, 1]], ![[21, 78, 74], [24, 31, 51], [33, 67, 46], [66, 29, 13], [70, 15, 8], [43, 105, 39], [35, 34, 39]], ![[0, 1], [30, 105, 102], [51, 4, 99], [77, 24, 111], [38, 31, 79], [28, 6, 18], [21, 78, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 36], []]
 b := ![[], [24, 49, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [83, 111, 57, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4752328, 626359, 109949]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42056, 5543, 973]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![8, 21, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![8, 21, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![8, 21, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![8, 21, 1], ![-332, 81, 22], ![-7304, 1274, 103]]]
  hmulB := by decide  
  f := ![![![-7, -21, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -21, 127]], ![![0, 0, 1], ![-4, -3, 22], ![-64, -7, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [113, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 126], [0, 1]]
 g := ![![[92, 9], [22, 15], [57, 11], [36, 50], [53, 71], [18, 1]], ![[0, 118], [38, 112], [1, 116], [47, 77], [61, 56], [36, 126]]]
 h' := ![![[18, 126], [54, 124], [36, 53], [123, 97], [107, 47], [125, 84], [0, 1]], ![[0, 1], [0, 3], [101, 74], [91, 30], [64, 80], [113, 43], [18, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [109, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [113, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1665, -376, -30]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 2, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-22, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-22, 1, 0]] 
 ![![127, 0, 0], ![105, 1, 0], ![24, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-22, 1, 0], ![0, -22, 1], ![-332, 73, -21]]]
  hmulB := by decide  
  f := ![![![1409, -64, 0], ![8128, 0, 0]], ![![1167, -53, 0], ![6732, 0, 0]], ![![268, -12, 0], ![1546, 1, 0]]]
  g := ![![![1, 0, 0], ![-105, 127, 0], ![-24, 0, 127]], ![![-1, 1, 0], ![18, -22, 1], ![-59, 73, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![8, 21, 1]] ![![127, 0, 0], ![-22, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2794, 127, 0]], ![![1016, 2667, 127], ![-508, -381, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-22, 1, 0]]], ![![![8, 21, 1]], ![![-4, -3, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 2, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-67, 2, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![64, 2, 1]] where
  M :=![![![-67, 2, 1], ![-332, 6, 3], ![-996, -113, 9]]]
  hmulB := by decide  
  f := ![![![3, -1, 0]], ![![0, 3, -1]], ![![4, -1, 0]]]
  g := ![![![-1, 0, 1], ![-4, 0, 3], ![-12, -1, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [79, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 130], [0, 1]]
 g := ![![[101, 4], [115, 91], [94], [13], [59], [13], [1]], ![[18, 127], [28, 40], [94], [13], [59], [13], [1]]]
 h' := ![![[12, 130], [85, 129], [82, 22], [33, 15], [76, 12], [105, 94], [52, 12], [0, 1]], ![[0, 1], [61, 2], [84, 109], [82, 116], [89, 119], [54, 37], [65, 119], [12, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [70, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [79, 119, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2577, -625, 539]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-283, -13, 539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![131, 0, 0], ![128, 1, 0], ![122, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![-332, 73, -2]]]
  hmulB := by decide  
  f := ![![![67, -2, -1]], ![![68, -2, -1]], ![![70, -1, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![-72, 73, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-67, 2, 1]] ![![-3, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [114, 45, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 12, 23], [23, 124, 114], [0, 1]]
 g := ![![[95, 132, 87], [99, 36], [57, 32], [66, 68, 9], [78, 133], [16, 1], []], ![[71, 101, 10, 26], [88, 1], [99, 107], [23, 19, 120, 90], [83, 25], [70, 32], [111, 118]], ![[81, 75, 20, 29], [115, 49], [51, 76], [122, 104, 113, 79], [10, 103], [115, 7], [20, 118]]]
 h' := ![![[130, 12, 23], [93, 75, 19], [62, 63, 6], [11, 86, 124], [81, 33, 3], [94, 125, 74], [0, 0, 1], [0, 1]], ![[23, 124, 114], [97, 127, 108], [26, 36, 1], [107, 126, 92], [121, 36, 35], [104, 18, 132], [136, 17, 124], [130, 12, 23]], ![[0, 1], [59, 72, 10], [47, 38, 130], [92, 62, 58], [108, 68, 99], [120, 131, 68], [30, 120, 12], [23, 124, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 129], []]
 b := ![[], [18, 88, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [114, 45, 121, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5090920, -1649206, 150974]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37160, -12038, 1102]
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



lemma PB280I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB280I2 : PrimesBelowBoundCertificateInterval O 79 137 280 where
  m := 11
  g := ![3, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB280I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
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
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![1442897]
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
      exact NI109N1
      exact NI109N2
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N1, I103N1, I109N0, I109N1, I109N2, I127N1, I131N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [], [], [I103N1], [], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
