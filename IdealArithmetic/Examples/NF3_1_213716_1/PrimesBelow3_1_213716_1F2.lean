
import IdealArithmetic.Examples.NF3_1_213716_1.RI3_1_213716_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![30, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![30, 1, 0]] 
 ![![83, 0, 0], ![30, 1, 0], ![13, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![30, 1, 0], ![0, 30, 1], ![-86, -8, 31]]]
  hmulB := by decide  
  f := ![![![781, 26, 0], ![-2158, 0, 0]], ![![270, 9, 0], ![-746, 0, 0]], ![![71, 2, 0], ![-196, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 83, 0], ![-13, 0, 83]], ![![0, 1, 0], ![-11, 30, 1], ![-3, -8, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -1, -1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![9, -1, -1]] 
 ![![83, 0, 0], ![56, 1, 0], ![18, 0, 1]] where
  M :=![![![9, -1, -1], ![86, 17, -2], ![172, 102, 15]]]
  hmulB := by decide  
  f := ![![![-459, 87, -19]], ![![-290, 55, -12]], ![![-170, 32, -7]]]
  g := ![![![1, -1, -1], ![-10, 17, -2], ![-70, 102, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-4, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-4, 1, 0]] 
 ![![83, 0, 0], ![79, 1, 0], ![67, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-4, 1, 0], ![0, -4, 1], ![-86, -8, -3]]]
  hmulB := by decide  
  f := ![![![93, -23, 0], ![1909, 0, 0]], ![![89, -22, 0], ![1827, 0, 0]], ![![77, -19, 0], ![1581, 1, 0]]]
  g := ![![![1, 0, 0], ![-79, 83, 0], ![-67, 0, 83]], ![![-1, 1, 0], ![3, -4, 1], ![9, -8, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![30, 1, 0]] ![![9, -1, -1]]
  ![![83, 0, 0], ![20, 3, 1]] where
 M := ![![![747, -83, -83]], ![![356, -13, -32]]]
 hmul := by decide  
 g := ![![![![-11, -4, -2], ![83, 0, 0]]], ![![![-8, -2, -1], ![51, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![20, 3, 1]] ![![83, 0, 0], ![-4, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-332, 83, 0]], ![![1660, 249, 83], ![-166, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-4, 1, 0]]], ![![![20, 3, 1]], ![![-2, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![39, -42, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![39, -42, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![39, 47, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![39, -42, 1], ![-86, 31, -41], ![3526, 242, -10]]]
  hmulB := by decide  
  f := ![![![-38, 42, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -47, 89]], ![![0, -1, 1], ![17, 22, -41], ![44, 8, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [83, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 88], [0, 1]]
 g := ![![[68, 71], [67], [80], [84, 42], [78, 34], [1]], ![[22, 18], [67], [80], [43, 47], [66, 55], [1]]]
 h' := ![![[52, 88], [24, 58], [45, 45], [59, 76], [23, 24], [6, 52], [0, 1]], ![[0, 1], [14, 31], [71, 44], [6, 13], [25, 65], [40, 37], [52, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [50, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [83, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-175, -147, -41]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 20, -41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![41, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![41, 1, 0]] 
 ![![89, 0, 0], ![41, 1, 0], ![10, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![41, 1, 0], ![0, 41, 1], ![-86, -8, 42]]]
  hmulB := by decide  
  f := ![![![1067, 26, 0], ![-2314, 0, 0]], ![![451, 11, 0], ![-978, 0, 0]], ![![60, 1, 0], ![-130, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 89, 0], ![-10, 0, 89]], ![![0, 1, 0], ![-19, 41, 1], ![-2, -8, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![39, -42, 1]] ![![89, 0, 0], ![41, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3649, 89, 0]], ![![3471, -3738, 89], ![1513, -1691, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![41, 1, 0]]], ![![![39, -42, 1]], ![![17, -19, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [45, 75, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 10, 20], [76, 86, 77], [0, 1]]
 g := ![![[61, 29, 24], [52, 11], [88, 18], [10, 66], [64, 75], [1]], ![[58, 7, 4, 68], [10, 3], [51, 18], [58, 44], [94, 12], [89, 51, 0, 46]], ![[18, 18, 32, 17], [58, 75], [], [68, 62], [72, 27], [44, 47, 61, 51]]]
 h' := ![![[68, 10, 20], [19, 72, 86], [82, 16, 37], [68, 76, 55], [18, 30, 39], [52, 22, 47], [0, 1]], ![[76, 86, 77], [66, 39, 9], [82, 8, 10], [90, 91, 42], [88, 69, 74], [27, 61, 20], [68, 10, 20]], ![[0, 1], [10, 83, 2], [96, 73, 50], [75, 27], [82, 95, 81], [11, 14, 30], [76, 86, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 80], []]
 b := ![[], [51, 89, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [45, 75, 50, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211751, 1164, -1746]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2183, 12, -18]
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


def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![17, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![17, 1, 0]] 
 ![![101, 0, 0], ![17, 1, 0], ![14, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![17, 1, 0], ![0, 17, 1], ![-86, -8, 18]]]
  hmulB := by decide  
  f := ![![![69, 4, 0], ![-404, 0, 0]], ![![-17, -1, 0], ![102, 0, 0]], ![![-14, -1, 0], ![84, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 101, 0], ![-14, 0, 101]], ![![0, 1, 0], ![-3, 17, 1], ![-2, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![88, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![0, -35, 1], ![-86, -8, -34]]]
  hmulB := by decide  
  f := ![![![1331, -38, 0], ![3838, 0, 0]], ![![876, -25, 0], ![2526, 0, 0]], ![![1168, -33, 0], ![3368, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-88, 0, 101]], ![![-1, 1, 0], ![22, -35, 1], ![34, -8, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![17, 1, 0]] ![![101, 0, 0], ![17, 1, 0]]
  ![![101, 0, 0], ![-14, 34, 1]] where
 M := ![![![10201, 0, 0], ![1717, 101, 0]], ![![1717, 101, 0], ![289, 34, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![17, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-14, 34, 1]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![-1414, 3434, 101], ![404, -1212, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-35, 1, 0]]], ![![![-14, 34, 1]], ![![4, -12, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N0
    exact isPrimeI101N1
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [65, 21, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 28, 77], [74, 74, 26], [0, 1]]
 g := ![![[91, 51, 63], [84, 96, 34], [84, 9, 100], [47, 1], [93, 76], [1]], ![[52, 96, 0, 94], [99, 38, 72, 96], [83, 2, 46, 5], [14, 82], [27, 19], [53, 77, 8, 37]], ![[60, 42, 40, 18], [93, 73, 19, 18], [58, 94, 33, 38], [48, 98], [71, 19], [97, 43, 24, 66]]]
 h' := ![![[59, 28, 77], [102, 31, 75], [102, 88, 72], [58, 41, 10], [34, 60, 1], [38, 82, 30], [0, 1]], ![[74, 74, 26], [73, 40, 6], [66, 17, 53], [80, 90, 86], [28, 91, 59], [54, 49, 88], [59, 28, 77]], ![[0, 1], [6, 32, 22], [76, 101, 81], [61, 75, 7], [20, 55, 43], [0, 75, 88], [74, 74, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 86], []]
 b := ![[], [76, 36, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [65, 21, 73, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18643, 11021, -2163]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181, 107, -21]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![50, -7, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![50, -7, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![50, 100, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![50, -7, 1], ![-86, 42, -6], ![516, -38, 36]]]
  hmulB := by decide  
  f := ![![![-49, 7, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -100, 107]], ![![0, -1, 1], ![2, 6, -6], ![-12, -34, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [47, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 106], [0, 1]]
 g := ![![[99, 41], [22, 85], [1], [48, 35], [3], [55, 1]], ![[0, 66], [96, 22], [1], [47, 72], [3], [3, 106]]]
 h' := ![![[55, 106], [36, 83], [34, 37], [98, 1], [41, 28], [90, 89], [0, 1]], ![[0, 1], [0, 24], [36, 70], [46, 106], [83, 79], [63, 18], [55, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [1, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [47, 52, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-158, -744, -230]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106, 208, -230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![6, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![6, 1, 0]] 
 ![![107, 0, 0], ![6, 1, 0], ![71, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![6, 1, 0], ![0, 6, 1], ![-86, -8, 7]]]
  hmulB := by decide  
  f := ![![![97, 16, 0], ![-1712, 0, 0]], ![![-6, -1, 0], ![108, 0, 0]], ![![61, 10, 0], ![-1076, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 107, 0], ![-71, 0, 107]], ![![0, 1, 0], ![-1, 6, 1], ![-5, -8, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![50, -7, 1]] ![![107, 0, 0], ![6, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![642, 107, 0]], ![![5350, -749, 107], ![214, 0, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![6, 1, 0]]], ![![![50, -7, 1]], ![![2, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![50, 6, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![50, 6, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![50, 6, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![50, 6, 1], ![-86, 42, 7], ![-602, -142, 49]]]
  hmulB := by decide  
  f := ![![![-49, -6, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -6, 109]], ![![0, 0, 1], ![-4, 0, 7], ![-28, -4, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [70, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 108], [0, 1]]
 g := ![![[108, 38], [20], [60, 66], [55, 82], [66], [70, 1]], ![[43, 71], [20], [102, 43], [18, 27], [66], [31, 108]]]
 h' := ![![[70, 108], [2, 16], [51, 42], [74, 34], [92, 55], [5, 34], [0, 1]], ![[0, 1], [32, 93], [48, 67], [56, 75], [18, 54], [96, 75], [70, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [38, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [70, 39, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188, -149, -43]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 1, -43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-7, 1, 0]] 
 ![![109, 0, 0], ![102, 1, 0], ![60, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-7, 1, 0], ![0, -7, 1], ![-86, -8, -6]]]
  hmulB := by decide  
  f := ![![![575, -82, 0], ![8938, 0, 0]], ![![540, -77, 0], ![8394, 0, 0]], ![![316, -45, 0], ![4912, 1, 0]]]
  g := ![![![1, 0, 0], ![-102, 109, 0], ![-60, 0, 109]], ![![-1, 1, 0], ![6, -7, 1], ![10, -8, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![50, 6, 1]] ![![109, 0, 0], ![-7, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-763, 109, 0]], ![![5450, 654, 109], ![-436, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-7, 1, 0]]], ![![![50, 6, 1]], ![![-4, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![28, 4, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![28, 4, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![28, 4, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![28, 4, 1], ![-86, 20, 5], ![-430, -126, 25]]]
  hmulB := by decide  
  f := ![![![-27, -4, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -4, 113]], ![![0, 0, 1], ![-2, 0, 5], ![-10, -2, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [61, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 112], [0, 1]]
 g := ![![[63, 63], [72], [11], [77], [41, 97], [112, 1]], ![[0, 50], [72], [11], [77], [57, 16], [111, 112]]]
 h' := ![![[112, 112], [17, 17], [51, 33], [48, 24], [98, 23], [61, 53], [0, 1]], ![[0, 1], [0, 96], [18, 80], [24, 89], [75, 90], [8, 60], [112, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [20, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [61, 1, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3291, -341, 395]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-127, -17, 395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-5, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-5, 1, 0]] 
 ![![113, 0, 0], ![108, 1, 0], ![88, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-5, 1, 0], ![0, -5, 1], ![-86, -8, -4]]]
  hmulB := by decide  
  f := ![![![361, -72, 0], ![8136, 0, 0]], ![![346, -69, 0], ![7798, 0, 0]], ![![276, -55, 0], ![6220, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 113, 0], ![-88, 0, 113]], ![![-1, 1, 0], ![4, -5, 1], ![10, -8, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![28, 4, 1]] ![![113, 0, 0], ![-5, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-565, 113, 0]], ![![3164, 452, 113], ![-226, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-5, 1, 0]]], ![![![28, 4, 1]], ![![-2, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [87, 112, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 117, 71], [26, 9, 56], [0, 1]]
 g := ![![[41, 47, 120], [29, 61, 44], [105, 33, 41], [69, 49, 37], [72, 15, 98], [1]], ![[21, 121, 90, 8], [67, 119, 41, 31], [51, 34, 75, 35], [70, 31, 30, 30], [98, 30, 77, 47], [90, 36, 21, 25]], ![[30, 114, 40, 123], [111, 71, 112, 56], [57, 108, 18, 63], [69, 67, 111, 46], [118, 11, 126, 109], [4, 74, 96, 102]]]
 h' := ![![[116, 117, 71], [17, 35, 82], [9, 114, 67], [93, 104, 101], [86, 105, 75], [40, 15, 15], [0, 1]], ![[26, 9, 56], [70, 69, 48], [101, 96, 61], [108, 29, 38], [106, 72, 2], [110, 49, 57], [116, 117, 71]], ![[0, 1], [63, 23, 124], [43, 44, 126], [88, 121, 115], [65, 77, 50], [83, 63, 55], [26, 9, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 120], []]
 b := ![[], [48, 46, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [87, 112, 112, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43688, -4699, -889]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![344, -37, -7]
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



lemma PB131I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 130 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 130 (by omega)

def PB131I2 : PrimesBelowBoundCertificateInterval O 79 130 131 where
  m := 9
  g := ![3, 2, 1, 3, 1, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127]
  hP := PB131I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI101N0
      exact NI101N1
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
  β := ![I83N0, I83N1, I83N2, I89N1, I101N0, I101N1, I107N1, I109N1, I113N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [], [I101N0, I101N0, I101N1], [], [I107N1], [I109N1], [I113N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
