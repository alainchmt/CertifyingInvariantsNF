
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-53, -29, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-53, -29, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![30, 54, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-53, -29, 1], ![258, -17, -174], ![-7482, -1001, -17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -54, 83]], ![![-1, -1, 1], ![66, 113, -174], ![-84, -1, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [75, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 82], [0, 1]]
 g := ![![[19, 31], [22, 49], [48], [78], [20, 30], [1]], ![[0, 52], [0, 34], [48], [78], [15, 53], [1]]]
 h' := ![![[69, 82], [10, 60], [68, 76], [79, 31], [77, 24], [8, 69], [0, 1]], ![[0, 1], [0, 23], [0, 7], [60, 52], [73, 59], [38, 14], [69, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [56, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [75, 14, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![591, 101, 28]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -17, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![8, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![8, 1, 0]] 
 ![![83, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![8, 1, 0], ![0, 8, 6], ![258, 36, 8]]]
  hmulB := by decide  
  f := ![![![353, 44, 0], ![-3652, 0, 0]], ![![24, 3, 0], ![-248, 0, 0]], ![![75, 8, -1], ![-776, 14, 0]]]
  g := ![![![1, 0, 0], ![-8, 83, 0], ![-17, 0, 83]], ![![0, 1, 0], ![-2, 8, 6], ![-2, 36, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-53, -29, 1]] ![![83, 0, 0], ![8, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![664, 83, 0]], ![![-4399, -2407, 83], ![-166, -249, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![8, 1, 0]]], ![![![-53, -29, 1]], ![![-2, -3, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [17, 63, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 64, 13], [44, 24, 76], [0, 1]]
 g := ![![[11, 76, 22], [35, 45], [34, 67], [44], [5, 35, 1], []], ![[66, 34, 39, 19], [80, 20], [3, 20], [39, 39, 19, 14], [7, 76, 70, 12], [14, 80]], ![[67, 9, 26, 13], [31, 5], [0, 49], [4, 61, 12, 75], [80, 2, 85, 63], [40, 80]]]
 h' := ![![[80, 64, 13], [64, 11, 17], [6, 63, 57], [53, 3, 45], [4, 69], [0, 0, 1], [0, 1]], ![[44, 24, 76], [55, 55, 17], [13, 55, 51], [81, 8, 51], [6, 55, 7], [21, 77, 24], [80, 64, 13]], ![[0, 1], [6, 23, 55], [55, 60, 70], [12, 78, 82], [14, 54, 82], [10, 12, 64], [44, 24, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 4], []]
 b := ![[], [52, 33, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [17, 63, 54, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-372287, 18957, 46458]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4183, 213, 522]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![10, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![10, 1, 0]] 
 ![![97, 0, 0], ![10, 1, 0], ![48, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![10, 1, 0], ![0, 10, 6], ![258, 36, 10]]]
  hmulB := by decide  
  f := ![![![581, 58, 0], ![-5626, 0, 0]], ![![50, 5, 0], ![-484, 0, 0]], ![![284, 20, -5], ![-2750, 81, 0]]]
  g := ![![![1, 0, 0], ![-10, 97, 0], ![-48, 0, 97]], ![![0, 1, 0], ![-4, 10, 6], ![-6, 36, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![18, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![18, 1, 0]] 
 ![![97, 0, 0], ![18, 1, 0], ![43, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![18, 1, 0], ![0, 18, 6], ![258, 36, 18]]]
  hmulB := by decide  
  f := ![![![415, 23, 0], ![-2231, 0, 0]], ![![54, 3, 0], ![-290, 0, 0]], ![![181, -5, -5], ![-973, 81, 0]]]
  g := ![![![1, 0, 0], ![-18, 97, 0], ![-43, 0, 97]], ![![0, 1, 0], ![-6, 18, 6], ![-12, 36, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4783, 142, -143]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![4783, 142, -143]] 
 ![![97, 0, 0], ![69, 1, 0], ![31, 0, 1]] where
  M :=![![![4783, 142, -143], ![-36894, -365, 852], ![36636, -1037, -365]]]
  hmulB := by decide  
  f := ![![![1016749, 200121, 68789]], ![![906219, 178366, 61311]], ![![857221, 168722, 57996]]]
  g := ![![![-6, 142, -143], ![-393, -365, 852], ![1232, -1037, -365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![10, 1, 0]] ![![97, 0, 0], ![18, 1, 0]]
  ![![1016749, 200121, 68789]] where
 M := ![![![9409, 0, 0], ![1746, 97, 0]], ![![970, 97, 0], ![180, 28, 6]]]
 hmul := by decide  
 g := ![![![![463951, 13774, -13871]], ![![49200, 2191, -1722]]], ![![![10936, 1055, -578]], ![![492, 94, -42]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1016749, 200121, 68789]] ![![4783, 142, -143]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [70, 27, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30, 44], [15, 70, 57], [0, 1]]
 g := ![![[92, 43, 13], [26, 43], [40, 47, 85], [35, 92], [47, 6], [1]], ![[40, 16, 72, 83], [90, 78], [92, 40, 48, 42], [34, 95], [0, 22], [76, 63, 99, 41]], ![[35, 18, 79, 75], [6, 56], [47, 2, 69, 46], [76, 54], [64, 13], [49, 66, 52, 60]]]
 h' := ![![[24, 30, 44], [75, 73, 66], [28, 73, 89], [10, 45, 40], [95, 71, 71], [31, 74, 39], [0, 1]], ![[15, 70, 57], [77, 36, 55], [69, 75, 49], [60, 17, 33], [97, 24, 14], [20, 29, 27], [24, 30, 44]], ![[0, 1], [55, 93, 81], [77, 54, 64], [98, 39, 28], [60, 6, 16], [46, 99, 35], [15, 70, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 42], []]
 b := ![[], [70, 62, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [70, 27, 62, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75548, 8383, -11009]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![748, 83, -109]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![3, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![3, 1, 0]] 
 ![![103, 0, 0], ![3, 1, 0], ![50, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![3, 1, 0], ![0, 3, 6], ![258, 36, 3]]]
  hmulB := by decide  
  f := ![![![196, 65, 0], ![-6695, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![92, 28, -5], ![-3142, 86, 0]]]
  g := ![![![1, 0, 0], ![-3, 103, 0], ![-50, 0, 103]], ![![0, 1, 0], ![-3, 3, 6], ![0, 36, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 6, 2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![31, 6, 2]] 
 ![![103, 0, 0], ![29, 1, 0], ![83, 0, 1]] where
  M :=![![![31, 6, 2], ![516, 103, 36], ![1548, 302, 103]]]
  hmulB := by decide  
  f := ![![![-263, -14, 10]], ![![-49, -3, 2]], ![![-247, -12, 9]]]
  g := ![![![-3, 6, 2], ![-53, 103, 36], ![-153, 302, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-32, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-32, 1, 0]] 
 ![![103, 0, 0], ![71, 1, 0], ![1, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-32, 1, 0], ![0, -32, 6], ![258, 36, -32]]]
  hmulB := by decide  
  f := ![![![1313, -41, 0], ![4223, 0, 0]], ![![961, -30, 0], ![3091, 0, 0]], ![![55, 25, -5], ![177, 86, 0]]]
  g := ![![![1, 0, 0], ![-71, 103, 0], ![-1, 0, 103]], ![![-1, 1, 0], ![22, -32, 6], ![-22, 36, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![3, 1, 0]] ![![31, 6, 2]]
  ![![103, 0, 0], ![-37, -29, 1]] where
 M := ![![![3193, 618, 206]], ![![609, 121, 42]]]
 hmul := by decide  
 g := ![![![![31, 6, 2], ![0, 0, 0]]], ![![![21, 13, 0], ![42, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-37, -29, 1]] ![![103, 0, 0], ![-32, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3296, 103, 0]], ![![-3811, -2987, 103], ![1442, 927, -206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-32, 1, 0]]], ![![![-37, -29, 1]], ![![14, 9, -2]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [54, 73, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 59, 52], [75, 47, 55], [0, 1]]
 g := ![![[41, 69, 41], [24, 85, 9], [33, 14], [59, 104, 34], [69, 1], [1]], ![[29, 69, 95, 48], [101, 98, 75, 37], [89, 37], [53, 87, 9, 11], [36, 16], [2, 19, 7, 10]], ![[88, 74, 65, 7], [100, 51, 54, 58], [49, 1], [67, 42, 6, 22], [34, 9], [33, 35, 13, 97]]]
 h' := ![![[33, 59, 52], [95, 63, 24], [78, 23, 104], [24, 4, 96], [46, 11, 81], [53, 34, 1], [0, 1]], ![[75, 47, 55], [19, 25, 17], [23, 53, 92], [96, 20, 12], [24, 12, 99], [91, 51, 103], [33, 59, 52]], ![[0, 1], [71, 19, 66], [56, 31, 18], [53, 83, 106], [104, 84, 34], [11, 22, 3], [75, 47, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 76], []]
 b := ![[], [96, 16, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [54, 73, 106, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-215712, -31779, 5136]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2016, -297, 48]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [84, 88, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 21, 72], [67, 87, 37], [0, 1]]
 g := ![![[86, 106, 31], [28, 93], [85, 94, 83], [46, 19, 63], [105, 61], [1]], ![[73, 62, 101, 8], [], [31, 98, 46, 56], [40, 8, 13, 91], [1, 83], [37, 13, 13, 32]], ![[13, 7, 31, 2], [89, 93], [53, 102, 46, 2], [1, 57, 57, 51], [98, 21], [98, 73, 22, 77]]]
 h' := ![![[79, 21, 72], [19, 83, 85], [54, 105, 86], [60, 97, 65], [89, 93, 45], [25, 21, 37], [0, 1]], ![[67, 87, 37], [48, 8, 73], [22, 20], [6, 37, 104], [56, 15, 38], [85, 32, 44], [79, 21, 72]], ![[0, 1], [44, 18, 60], [76, 93, 23], [43, 84, 49], [23, 1, 26], [84, 56, 28], [67, 87, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 58], []]
 b := ![[], [42, 50, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [84, 88, 72, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3270, 218, 218]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, 2, 2]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [42, 65, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 42, 91], [52, 70, 22], [0, 1]]
 g := ![![[99, 93, 7], [9, 104], [95, 14], [15, 11], [35, 14, 88], [1]], ![[29, 89, 4, 82], [4, 77], [110, 112], [1, 8], [52, 37, 55, 11], [29, 6, 48, 87]], ![[27, 103, 20, 87], [33, 32], [54, 44], [75, 56], [20, 42, 48, 77], [8, 67, 82, 26]]]
 h' := ![![[23, 42, 91], [10, 35, 81], [106, 15, 68], [49, 83, 63], [112, 31, 89], [71, 48, 75], [0, 1]], ![[52, 70, 22], [89, 23, 41], [101, 103, 23], [75, 88, 98], [111, 19, 11], [101, 107, 13], [23, 42, 91]], ![[0, 1], [58, 55, 104], [75, 108, 22], [99, 55, 65], [56, 63, 13], [39, 71, 25], [52, 70, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 22], []]
 b := ![[], [69, 90, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [42, 65, 38, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11560352, 1898513, 340356]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102304, 16801, 3012]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![59, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![59, 1, 0]] 
 ![![127, 0, 0], ![59, 1, 0], ![76, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![59, 1, 0], ![0, 59, 6], ![258, 36, 59]]]
  hmulB := by decide  
  f := ![![![1299, 22, 0], ![-2794, 0, 0]], ![![531, 9, 0], ![-1142, 0, 0]], ![![782, -36, -5], ![-1682, 106, 0]]]
  g := ![![![1, 0, 0], ![-59, 127, 0], ![-76, 0, 127]], ![![0, 1, 0], ![-31, 59, 6], ![-50, 36, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1951, 384, 132]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1951, 384, 132]] 
 ![![127, 0, 0], ![81, 1, 0], ![113, 0, 1]] where
  M :=![![![1951, 384, 132], ![34056, 6703, 2304], ![99072, 19500, 6703]]]
  hmulB := by decide  
  f := ![![![2209, 48, -60]], ![![1287, 31, -36]], ![![2063, 36, -53]]]
  g := ![![![-347, 384, 132], ![-6057, 6703, 2304], ![-17621, 19500, 6703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-13, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-13, 1, 0]] 
 ![![127, 0, 0], ![114, 1, 0], ![120, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-13, 1, 0], ![0, -13, 6], ![258, 36, -13]]]
  hmulB := by decide  
  f := ![![![1223, -94, 0], ![11938, 0, 0]], ![![1106, -85, 0], ![10796, 0, 0]], ![![1156, -78, -5], ![11284, 106, 0]]]
  g := ![![![1, 0, 0], ![-114, 127, 0], ![-120, 0, 127]], ![![-1, 1, 0], ![6, -13, 6], ![-18, 36, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![59, 1, 0]] ![![1951, 384, 132]]
  ![![127, 0, 0], ![-29, -19, 1]] where
 M := ![![![247777, 48768, 16764]], ![![149165, 29359, 10092]]]
 hmul := by decide  
 g := ![![![![1864, 327, 135], ![-381, 0, 0]]], ![![![1130, 202, 81], ![-195, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-29, -19, 1]] ![![127, 0, 0], ![-13, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1651, 127, 0]], ![![-3683, -2413, 127], ![635, 254, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-13, 1, 0]]], ![![![-29, -19, 1]], ![![5, 2, -1]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [88, 118, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 85, 35], [0, 45, 96], [0, 1]]
 g := ![![[47, 50, 61], [23, 3, 5], [59, 39], [113, 77], [71, 25], [56, 1], []], ![[25, 116, 48, 91], [63, 43, 106, 117], [68, 101], [106, 63], [25, 3], [37, 60], [11, 46]], ![[0, 57, 112, 22], [27, 84, 35, 106], [28, 15], [65, 13], [104, 41], [119, 20], [81, 46]]]
 h' := ![![[56, 85, 35], [72, 12, 89], [97, 31, 23], [124, 32, 63], [51, 105, 48], [50, 116, 5], [0, 0, 1], [0, 1]], ![[0, 45, 96], [78, 73, 102], [83, 125, 24], [33, 14, 25], [86, 70, 71], [94, 76, 93], [72, 113, 45], [56, 85, 35]], ![[0, 1], [113, 46, 71], [34, 106, 84], [128, 85, 43], [79, 87, 12], [42, 70, 33], [77, 18, 85], [0, 45, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 110], []]
 b := ![[], [37, 102, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [88, 118, 75, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2882, -5109, 1703]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, -39, 13]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![55, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![55, 1, 0]] 
 ![![137, 0, 0], ![55, 1, 0], ![21, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![55, 1, 0], ![0, 55, 6], ![258, 36, 55]]]
  hmulB := by decide  
  f := ![![![166, 3, 0], ![-411, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-42, -10, -1], ![105, 23, 0]]]
  g := ![![![1, 0, 0], ![-55, 137, 0], ![-21, 0, 137]], ![![0, 1, 0], ![-23, 55, 6], ![-21, 36, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-29, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-29, 1, 0]] 
 ![![137, 0, 0], ![108, 1, 0], ![111, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-29, 1, 0], ![0, -29, 6], ![258, 36, -29]]]
  hmulB := by decide  
  f := ![![![1915, -66, 0], ![9042, 0, 0]], ![![1538, -53, 0], ![7262, 0, 0]], ![![1563, -49, -1], ![7380, 23, 0]]]
  g := ![![![1, 0, 0], ![-108, 137, 0], ![-111, 0, 137]], ![![-1, 1, 0], ![18, -29, 6], ![-3, 36, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-26, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-26, 1, 0]] 
 ![![137, 0, 0], ![111, 1, 0], ![70, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-26, 1, 0], ![0, -26, 6], ![258, 36, -26]]]
  hmulB := by decide  
  f := ![![![1873, -72, 0], ![9864, 0, 0]], ![![1483, -57, 0], ![7810, 0, 0]], ![![946, -32, -1], ![4982, 23, 0]]]
  g := ![![![1, 0, 0], ![-111, 137, 0], ![-70, 0, 137]], ![![-1, 1, 0], ![18, -26, 6], ![-14, 36, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![55, 1, 0]] ![![137, 0, 0], ![-29, 1, 0]]
  ![![137, 0, 0], ![31, 50, 1]] where
 M := ![![![18769, 0, 0], ![-3973, 137, 0]], ![![7535, 137, 0], ![-1595, 26, 6]]]
 hmul := by decide  
 g := ![![![![106, -50, -1], ![137, 0, 0]], ![![-29, 1, 0], ![0, 0, 0]]], ![![![24, -49, -1], ![137, 0, 0]], ![![-13, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![31, 50, 1]] ![![137, 0, 0], ![-26, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3562, 137, 0]], ![![4247, 6850, 137], ![-548, -1233, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-26, 1, 0]]], ![![![31, 50, 1]], ![![-4, -9, 2]]]]
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


lemma PB233I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB233I2 : PrimesBelowBoundCertificateInterval O 79 137 233 where
  m := 11
  g := ![2, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB233I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I97N0, I97N1, I97N2, I103N0, I103N1, I103N2, I127N0, I127N1, I127N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [], [I97N0, I97N1, I97N2], [], [I103N0, I103N1, I103N2], [], [], [], [I127N0, I127N1, I127N2], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
