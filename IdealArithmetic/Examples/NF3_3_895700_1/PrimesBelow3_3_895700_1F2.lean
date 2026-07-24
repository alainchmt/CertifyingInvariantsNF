
import IdealArithmetic.Examples.NF3_3_895700_1.RI3_3_895700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-40, -28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-40, -28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![43, 55, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-40, -28, 1], ![-456, 46, -55], ![11813, -2579, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -55, 83]], ![![-1, -1, 1], ![23, 37, -55], ![133, -43, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [35, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 82], [0, 1]]
 g := ![![[65, 69], [36, 31], [69], [75], [11, 77], [1]], ![[43, 14], [61, 52], [69], [75], [49, 6], [1]]]
 h' := ![![[49, 82], [68, 22], [67, 23], [18, 22], [30, 65], [48, 49], [0, 1]], ![[0, 1], [67, 61], [32, 60], [17, 61], [61, 18], [42, 34], [49, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [73, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [35, 34, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2393, -372, 286]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, -194, 286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-28, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-28, 1, 0]] 
 ![![83, 0, 0], ![55, 1, 0], ![65, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-28, 1, 0], ![1, -28, 2], ![-428, 86, -27]]]
  hmulB := by decide  
  f := ![![![4665, -163478, 11680], ![-3486, -484720, 0]], ![![3086, -108304, 7738], ![-2323, -321127, 0]], ![![3655, -128025, 9147], ![-2725, -379600, 0]]]
  g := ![![![1, 0, 0], ![-55, 83, 0], ![-65, 0, 83]], ![![-1, 1, 0], ![17, -28, 2], ![-41, 86, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-40, -28, 1]] ![![83, 0, 0], ![-28, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2324, 83, 0]], ![![-3320, -2324, 83], ![664, 830, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-28, 1, 0]]], ![![![-40, -28, 1]], ![![8, 10, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![53, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![1, 42, 2], ![-428, 86, 43]]]
  hmulB := by decide  
  f := ![![![-2738, -180269, -8586], ![-3293, 382077, 0]], ![![-1311, -85033, -4050], ![-1512, 180225, 0]], ![![-1664, -107352, -5113], ![-1890, 227529, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-53, 0, 89]], ![![0, 1, 0], ![-21, 42, 2], ![-71, 86, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-40, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-40, 1, 0]] 
 ![![89, 0, 0], ![49, 1, 0], ![46, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-40, 1, 0], ![1, -40, 2], ![-428, 86, -39]]]
  hmulB := by decide  
  f := ![![![-599, 36792, -1840], ![712, 81880, 0]], ![![-305, 20235, -1012], ![446, 45034, 0]], ![![-306, 19016, -951], ![376, 42320, 0]]]
  g := ![![![1, 0, 0], ![-49, 89, 0], ![-46, 0, 89]], ![![-1, 1, 0], ![21, -40, 2], ![-32, 86, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-3, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-3, 1, 0]] 
 ![![89, 0, 0], ![86, 1, 0], ![85, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-3, 1, 0], ![1, -3, 2], ![-428, 86, -2]]]
  hmulB := by decide  
  f := ![![![-3294, 9909, -6608], ![267, 294056, 0]], ![![-3182, 9573, -6384], ![268, 284088, 0]], ![![-3147, 9464, -6311], ![224, 280840, 0]]]
  g := ![![![1, 0, 0], ![-86, 89, 0], ![-85, 0, 89]], ![![-1, 1, 0], ![1, -3, 2], ![-86, 86, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![42, 1, 0]] ![![89, 0, 0], ![-40, 1, 0]]
  ![![89, 0, 0], ![-83, 1, 1]] where
 M := ![![![7921, 0, 0], ![-3560, 89, 0]], ![![3738, 89, 0], ![-1679, 2, 2]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![43, 0, -1], ![89, 0, 0]]], ![![![42, 1, 0], ![0, 0, 0]], ![![66, -1, -1], ![91, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-83, 1, 1]] ![![89, 0, 0], ![-3, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-267, 89, 0]], ![![-7387, 89, 89], ![-178, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-3, 1, 0]]], ![![![-83, 1, 1]], ![![-2, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [42, 19, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 39, 69], [90, 57, 28], [0, 1]]
 g := ![![[37, 64, 75], [7, 95], [66, 64], [47, 6], [1, 81], [1]], ![[22, 36, 32, 17], [64, 73], [64, 11], [51, 85], [15, 70], [41, 32, 42, 67]], ![[12, 56, 12, 55], [83, 54], [58, 65], [72, 81], [55, 3], [34, 8, 31, 30]]]
 h' := ![![[95, 39, 69], [61, 20, 50], [89, 26, 80], [57, 28, 8], [73, 18, 54], [55, 78, 88], [0, 1]], ![[90, 57, 28], [50, 27, 59], [64, 42, 49], [91, 83, 60], [14, 75, 52], [16, 91, 19], [95, 39, 69]], ![[0, 1], [5, 50, 85], [22, 29, 65], [18, 83, 29], [61, 4, 88], [72, 25, 87], [90, 57, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 13], []]
 b := ![[], [55, 44, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [42, 19, 9, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12907887, -4872213, 962919]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![133071, -50229, 9927]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-74, 20, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-74, 20, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![27, 20, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-74, 20, 1], ![-408, 12, 41], ![-8731, 1549, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -20, 101]], ![![-1, 0, 1], ![-15, -8, 41], ![-95, 9, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [59, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 100], [0, 1]]
 g := ![![[2, 54], [88], [67, 49], [54], [77], [84, 1]], ![[94, 47], [88], [42, 52], [54], [77], [67, 100]]]
 h' := ![![[84, 100], [54, 16], [87, 47], [21, 7], [51, 16], [94, 28], [0, 1]], ![[0, 1], [85, 85], [96, 54], [3, 94], [82, 85], [22, 73], [84, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [74, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [59, 17, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-685200, -756341, 381944]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108888, -83121, 381944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-41, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-41, 1, 0]] 
 ![![101, 0, 0], ![60, 1, 0], ![69, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-41, 1, 0], ![1, -41, 2], ![-428, 86, -40]]]
  hmulB := by decide  
  f := ![![![-411, 23612, -1152], ![404, 58176, 0]], ![![-218, 14019, -684], ![304, 34542, 0]], ![![-241, 16130, -787], ![374, 39744, 0]]]
  g := ![![![1, 0, 0], ![-60, 101, 0], ![-69, 0, 101]], ![![-1, 1, 0], ![23, -41, 2], ![-28, 86, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-74, 20, 1]] ![![101, 0, 0], ![-41, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4141, 101, 0]], ![![-7474, 2020, 101], ![2626, -808, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-41, 1, 0]]], ![![![-74, 20, 1]], ![![26, -8, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-85, 52, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-85, 52, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![18, 52, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-85, 52, 1], ![-376, 1, 105], ![-22427, 4301, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -52, 103]], ![![-1, 0, 1], ![-22, -53, 105], ![-227, 15, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [11, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 102], [0, 1]]
 g := ![![[92, 50], [89, 60], [101, 55], [98], [16], [18, 1]], ![[65, 53], [36, 43], [61, 48], [98], [16], [36, 102]]]
 h' := ![![[18, 102], [51, 87], [22, 36], [33, 63], [94, 43], [8, 4], [0, 1]], ![[0, 1], [72, 16], [52, 67], [34, 40], [44, 60], [80, 99], [18, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [42, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [11, 85, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149, -5054, 1737]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-305, -926, 1737]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-2, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-2, 1, 0]] 
 ![![103, 0, 0], ![101, 1, 0], ![50, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-2, 1, 0], ![1, -2, 2], ![-428, 86, -1]]]
  hmulB := by decide  
  f := ![![![-1782, 3569, -3570], ![103, 183855, 0]], ![![-1747, 3499, -3500], ![104, 180250, 0]], ![![-864, 1732, -1733], ![104, 89250, 0]]]
  g := ![![![1, 0, 0], ![-101, 103, 0], ![-50, 0, 103]], ![![-1, 1, 0], ![1, -2, 2], ![-88, 86, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-85, 52, 1]] ![![103, 0, 0], ![-2, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-206, 103, 0]], ![![-8755, 5356, 103], ![-206, -103, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-2, 1, 0]]], ![![![-85, 52, 1]], ![![-2, -1, 1]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [65, 56, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 52, 71], [28, 54, 36], [0, 1]]
 g := ![![[42, 86, 105], [78, 95, 75], [48, 30], [34, 54, 87], [33, 87], [1]], ![[25, 44, 74, 80], [47, 33, 5, 20], [16, 4], [16, 90, 80, 43], [20, 101], [5, 74, 54, 103]], ![[29, 103, 3, 34], [92, 18, 6, 56], [32, 99], [98, 0, 101, 69], [50, 16], [79, 31, 17, 4]]]
 h' := ![![[52, 52, 71], [66, 73, 31], [68, 12, 17], [37, 5, 43], [47, 98, 27], [42, 51, 80], [0, 1]], ![[28, 54, 36], [17, 80, 9], [78, 98, 58], [72, 31, 2], [20, 75, 70], [6, 76, 23], [52, 52, 71]], ![[0, 1], [44, 61, 67], [58, 104, 32], [76, 71, 62], [70, 41, 10], [18, 87, 4], [28, 54, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 105], []]
 b := ![[], [24, 102, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [65, 56, 27, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78645, 142310, -46010]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-735, 1330, -430]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-20, -6, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-20, -6, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![89, 103, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-20, -6, 1], ![-434, 66, -11], ![2397, -687, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -103, 109]], ![![-1, -1, 1], ![5, 11, -11], ![-27, -63, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [95, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 108], [0, 1]]
 g := ![![[25, 81], [80], [71, 45], [39, 9], [4], [23, 1]], ![[35, 28], [80], [16, 64], [28, 100], [4], [46, 108]]]
 h' := ![![[23, 108], [90, 100], [13, 84], [1, 63], [81, 3], [104, 107], [0, 1]], ![[0, 1], [101, 9], [92, 25], [33, 46], [41, 106], [58, 2], [23, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [36, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [95, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49699, 9975, 1880]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1991, -1685, 1880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![11, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![11, 1, 0]] 
 ![![109, 0, 0], ![11, 1, 0], ![49, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![11, 1, 0], ![1, 11, 2], ![-428, 86, 12]]]
  hmulB := by decide  
  f := ![![![0, 109, 20], ![109, -1090, 0]], ![![1, 11, 2], ![1, -109, 0]], ![![0, 49, 9], ![49, -490, 0]]]
  g := ![![![1, 0, 0], ![-11, 109, 0], ![-49, 0, 109]], ![![0, 1, 0], ![-2, 11, 2], ![-18, 86, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-20, -6, 1]] ![![109, 0, 0], ![11, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![1199, 109, 0]], ![![-2180, -654, 109], ![-654, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![11, 1, 0]]], ![![![-20, -6, 1]], ![![-6, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![4, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![4, 1, 0]] 
 ![![113, 0, 0], ![4, 1, 0], ![49, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![4, 1, 0], ![1, 4, 2], ![-428, 86, 5]]]
  hmulB := by decide  
  f := ![![![-5087, -20397, -10200], ![-339, 576300, 0]], ![![-180, -720, -360], ![1, 20340, 0]], ![![-2207, -8845, -4423], ![-115, 249900, 0]]]
  g := ![![![1, 0, 0], ![-4, 113, 0], ![-49, 0, 113]], ![![0, 1, 0], ![-1, 4, 2], ![-9, 86, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![14, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![14, 1, 0]] 
 ![![113, 0, 0], ![14, 1, 0], ![72, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![14, 1, 0], ![1, 14, 2], ![-428, 86, 15]]]
  hmulB := by decide  
  f := ![![![-7846, -113173, -16170], ![-1921, 913605, 0]], ![![-973, -14012, -2002], ![-225, 113113, 0]], ![![-4996, -72110, -10303], ![-1250, 582120, 0]]]
  g := ![![![1, 0, 0], ![-14, 113, 0], ![-72, 0, 113]], ![![0, 1, 0], ![-3, 14, 2], ![-24, 86, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-19, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-19, 1, 0]] 
 ![![113, 0, 0], ![94, 1, 0], ![46, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-19, 1, 0], ![1, -19, 2], ![-428, 86, -18]]]
  hmulB := by decide  
  f := ![![![2631, -52850, 5564], ![-904, -314366, 0]], ![![2201, -43960, 4628], ![-677, -261482, 0]], ![![1087, -21515, 2265], ![-273, -127972, 0]]]
  g := ![![![1, 0, 0], ![-94, 113, 0], ![-46, 0, 113]], ![![-1, 1, 0], ![15, -19, 2], ![-68, 86, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![4, 1, 0]] ![![113, 0, 0], ![14, 1, 0]]
  ![![113, 0, 0], ![-28, 9, 1]] where
 M := ![![![12769, 0, 0], ![1582, 113, 0]], ![![452, 113, 0], ![57, 18, 2]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-28, 9, 1]] ![![113, 0, 0], ![-19, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2147, 113, 0]], ![![-3164, 1017, 113], ![113, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-19, 1, 0]]], ![![![-28, 9, 1]], ![![1, -1, 0]]]]
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
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-77, 8, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-77, 8, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![50, 8, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-77, 8, 1], ![-420, 9, 17], ![-3595, 517, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -8, 127]], ![![-1, 0, 1], ![-10, -1, 17], ![-35, 3, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [40, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [118, 126], [0, 1]]
 g := ![![[105, 107], [13, 68], [84, 36], [58, 68], [40, 30], [118, 1]], ![[31, 20], [36, 59], [14, 91], [81, 59], [24, 97], [109, 126]]]
 h' := ![![[118, 126], [115, 19], [69, 103], [93, 121], [51, 24], [106, 41], [0, 1]], ![[0, 1], [71, 108], [31, 24], [20, 6], [89, 103], [118, 86], [118, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [103, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [40, 9, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6200, -3072, 759]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250, -72, 759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-17, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-17, 1, 0]] 
 ![![127, 0, 0], ![110, 1, 0], ![110, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-17, 1, 0], ![1, -17, 2], ![-428, 86, -16]]]
  hmulB := by decide  
  f := ![![![6819, -119938, 14112], ![-1778, -896112, 0]], ![![5908, -103875, 12222], ![-1523, -776097, 0]], ![![5901, -103883, 12223], ![-1579, -776160, 0]]]
  g := ![![![1, 0, 0], ![-110, 127, 0], ![-110, 0, 127]], ![![-1, 1, 0], ![13, -17, 2], ![-64, 86, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-77, 8, 1]] ![![127, 0, 0], ![-17, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2159, 127, 0]], ![![-9779, 1016, 127], ![889, -127, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-17, 1, 0]]], ![![![-77, 8, 1]], ![![7, -1, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![5, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![5, 1, 0]] 
 ![![131, 0, 0], ![5, 1, 0], ![119, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![5, 1, 0], ![1, 5, 2], ![-428, 86, 6]]]
  hmulB := by decide  
  f := ![![![-3979, -19948, -7980], ![-262, 522690, 0]], ![![-152, -760, -304], ![1, 19912, 0]], ![![-3616, -18121, -7249], ![-199, 474810, 0]]]
  g := ![![![1, 0, 0], ![-5, 131, 0], ![-119, 0, 131]], ![![0, 1, 0], ![-2, 5, 2], ![-12, 86, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -4, -1]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![41, -4, -1]] 
 ![![131, 0, 0], ![23, 1, 0], ![129, 0, 1]] where
  M :=![![![41, -4, -1], ![424, -45, -9], ![1883, -173, -49]]]
  hmulB := by decide  
  f := ![![![-648, 23, 9]], ![![-143, 5, 2]], ![![-725, 26, 10]]]
  g := ![![![2, -4, -1], ![20, -45, -9], ![93, -173, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-29, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-29, 1, 0]] 
 ![![131, 0, 0], ![102, 1, 0], ![104, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-29, 1, 0], ![1, -29, 2], ![-428, 86, -28]]]
  hmulB := by decide  
  f := ![![![-812, 26097, -1800], ![393, 117900, 0]], ![![-612, 20297, -1400], ![394, 91700, 0]], ![![-638, 20718, -1429], ![342, 93600, 0]]]
  g := ![![![1, 0, 0], ![-102, 131, 0], ![-104, 0, 131]], ![![-1, 1, 0], ![21, -29, 2], ![-48, 86, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![5, 1, 0]] ![![41, -4, -1]]
  ![![131, 0, 0], ![-73, 14, 1]] where
 M := ![![![5371, -524, -131]], ![![629, -65, -14]]]
 hmul := by decide  
 g := ![![![![41, -4, -1], ![0, 0, 0]]], ![![![70, -13, -1], ![117, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-73, 14, 1]] ![![131, 0, 0], ![-29, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3799, 131, 0]], ![![-9563, 1834, 131], ![1703, -393, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-29, 1, 0]]], ![![![-73, 14, 1]], ![![13, -3, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-125, -37, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-125, -37, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![12, 100, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-125, -37, 1], ![-465, -39, -73], ![15665, -3353, -76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -100, 137]], ![![-1, -1, 1], ![3, 53, -73], ![121, 31, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [63, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 136], [0, 1]]
 g := ![![[70, 87], [4], [101], [119, 22], [101], [128], [1]], ![[0, 50], [4], [101], [95, 115], [101], [128], [1]]]
 h' := ![![[111, 136], [54, 118], [13, 135], [38, 85], [27, 61], [15, 85], [74, 111], [0, 1]], ![[0, 1], [0, 19], [65, 2], [20, 52], [85, 76], [134, 52], [65, 26], [111, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [135, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [63, 26, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6040, -2018, 1506]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-176, -1114, 1506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-64, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-64, 1, 0]] 
 ![![137, 0, 0], ![73, 1, 0], ![76, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-64, 1, 0], ![1, -64, 2], ![-428, 86, -63]]]
  hmulB := by decide  
  f := ![![![9631, -960300, 30012], ![-11508, -2055822, 0]], ![![5180, -511636, 15990], ![-6027, -1095315, 0]], ![![5396, -532722, 16649], ![-6270, -1140456, 0]]]
  g := ![![![1, 0, 0], ![-73, 137, 0], ![-76, 0, 137]], ![![-1, 1, 0], ![33, -64, 2], ![-14, 86, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-125, -37, 1]] ![![137, 0, 0], ![-64, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-8768, 137, 0]], ![![-17125, -5069, 137], ![7535, 2329, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-64, 1, 0]]], ![![![-125, -37, 1]], ![![55, 17, -1]]]]
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


lemma PB211I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB211I2 : PrimesBelowBoundCertificateInterval O 79 137 211 where
  m := 11
  g := ![2, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB211I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I101N1, I103N1, I109N1, I113N0, I113N1, I113N2, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [], [I101N1], [I103N1], [], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
