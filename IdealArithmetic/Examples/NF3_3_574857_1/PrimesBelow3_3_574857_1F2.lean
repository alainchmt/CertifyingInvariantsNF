
import IdealArithmetic.Examples.NF3_3_574857_1.RI3_3_574857_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8027, 393, -124]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![8027, 393, -124]] 
 ![![83, 0, 0], ![0, 83, 0], ![35, 39, 1]] where
  M :=![![![8027, 393, -124], ![-25172, -1273, 393], ![79779, 4303, -1273]]]
  hmulB := by decide  
  f := ![![![-850, -401, -41]], ![![-8323, -3925, -401]], ![![-5250, -2476, -253]]]
  g := ![![![149, 63, -124], ![-469, -200, 393], ![1498, 650, -1273]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [61, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 82], [0, 1]]
 g := ![![[49, 49], [11, 11], [59], [70], [38, 1], [1]], ![[0, 34], [0, 72], [59], [70], [37, 82], [1]]]
 h' := ![![[82, 82], [76, 76], [54, 54], [82, 68], [6, 53], [22, 82], [0, 1]], ![[0, 1], [0, 7], [0, 29], [14, 15], [36, 30], [23, 1], [82, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [69, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [61, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![467, 352, 75]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -31, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![850, 401, 41]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![850, 401, 41]] 
 ![![83, 0, 0], ![44, 1, 0], ![56, 0, 1]] where
  M :=![![![850, 401, 41], ![8323, 3925, 401], ![81403, 38398, 3925]]]
  hmulB := by decide  
  f := ![![![-8027, -393, 124]], ![![-3952, -193, 61]], ![![-6377, -317, 99]]]
  g := ![![![-230, 401, 41], ![-2251, 3925, 401], ![-22023, 38398, 3925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![8027, 393, -124]] ![![850, 401, 41]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-318, -14, 5]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-318, -14, 5]] 
 ![![89, 0, 0], ![0, 89, 0], ![61, 15, 1]] where
  M :=![![![-318, -14, 5], ![1015, 57, -14], ![-2842, -35, 57]]]
  hmulB := by decide  
  f := ![![![31, 7, -1]], ![![-203, -44, 7]], ![![3, 1, 0]]]
  g := ![![![-7, -1, 5], ![21, 3, -14], ![-71, -10, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [81, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 88], [0, 1]]
 g := ![![[31, 11], [79], [18], [18, 71], [46, 5], [1]], ![[0, 78], [79], [18], [4, 18], [40, 84], [1]]]
 h' := ![![[70, 88], [77, 79], [54, 41], [55, 14], [12, 31], [8, 70], [0, 1]], ![[0, 1], [0, 10], [76, 48], [56, 75], [46, 58], [13, 19], [70, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [50, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [81, 19, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2373, 893, 730]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-527, -113, 730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -7, 1]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-31, -7, 1]] 
 ![![89, 0, 0], ![74, 1, 0], ![42, 0, 1]] where
  M :=![![![-31, -7, 1], ![203, 44, -7], ![-1421, -322, 44]]]
  hmulB := by decide  
  f := ![![![318, 14, -5]], ![![253, 11, -4]], ![![182, 7, -3]]]
  g := ![![![5, -7, 1], ![-31, 44, -7], ![231, -322, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-318, -14, 5]] ![![-31, -7, 1]]
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
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-146, -34, 5]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-146, -34, 5]] 
 ![![97, 0, 0], ![34, 1, 0], ![8, 0, 1]] where
  M :=![![![-146, -34, 5], ![1015, 229, -34], ![-6902, -1535, 229]]]
  hmulB := by decide  
  f := ![![![251, 111, 11]], ![![111, 50, 5]], ![![253, 118, 12]]]
  g := ![![![10, -34, 5], ![-67, 229, -34], ![448, -1535, 229]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129, 6, -2]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![129, 6, -2]] 
 ![![97, 0, 0], ![71, 1, 0], ![3, 0, 1]] where
  M :=![![![129, 6, -2], ![-406, -21, 6], ![1218, 44, -21]]]
  hmulB := by decide  
  f := ![![![177, 38, -6]], ![![117, 25, -4]], ![![85, 18, -3]]]
  g := ![![![-3, 6, -2], ![11, -21, 6], ![-19, 44, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 29, 3]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![61, 29, 3]] 
 ![![97, 0, 0], ![89, 1, 0], ![33, 0, 1]] where
  M :=![![![61, 29, 3], ![609, 286, 29], ![5887, 2784, 286]]]
  hmulB := by decide  
  f := ![![![-1060, -58, 17]], ![![-937, -51, 15]], ![![-482, -29, 8]]]
  g := ![![![-27, 29, 3], ![-266, 286, 29], ![-2591, 2784, 286]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-146, -34, 5]] ![![129, 6, -2]]
  ![![1060, 58, -17]] where
 M := ![![![1060, 58, -17]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1060, 58, -17]] ![![61, 29, 3]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![871, 48, -14]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![871, 48, -14]] 
 ![![101, 0, 0], ![0, 101, 0], ![46, 11, 1]] where
  M :=![![![871, 48, -14], ![-2842, -179, 48], ![9744, 758, -179]]]
  hmulB := by decide  
  f := ![![![43, 20, 2]], ![![406, 193, 20]], ![![104, 49, 5]]]
  g := ![![![15, 2, -14], ![-50, -7, 48], ![178, 27, -179]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [32, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 100], [0, 1]]
 g := ![![[81, 49], [76], [80, 58], [58], [68], [34, 1]], ![[30, 52], [76], [32, 43], [58], [68], [68, 100]]]
 h' := ![![[34, 100], [5, 94], [66, 50], [14, 19], [70, 82], [23, 13], [0, 1]], ![[0, 1], [70, 7], [49, 51], [54, 82], [30, 19], [61, 88], [34, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [58, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [32, 67, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-566, -8, 137]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -15, 137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -20, -2]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-43, -20, -2]] 
 ![![101, 0, 0], ![90, 1, 0], ![81, 0, 1]] where
  M :=![![![-43, -20, -2], ![-406, -193, -20], ![-4060, -1906, -193]]]
  hmulB := by decide  
  f := ![![![-871, -48, 14]], ![![-748, -41, 12]], ![![-795, -46, 13]]]
  g := ![![![19, -20, -2], ![184, -193, -20], ![1813, -1906, -193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![871, 48, -14]] ![![-43, -20, -2]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [59, 83, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 9, 16], [95, 93, 87], [0, 1]]
 g := ![![[86, 9, 100], [90, 96, 93], [72, 95, 68], [66, 58], [15, 92], [1]], ![[82, 69, 17, 38], [10, 87, 45, 30], [44, 12, 27, 55], [10, 92], [42, 26], [88, 61, 27, 79]], ![[89, 26, 20, 39], [5, 37, 53, 51], [0, 2, 101, 73], [25, 81], [67, 83], [25, 57, 29, 24]]]
 h' := ![![[76, 9, 16], [46, 57, 10], [78, 90, 89], [49, 24, 58], [21, 31, 77], [44, 20, 68], [0, 1]], ![[95, 93, 87], [87, 57, 91], [71, 27, 35], [16, 2, 10], [20, 2, 35], [51, 25, 52], [76, 9, 16]], ![[0, 1], [51, 92, 2], [31, 89, 82], [100, 77, 35], [37, 70, 94], [73, 58, 86], [95, 93, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 24], []]
 b := ![[], [53, 17, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [59, 83, 35, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-747471, -619545, -121849]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7257, -6015, -1183]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [79, 19, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 78, 105], [0, 28, 2], [0, 1]]
 g := ![![[94, 61, 48], [80, 31, 44], [88, 41], [48, 13, 61], [23, 30], [1]], ![[3, 94, 7, 100], [12, 74, 41, 100], [2, 49], [1, 60, 52, 30], [80, 14], [88, 5, 103, 99]], ![[0, 35, 57, 82], [13, 49, 91, 6], [32, 75], [106, 89, 67, 18], [33, 61], [13, 81, 99, 8]]]
 h' := ![![[64, 78, 105], [100, 38, 35], [72, 91, 77], [60, 72, 24], [37, 88, 32], [28, 88, 64], [0, 1]], ![[0, 28, 2], [62, 18, 48], [34, 39, 48], [70, 71, 100], [2, 77, 78], [104, 31, 11], [64, 78, 105]], ![[0, 1], [43, 51, 24], [75, 84, 89], [79, 71, 90], [98, 49, 104], [43, 95, 32], [0, 28, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 31], []]
 b := ![[], [43, 15, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [79, 19, 43, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69550, -32849, -3210]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-650, -307, -30]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [32, 91, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 80, 90], [13, 28, 19], [0, 1]]
 g := ![![[91, 24, 28], [50, 74], [49, 89, 60], [85, 71, 102], [4, 83], [1]], ![[11, 8, 16, 96], [33, 49], [97, 26, 73, 58], [84, 37, 78, 92], [34, 106], [24, 63, 10, 8]], ![[43, 1, 29, 14], [92, 108], [25, 41, 38, 37], [25, 31, 66, 42], [71, 29], [108, 67, 106, 101]]]
 h' := ![![[31, 80, 90], [55, 38, 30], [67, 21, 69], [5, 52, 96], [24, 79, 50], [77, 18, 44], [0, 1]], ![[13, 28, 19], [37, 44, 9], [60, 43, 7], [57, 1, 65], [80, 55, 8], [29, 47, 18], [31, 80, 90]], ![[0, 1], [83, 27, 70], [53, 45, 33], [40, 56, 57], [20, 84, 51], [49, 44, 47], [13, 28, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 83], []]
 b := ![[], [62, 90, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [32, 91, 65, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2826152, 1297209, 128293]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25928, 11901, 1177]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [78, 74, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 102, 69], [68, 10, 44], [0, 1]]
 g := ![![[97, 40, 56], [64, 7], [19, 111], [26, 1], [21, 2, 18], [1]], ![[17, 92, 14, 18], [105, 51], [24, 100], [31, 51], [79, 32, 10, 91], [9, 107, 28, 18]], ![[16, 76, 89, 11], [21, 91], [55, 30], [11, 106], [63, 99, 32, 61], [98, 59, 40, 95]]]
 h' := ![![[5, 102, 69], [2, 79, 13], [19, 37, 81], [91, 112, 87], [57, 80, 112], [35, 39, 73], [0, 1]], ![[68, 10, 44], [18, 19, 44], [33, 67, 86], [53, 43, 10], [95, 60, 86], [101, 107, 31], [5, 102, 69]], ![[0, 1], [108, 15, 56], [86, 9, 59], [46, 71, 16], [0, 86, 28], [106, 80, 9], [68, 10, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 61], []]
 b := ![[], [53, 8, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [78, 74, 40, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56274, 7571, -2712]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![498, 67, -24]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2421, 115, -37]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![2421, 115, -37]] 
 ![![127, 0, 0], ![0, 127, 0], ![65, 93, 1]] where
  M :=![![![2421, 115, -37], ![-7511, -354, 115], ![23345, 1114, -354]]]
  hmulB := by decide  
  f := ![![![-22, -4, 1]], ![![203, 53, -4]], ![![131, 36, -2]]]
  g := ![![![38, 28, -37], ![-118, -87, 115], ![365, 268, -354]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [49, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 126], [0, 1]]
 g := ![![[30, 70], [95, 35], [35, 115], [2, 8], [2, 122], [54, 1]], ![[0, 57], [80, 92], [22, 12], [53, 119], [113, 5], [108, 126]]]
 h' := ![![[54, 126], [44, 18], [63, 17], [29, 49], [29, 32], [21, 73], [0, 1]], ![[0, 1], [0, 109], [92, 110], [8, 78], [106, 95], [26, 54], [54, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [13, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [49, 73, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![861, 1185, 447]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-222, -318, 447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 4, -1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![22, 4, -1]] 
 ![![127, 0, 0], ![34, 1, 0], ![114, 0, 1]] where
  M :=![![![22, 4, -1], ![-203, -53, 4], ![812, 97, -53]]]
  hmulB := by decide  
  f := ![![![-2421, -115, 37]], ![![-589, -28, 9]], ![![-2357, -112, 36]]]
  g := ![![![0, 4, -1], ![9, -53, 4], ![28, 97, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![2421, 115, -37]] ![![22, 4, -1]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11065, 425, -159]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![11065, 425, -159]] 
 ![![131, 0, 0], ![0, 131, 0], ![68, 55, 1]] where
  M :=![![![11065, 425, -159], ![-32277, -860, 425], ![86275, -402, -860]]]
  hmulB := by decide  
  f := ![![![-6950, -3278, -335]], ![![-68005, -32075, -3278]], ![![-37239, -17564, -1795]]]
  g := ![![![167, 70, -159], ![-467, -185, 425], ![1105, 358, -860]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [96, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 130], [0, 1]]
 g := ![![[5, 11], [105, 60], [112], [65], [114], [102], [1]], ![[96, 120], [125, 71], [112], [65], [114], [102], [1]]]
 h' := ![![[44, 130], [7, 50], [50, 86], [86, 80], [13, 14], [79, 101], [35, 44], [0, 1]], ![[0, 1], [111, 81], [35, 45], [69, 51], [105, 117], [69, 30], [6, 87], [44, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [24, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [96, 87, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7846, -3098, 582]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-362, -268, 582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6950, -3278, -335]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-6950, -3278, -335]] 
 ![![131, 0, 0], ![76, 1, 0], ![119, 0, 1]] where
  M :=![![![-6950, -3278, -335], ![-68005, -32075, -3278], ![-665434, -313855, -32075]]]
  hmulB := by decide  
  f := ![![![11065, 425, -159]], ![![6173, 240, -89]], ![![10710, 383, -151]]]
  g := ![![![2153, -3278, -335], ![21067, -32075, -3278], ![206141, -313855, -32075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![11065, 425, -159]] ![![-6950, -3278, -335]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-647, -140, 22]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-647, -140, 22]] 
 ![![137, 0, 0], ![0, 137, 0], ![64, 31, 1]] where
  M :=![![![-647, -140, 22], ![4466, 1003, -140], ![-28420, -6034, 1003]]]
  hmulB := by decide  
  f := ![![![1177, 56, -18]], ![![-3654, -173, 56]], ![![-194, -9, 3]]]
  g := ![![![-15, -6, 22], ![98, 39, -140], ![-676, -271, 1003]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [9, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 136], [0, 1]]
 g := ![![[99, 61], [14], [74], [2, 76], [128], [103], [1]], ![[0, 76], [14], [74], [101, 61], [128], [103], [1]]]
 h' := ![![[68, 136], [114, 91], [69, 98], [119, 99], [109, 58], [113, 26], [128, 68], [0, 1]], ![[0, 1], [0, 46], [20, 39], [1, 38], [80, 79], [100, 111], [94, 69], [68, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [46, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [9, 69, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![669, -42, 171]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -39, 171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1177, -56, 18]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-1177, -56, 18]] 
 ![![137, 0, 0], ![106, 1, 0], ![135, 0, 1]] where
  M :=![![![-1177, -56, 18], ![3654, 173, -56], ![-11368, -546, 173]]]
  hmulB := by decide  
  f := ![![![647, 140, -22]], ![![468, 101, -16]], ![![845, 182, -29]]]
  g := ![![![17, -56, 18], ![-52, 173, -56], ![169, -546, 173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-647, -140, 22]] ![![-1177, -56, 18]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB169I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB169I2 : PrimesBelowBoundCertificateInterval O 79 137 169 where
  m := 11
  g := ![2, 2, 3, 2, 1, 1, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB169I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [], [], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
