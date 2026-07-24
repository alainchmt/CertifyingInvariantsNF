
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 3, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![59, 3, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![59, 3, 1]] where
  M :=![![![59, 3, 1], ![153, 12, 4], ![612, -35, 16]]]
  hmulB := by decide  
  f := ![![![4, -1, 0]], ![![0, 4, -1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-1, 0, 4], ![-4, -1, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [43, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 82], [0, 1]]
 g := ![![[36, 7], [19, 65], [4], [70], [66, 11], [1]], ![[73, 76], [78, 18], [4], [70], [53, 72], [1]]]
 h' := ![![[29, 82], [13, 67], [53, 56], [68, 2], [67, 53], [40, 29], [0, 1]], ![[0, 1], [47, 16], [17, 27], [43, 81], [27, 30], [51, 54], [29, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [39, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [43, 54, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![502, -42, -97]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![75, 3, -97]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![83, 0, 0], ![79, 1, 0], ![67, 0, 1]] where
  M :=![![![-4, 1, 0], ![0, -4, 1], ![153, -47, -3]]]
  hmulB := by decide  
  f := ![![![-59, -3, -1]], ![![-58, -3, -1]], ![![-55, -2, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 1], ![49, -47, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![59, 3, 1]] ![![-4, 1, 0]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [33, 60, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 62, 35], [7, 26, 54], [0, 1]]
 g := ![![[25, 64, 36], [72, 40], [27, 40], [63, 50, 71], [51, 72, 1], []], ![[62, 29, 19, 77], [87, 40], [55, 17], [54, 73, 6, 61], [50, 22, 76, 75], [69, 68]], ![[32, 29, 86, 27], [], [27, 4], [7, 75, 26, 7], [14, 81, 14, 28], [50, 68]]]
 h' := ![![[65, 62, 35], [5, 86, 6], [44, 59, 29], [57, 63, 60], [8, 82, 31], [0, 0, 1], [0, 1]], ![[7, 26, 54], [17, 80, 51], [29, 19, 60], [81, 69, 27], [44, 80, 27], [79, 74, 26], [65, 62, 35]], ![[0, 1], [79, 12, 32], [41, 11], [24, 46, 2], [79, 16, 31], [1, 15, 62], [7, 26, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 4], []]
 b := ![[], [74, 43, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [33, 60, 17, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![625759, -365790, 53400]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7031, -4110, 600]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 82, -12]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-137, 82, -12]] 
 ![![97, 0, 0], ![0, 97, 0], ![68, 74, 1]] where
  M :=![![![-137, 82, -12], ![-1836, 427, 70], ![10710, -5126, 497]]]
  hmulB := by decide  
  f := ![![![5887, 214, 112]], ![![17136, 623, 326]], ![![17714, 644, 337]]]
  g := ![![![7, 10, -12], ![-68, -49, 70], ![-238, -432, 497]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [58, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 96], [0, 1]]
 g := ![![[32, 75], [33], [94], [11], [2], [84, 1]], ![[27, 22], [33], [94], [11], [2], [71, 96]]]
 h' := ![![[84, 96], [20, 47], [73, 79], [53, 26], [77, 37], [75, 14], [0, 1]], ![[0, 1], [88, 50], [16, 18], [6, 71], [81, 60], [87, 83], [84, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [31, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [58, 13, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3169, 85, 68]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -51, 68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5887, 214, 112]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![5887, 214, 112]] 
 ![![97, 0, 0], ![22, 1, 0], ![1, 0, 1]] where
  M :=![![![5887, 214, 112], ![17136, 623, 326], ![49878, 1814, 949]]]
  hmulB := by decide  
  f := ![![![-137, 82, -12]], ![![-50, 23, -2]], ![![109, -52, 5]]]
  g := ![![![11, 214, 112], ![32, 623, 326], ![93, 1814, 949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-137, 82, -12]] ![![5887, 214, 112]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![49, -2, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![49, -2, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![49, 99, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![49, -2, 1], ![153, 2, -1], ![-153, 200, 1]]]
  hmulB := by decide  
  f := ![![![-48, 2, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -99, 101]], ![![0, -1, 1], ![2, 1, -1], ![-2, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [35, 17, 1] where
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
 g := ![![[38, 85], [71], [64, 84], [96], [78], [84, 1]], ![[7, 16], [71], [50, 17], [96], [78], [67, 100]]]
 h' := ![![[84, 100], [61, 61], [83, 77], [60, 36], [17, 55], [90, 52], [0, 1]], ![[0, 1], [34, 40], [87, 24], [54, 65], [92, 46], [14, 49], [84, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [27, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [35, 17, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![512, 1255, -476]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![236, 479, -476]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, 1, 0]] 
 ![![101, 0, 0], ![1, 1, 0], ![100, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, 1, 0], ![0, 1, 1], ![153, -47, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![101, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 101, 0], ![-100, 0, 101]], ![![0, 1, 0], ![-1, 1, 1], ![0, -47, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![49, -2, 1]] ![![101, 0, 0], ![1, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![101, 101, 0]], ![![4949, -202, 101], ![202, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![1, 1, 0]]], ![![![49, -2, 1]], ![![2, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![28, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![28, 1, 0]] 
 ![![103, 0, 0], ![28, 1, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![28, 1, 0], ![0, 28, 1], ![153, -47, 29]]]
  hmulB := by decide  
  f := ![![![1401, 50, 0], ![-5150, 0, 0]], ![![364, 13, 0], ![-1338, 0, 0]], ![![512, 18, 0], ![-1882, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 103, 0], ![-40, 0, 103]], ![![0, 1, 0], ![-8, 28, 1], ![3, -47, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-23, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-23, 1, 0]] 
 ![![103, 0, 0], ![80, 1, 0], ![89, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-23, 1, 0], ![0, -23, 1], ![153, -47, -22]]]
  hmulB := by decide  
  f := ![![![300, -13, 0], ![1339, 0, 0]], ![![254, -11, 0], ![1134, 0, 0]], ![![282, -12, 0], ![1259, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 103, 0], ![-89, 0, 103]], ![![-1, 1, 0], ![17, -23, 1], ![57, -47, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-6, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-6, 1, 0]] 
 ![![103, 0, 0], ![97, 1, 0], ![67, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-6, 1, 0], ![0, -6, 1], ![153, -47, -5]]]
  hmulB := by decide  
  f := ![![![529, -88, 0], ![9064, 0, 0]], ![![499, -83, 0], ![8550, 0, 0]], ![![349, -58, 0], ![5980, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 103, 0], ![-67, 0, 103]], ![![-1, 1, 0], ![5, -6, 1], ![49, -47, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![28, 1, 0]] ![![103, 0, 0], ![-23, 1, 0]]
  ![![103, 0, 0], ![77, 5, 1]] where
 M := ![![![10609, 0, 0], ![-2369, 103, 0]], ![![2884, 103, 0], ![-644, 5, 1]]]
 hmul := by decide  
 g := ![![![![26, -5, -1], ![103, 0, 0]], ![![-23, 1, 0], ![0, 0, 0]]], ![![![-49, -4, -1], ![103, 0, 0]], ![![-7, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![77, 5, 1]] ![![103, 0, 0], ![-6, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-618, 103, 0]], ![![7931, 515, 103], ![-309, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-6, 1, 0]]], ![![![77, 5, 1]], ![![-3, 0, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [90, 40, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 21, 105], [38, 85, 2], [0, 1]]
 g := ![![[85, 100, 44], [82, 97, 29], [39, 101], [24, 102, 4], [72, 11], [1]], ![[78, 83, 77, 37], [26, 8, 14, 4], [64, 36], [30, 77, 30, 101], [55, 3], [55, 18, 51, 99]], ![[31, 47, 38, 94], [58, 12, 95, 82], [77, 75], [89, 3, 77, 84], [6, 19], [97, 26, 44, 8]]]
 h' := ![![[54, 21, 105], [3, 23, 77], [100, 1, 52], [87, 36, 84], [15, 13, 105], [17, 67, 92], [0, 1]], ![[38, 85, 2], [45, 65, 79], [94, 75, 31], [41, 86, 6], [102, 24, 18], [39, 21, 89], [54, 21, 105]], ![[0, 1], [81, 19, 58], [34, 31, 24], [3, 92, 17], [85, 70, 91], [25, 19, 33], [38, 85, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 75], []]
 b := ![[], [3, 17, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [90, 40, 15, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18297, 2782, -3103]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, 26, -29]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [69, 106, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 66, 58], [46, 42, 51], [0, 1]]
 g := ![![[87, 93, 80], [73, 82], [40, 4, 71], [44, 25, 35], [55, 27], [1]], ![[24, 67, 64, 65], [101, 4], [2, 55, 52, 52], [22, 103, 107, 107], [89, 22], [3, 6, 49, 2]], ![[59, 2, 0, 55], [102, 84], [71, 13, 57, 55], [20, 46, 2, 44], [84, 63], [76, 69, 105, 107]]]
 h' := ![![[101, 66, 58], [3, 96, 84], [74, 100, 54], [16, 49, 17], [94, 68, 97], [40, 3, 38], [0, 1]], ![[46, 42, 51], [14, 28, 49], [94, 69, 2], [84, 94, 68], [46, 17, 61], [44, 59, 26], [101, 66, 58]], ![[0, 1], [90, 94, 85], [77, 49, 53], [82, 75, 24], [41, 24, 60], [96, 47, 45], [46, 42, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 61], []]
 b := ![[], [46, 78, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [69, 106, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1264945, -205029, -10791]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11605, -1881, -99]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-23, 12, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-23, 12, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![90, 12, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-23, 12, 1], ![153, -70, 13], ![1989, -458, -57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -12, 113]], ![![-1, 0, 1], ![-9, -2, 13], ![63, 2, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [60, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 112], [0, 1]]
 g := ![![[49, 81], [2], [51], [102], [63, 85], [111, 1]], ![[0, 32], [2], [51], [102], [6, 28], [109, 112]]]
 h' := ![![[111, 112], [95, 104], [21, 51], [97, 27], [62, 21], [7, 57], [0, 1]], ![[0, 1], [0, 9], [32, 62], [43, 86], [20, 92], [6, 56], [111, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [68, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [60, 2, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-706, 388, -43]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 8, -43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-13, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-13, 1, 0]] 
 ![![113, 0, 0], ![100, 1, 0], ![57, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-13, 1, 0], ![0, -13, 1], ![153, -47, -12]]]
  hmulB := by decide  
  f := ![![![1210, -93, 0], ![10509, 0, 0]], ![![1080, -83, 0], ![9380, 0, 0]], ![![626, -48, 0], ![5437, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 113, 0], ![-57, 0, 113]], ![![-1, 1, 0], ![11, -13, 1], ![49, -47, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-23, 12, 1]] ![![113, 0, 0], ![-13, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1469, 113, 0]], ![![-2599, 1356, 113], ![452, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-13, 1, 0]]], ![![![-23, 12, 1]], ![![4, -2, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30013, 1091, 571]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![30013, 1091, 571]] 
 ![![127, 0, 0], ![0, 127, 0], ![45, 104, 1]] where
  M :=![![![30013, 1091, 571], ![87363, 3176, 1662], ![254286, 9249, 4838]]]
  hmulB := by decide  
  f := ![![![-50, 23, -2]], ![![-306, 44, 21]], ![![-243, 34, 17]]]
  g := ![![![34, -459, 571], ![99, -1336, 1662], ![288, -3889, 4838]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [55, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 126], [0, 1]]
 g := ![![[106, 117], [34, 17], [22, 76], [48, 115], [51, 47], [12, 1]], ![[113, 10], [111, 110], [45, 51], [31, 12], [107, 80], [24, 126]]]
 h' := ![![[12, 126], [35, 25], [60, 115], [27, 87], [116, 49], [102, 89], [0, 1]], ![[0, 1], [81, 102], [43, 12], [55, 40], [69, 78], [27, 38], [12, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [60, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [55, 115, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1279, 351, 51]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -39, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, 23, -2]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-50, 23, -2]] 
 ![![127, 0, 0], ![22, 1, 0], ![24, 0, 1]] where
  M :=![![![-50, 23, -2], ![-306, 44, 21], ![3213, -1293, 65]]]
  hmulB := by decide  
  f := ![![![30013, 1091, 571]], ![![5887, 214, 112]], ![![7674, 279, 146]]]
  g := ![![![-4, 23, -2], ![-14, 44, 21], ![237, -1293, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![30013, 1091, 571]] ![![-50, 23, -2]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [88, 130, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 73, 92], [13, 57, 39], [0, 1]]
 g := ![![[108, 41, 16], [9, 61, 21], [84, 77], [33, 75], [4, 12], [72, 1], []], ![[8, 13, 4, 14], [129, 73, 18, 126], [27, 89], [51, 44], [66, 91], [116, 105], [66, 80]], ![[2, 26, 117, 20], [92, 59, 72, 15], [79, 101], [39, 129], [27, 34], [17, 89], [119, 80]]]
 h' := ![![[59, 73, 92], [125, 57, 127], [69, 106, 105], [16, 106, 83], [118, 91, 72], [83, 115, 76], [0, 0, 1], [0, 1]], ![[13, 57, 39], [89, 90, 38], [15, 75, 17], [66, 20, 73], [121, 11, 31], [54, 70, 109], [31, 68, 57], [59, 73, 92]], ![[0, 1], [27, 115, 97], [120, 81, 9], [103, 5, 106], [28, 29, 28], [96, 77, 77], [46, 63, 73], [13, 57, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 17], []]
 b := ![[], [115, 117, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [88, 130, 59, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![499372, -100084, -24104]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3812, -764, -184]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![61, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![61, 1, 0]] 
 ![![137, 0, 0], ![61, 1, 0], ![115, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![61, 1, 0], ![0, 61, 1], ![153, -47, 62]]]
  hmulB := by decide  
  f := ![![![428, 7, 0], ![-959, 0, 0]], ![![122, 2, 0], ![-273, 0, 0]], ![![394, 6, 0], ![-883, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 137, 0], ![-115, 0, 137]], ![![0, 1, 0], ![-28, 61, 1], ![-30, -47, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-34, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-34, 1, 0]] 
 ![![137, 0, 0], ![103, 1, 0], ![77, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-34, 1, 0], ![0, -34, 1], ![153, -47, -33]]]
  hmulB := by decide  
  f := ![![![4591, -135, 0], ![18495, 0, 0]], ![![3469, -102, 0], ![13975, 0, 0]], ![![2627, -77, 0], ![10583, 1, 0]]]
  g := ![![![1, 0, 0], ![-103, 137, 0], ![-77, 0, 137]], ![![-1, 1, 0], ![25, -34, 1], ![55, -47, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-28, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-28, 1, 0]] 
 ![![137, 0, 0], ![109, 1, 0], ![38, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-28, 1, 0], ![0, -28, 1], ![153, -47, -27]]]
  hmulB := by decide  
  f := ![![![2941, -105, 0], ![14385, 0, 0]], ![![2353, -84, 0], ![11509, 0, 0]], ![![846, -30, 0], ![4138, 1, 0]]]
  g := ![![![1, 0, 0], ![-109, 137, 0], ![-38, 0, 137]], ![![-1, 1, 0], ![22, -28, 1], ![46, -47, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![61, 1, 0]] ![![137, 0, 0], ![-34, 1, 0]]
  ![![137, 0, 0], ![-19, 27, 1]] where
 M := ![![![18769, 0, 0], ![-4658, 137, 0]], ![![8357, 137, 0], ![-2074, 27, 1]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![-15, -26, -1], ![137, 0, 0]]], ![![![61, 1, 0], ![0, 0, 0]], ![![4, -27, -1], ![138, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-19, 27, 1]] ![![137, 0, 0], ![-28, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3836, 137, 0]], ![![-2603, 3699, 137], ![685, -822, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-28, 1, 0]]], ![![![-19, 27, 1]], ![![5, -6, 0]]]]
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


lemma PB271I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB271I2 : PrimesBelowBoundCertificateInterval O 79 137 271 where
  m := 11
  g := ![2, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB271I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I97N1, I101N1, I103N0, I103N1, I103N2, I113N1, I127N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [], [], [I113N1], [I127N1], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
