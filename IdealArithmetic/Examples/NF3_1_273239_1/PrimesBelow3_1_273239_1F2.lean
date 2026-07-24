
import IdealArithmetic.Examples.NF3_1_273239_1.RI3_1_273239_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, -9, 4]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![36, -9, 4]] 
 ![![83, 0, 0], ![0, 83, 0], ![9, 60, 1]] where
  M :=![![![36, -9, 4], ![404, 65, -75], ![-505, 64, -10]]]
  hmulB := by decide  
  f := ![![![50, 2, 5]], ![![505, 20, 52]], ![![379, 15, 39]]]
  g := ![![![0, -3, 4], ![13, 55, -75], ![-5, 8, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [22, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 82], [0, 1]]
 g := ![![[65, 48], [72, 59], [4], [64], [36, 29], [1]], ![[66, 35], [30, 24], [4], [64], [66, 54], [1]]]
 h' := ![![[64, 82], [76, 31], [46, 68], [36, 2], [38, 75], [61, 64], [0, 1]], ![[0, 1], [68, 52], [82, 15], [81, 81], [24, 8], [7, 19], [64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [58, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [22, 19, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4062, 4006, -849]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![141, 662, -849]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50, 2, 5]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![50, 2, 5]] 
 ![![83, 0, 0], ![81, 1, 0], ![44, 0, 1]] where
  M :=![![![50, 2, 5], ![505, 20, 52], ![707, 27, 72]]]
  hmulB := by decide  
  f := ![![![36, -9, 4]], ![![40, -8, 3]], ![![13, -4, 2]]]
  g := ![![![-4, 2, 5], ![-41, 20, 52], ![-56, 27, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![36, -9, 4]] ![![50, 2, 5]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4699, -4030, 3241]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-4699, -4030, 3241]] 
 ![![89, 0, 0], ![9, 1, 0], ![21, 0, 1]] where
  M :=![![![-4699, -4030, 3241], ![327341, 2487, -24884], ![-79689, 38807, -22397]]]
  hmulB := by decide  
  f := ![![![909972049, 35513577, 92222153]], ![![196676246, 7675705, 19932378]], ![![359671031, 14036920, 36451270]]]
  g := ![![![-410, -4030, 3241], ![9298, 2487, -24884], ![465, 38807, -22397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19775, 828, 797]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-19775, 828, 797]] 
 ![![89, 0, 0], ![25, 1, 0], ![84, 0, 1]] where
  M :=![![![-19775, 828, 797], ![80497, -27103, 13890], ![164125, 2267, -13213]]]
  hmulB := by decide  
  f := ![![![-326623309, -12747163, -33102011]], ![![-129313324, -5046725, -13105406]], ![![-360304770, -14061653, -36515497]]]
  g := ![![![-1207, 828, 797], ![-4592, -27103, 13890], ![13678, 2267, -13213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 0, 1]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-14, 0, 1]] 
 ![![89, 0, 0], ![54, 1, 0], ![75, 0, 1]] where
  M :=![![![-14, 0, 1], ![101, -18, 6], ![101, 7, -12]]]
  hmulB := by decide  
  f := ![![![174, 7, 18]], ![![126, 5, 13]], ![![175, 7, 18]]]
  g := ![![![-1, 0, 1], ![7, -18, 6], ![7, 7, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-4699, -4030, 3241]] ![![-19775, 828, 797]]
  ![![300448940, 112681665, -102545136]] where
 M := ![![![300448940, 112681665, -102545136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![300448940, 112681665, -102545136]] ![![-14, 0, 1]]
  ![![89, 0, 0]] where
 M := ![![![-3182495731, -2746085922, 2207080562]]]
 hmul := by decide  
 g := ![![![![-35758379, -30854898, 24798658]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23380, 1978, 221]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-23380, 1978, 221]] 
 ![![97, 0, 0], ![0, 97, 0], ![43, 5, 1]] where
  M :=![![![-23380, 1978, 221], ![22321, -34154, 23084], ![222099, -6365, -11070]]]
  hmulB := by decide  
  f := ![![![5412520, 211235, 548538]], ![![55402338, 2162193, 5614813]], ![![6046259, 235968, 612765]]]
  g := ![![![-339, 9, 221], ![-10003, -1542, 23084], ![7197, 505, -11070]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [20, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 96], [0, 1]]
 g := ![![[32, 6], [93], [61], [9], [79], [39, 1]], ![[72, 91], [93], [61], [9], [79], [78, 96]]]
 h' := ![![[39, 96], [36, 43], [76, 53], [61, 35], [85, 94], [93, 46], [0, 1]], ![[0, 1], [64, 54], [9, 44], [68, 62], [65, 3], [44, 51], [39, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [18, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [20, 58, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1478, 1778, 569]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237, -11, 569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5412520, -211235, -548538]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-5412520, -211235, -548538]] 
 ![![97, 0, 0], ![36, 1, 0], ![22, 0, 1]] where
  M :=![![![-5412520, -211235, -548538], ![-55402338, -2162193, -5614813], ![-76737073, -2994826, -7777006]]]
  hmulB := by decide  
  f := ![![![23380, -1978, -221]], ![![8447, -382, -320]], ![![3013, -383, 64]]]
  g := ![![![147008, -211235, -548538], ![1504768, -2162193, -5614813], ![2084235, -2994826, -7777006]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-23380, 1978, 221]] ![![-5412520, -211235, -548538]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![412, 11, -37]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![412, 11, -37]] 
 ![![101, 0, 0], ![0, 101, 0], ![38, 27, 1]] where
  M :=![![![412, 11, -37], ![-3737, 505, -101], ![-2626, -303, 404]]]
  hmulB := by decide  
  f := ![![![1717, 67, 174]], ![![17574, 686, 1781]], ![![5585, 218, 566]]]
  g := ![![![18, 10, -37], ![1, 32, -101], ![-178, -111, 404]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [27, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 100], [0, 1]]
 g := ![![[27, 87], [70], [21, 56], [96], [82], [79, 1]], ![[32, 14], [70], [1, 45], [96], [82], [57, 100]]]
 h' := ![![[79, 100], [35, 84], [39, 26], [9, 64], [51, 55], [89, 53], [0, 1]], ![[0, 1], [5, 17], [73, 75], [15, 37], [53, 46], [34, 48], [79, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [8, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2715, -67, 207]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -56, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1717, 67, 174]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1717, 67, 174]] 
 ![![101, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1717, 67, 174], ![17574, 686, 1781], ![24341, 950, 2467]]]
  hmulB := by decide  
  f := ![![![412, 11, -37]], ![![-37, 5, -1]], ![![-26, -3, 4]]]
  g := ![![![17, 67, 174], ![174, 686, 1781], ![241, 950, 2467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![412, 11, -37]] ![![1717, 67, 174]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27804, 5633, -6028]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![27804, 5633, -6028]] 
 ![![103, 0, 0], ![0, 103, 0], ![23, 54, 1]] where
  M :=![![![27804, 5633, -6028], ![-608828, 23751, 25795], ![-39895, -64728, 49546]]]
  hmulB := by decide  
  f := ![![![-27635202, -1078522, -2800721]], ![![-282872821, -11039708, -28668068]], ![![-158277141, -6177099, -16040777]]]
  g := ![![![1616, 3215, -6028], ![-11671, -13293, 25795], ![-11451, -26604, 49546]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [100, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 102], [0, 1]]
 g := ![![[63, 34], [4, 79], [15, 13], [93], [83], [86, 1]], ![[0, 69], [0, 24], [0, 90], [93], [83], [69, 102]]]
 h' := ![![[86, 102], [12, 31], [45, 39], [96, 42], [69, 14], [52, 86], [0, 1]], ![[0, 1], [0, 72], [0, 64], [0, 61], [37, 89], [32, 17], [86, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [15, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [100, 17, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4966, 5748, -1141]
  a := ![1, 11, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![303, 654, -1141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27635202, -1078522, -2800721]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-27635202, -1078522, -2800721]] 
 ![![103, 0, 0], ![18, 1, 0], ![63, 0, 1]] where
  M :=![![![-27635202, -1078522, -2800721], ![-282872821, -11039708, -28668068], ![-391803543, -15290959, -39707776]]]
  hmulB := by decide  
  f := ![![![27804, 5633, -6028]], ![![-1052, 1215, -803]], ![![16619, 2817, -3206]]]
  g := ![![![1633239, -1078522, -2800721], ![16717769, -11039708, -28668068], ![23155569, -15290959, -39707776]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![27804, 5633, -6028]] ![![-27635202, -1078522, -2800721]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [48, 30, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 103, 24], [6, 3, 83], [0, 1]]
 g := ![![[37, 79, 34], [57, 18, 83], [1, 27], [38, 20, 69], [5, 47], [1]], ![[21, 4, 12, 63], [58, 62, 79, 17], [71, 1], [93, 43], [6, 53], [100, 24, 2, 21]], ![[54, 51, 74, 14], [101, 65, 64, 1], [88, 27], [32, 101, 79, 56], [58, 14], [33, 52, 89, 86]]]
 h' := ![![[43, 103, 24], [46, 95, 26], [84, 6, 46], [102, 38, 53], [31, 46, 60], [59, 77, 49], [0, 1]], ![[6, 3, 83], [24, 25, 4], [39, 67, 68], [68, 11, 1], [46, 51], [21, 89, 69], [43, 103, 24]], ![[0, 1], [105, 94, 77], [39, 34, 100], [25, 58, 53], [99, 10, 47], [23, 48, 96], [6, 3, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 88], []]
 b := ![[], [58, 11, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [48, 30, 58, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6991273, 475829, -195703]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65339, 4447, -1829]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, -12, 21]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-175, -12, 21]] 
 ![![109, 0, 0], ![0, 109, 0], ![28, 15, 1]] where
  M :=![![![-175, -12, 21], ![2121, -199, -6], ![909, 195, -205]]]
  hmulB := by decide  
  f := ![![![-385, -15, -39]], ![![-3939, -154, -399]], ![![-691, -27, -70]]]
  g := ![![![-7, -3, 21], ![21, -1, -6], ![61, 30, -205]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [63, 39, 1] where
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
 g := ![![[11, 45], [74], [92, 7], [57, 64], [46], [70, 1]], ![[0, 64], [74], [37, 102], [68, 45], [46], [31, 108]]]
 h' := ![![[70, 108], [59, 63], [90, 40], [6, 94], [38, 101], [59, 41], [0, 1]], ![[0, 1], [0, 46], [56, 69], [46, 15], [23, 8], [95, 68], [70, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [1, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [63, 39, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![367743, 313678, -31023]
  a := ![1, -81, 182]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11343, 7147, -31023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![385, 15, 39]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![385, 15, 39]] 
 ![![109, 0, 0], ![47, 1, 0], ![98, 0, 1]] where
  M :=![![![385, 15, 39], ![3939, 154, 399], ![5454, 213, 553]]]
  hmulB := by decide  
  f := ![![![175, 12, -21]], ![![56, 7, -9]], ![![149, 9, -17]]]
  g := ![![![-38, 15, 39], ![-389, 154, 399], ![-539, 213, 553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-175, -12, 21]] ![![385, 15, 39]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1894, 592, -561]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1894, 592, -561]] 
 ![![113, 0, 0], ![0, 113, 0], ![78, 35, 1]] where
  M :=![![![1894, 592, -561], ![-56661, 1178, 3146], ![3131, -6295, 4324]]]
  hmulB := by decide  
  f := ![![![-220334, -8599, -22330]], ![![-2255330, -88019, -228569]], ![![-878287, -34277, -89011]]]
  g := ![![![404, 179, -561], ![-2673, -964, 3146], ![-2957, -1395, 4324]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [31, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 112], [0, 1]]
 g := ![![[70, 62], [1], [22], [61], [91, 82], [90, 1]], ![[0, 51], [1], [22], [61], [13, 31], [67, 112]]]
 h' := ![![[90, 112], [64, 47], [78, 112], [46, 19], [4, 93], [35, 46], [0, 1]], ![[0, 1], [0, 66], [101, 1], [61, 94], [12, 20], [107, 67], [90, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [63, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [31, 23, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3241, 2296, 43]
  a := ![-1, -7, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 7, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-220334, -8599, -22330]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-220334, -8599, -22330]] 
 ![![113, 0, 0], ![61, 1, 0], ![49, 0, 1]] where
  M :=![![![-220334, -8599, -22330], ![-2255330, -88019, -228569], ![-3123829, -121914, -316588]]]
  hmulB := by decide  
  f := ![![![1894, 592, -561]], ![![521, 330, -275]], ![![849, 201, -205]]]
  g := ![![![12375, -8599, -22330], ![126670, -88019, -228569], ![175449, -121914, -316588]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1894, 592, -561]] ![![-220334, -8599, -22330]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6609201, 257938, 669817]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![6609201, 257938, 669817]] 
 ![![127, 0, 0], ![0, 127, 0], ![120, 107, 1]] where
  M :=![![![6609201, 257938, 669817], ![67651517, 2640243, 6856220], ![93703255, 3656967, 9496463]]]
  hmulB := by decide  
  f := ![![![-2553, -65, 227]], ![![22927, -3136, 647]], ![![17033, -2689, 740]]]
  g := ![![![-580857, -562303, 669817], ![-5945629, -5755711, 6856220], ![-8235215, -7972162, 9496463]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [48, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 126], [0, 1]]
 g := ![![[60, 34], [71, 121], [100, 62], [84, 38], [58, 70], [41, 1]], ![[57, 93], [79, 6], [102, 65], [118, 89], [7, 57], [82, 126]]]
 h' := ![![[41, 126], [21, 65], [26, 116], [32, 69], [10, 66], [64, 109], [0, 1]], ![[0, 1], [19, 62], [83, 11], [67, 58], [49, 61], [88, 18], [41, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [46, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [48, 86, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9441, 8015, 1536]
  a := ![0, -14, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1377, -1231, 1536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2553, 65, -227]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![2553, 65, -227]] 
 ![![127, 0, 0], ![87, 1, 0], ![125, 0, 1]] where
  M :=![![![2553, 65, -227], ![-22927, 3136, -647], ![-16362, -1849, 2489]]]
  hmulB := by decide  
  f := ![![![-6609201, -257938, -669817]], ![![-5060252, -197487, -512837]], ![![-7242940, -282671, -734044]]]
  g := ![![![199, 65, -227], ![-1692, 3136, -647], ![-1312, -1849, 2489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![6609201, 257938, 669817]] ![![2553, 65, -227]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [43, 111, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 114, 39], [29, 16, 92], [0, 1]]
 g := ![![[18, 125, 33], [62, 7, 80], [23, 113], [114, 60], [69, 4], [41, 1], []], ![[37, 76, 37, 52], [77, 96, 128, 123], [69, 43], [122, 102], [104, 100], [54, 125], [120, 80]], ![[88, 42, 55, 42], [107, 45, 45, 116], [18, 46], [32, 61], [43, 64], [83, 27], [67, 80]]]
 h' := ![![[12, 114, 39], [85, 82, 66], [45, 47, 92], [36, 29, 47], [109, 61, 86], [71, 122, 129], [0, 0, 1], [0, 1]], ![[29, 16, 92], [2, 109, 62], [126, 129, 30], [39, 95, 49], [62, 64, 87], [39, 36, 10], [93, 124, 16], [12, 114, 39]], ![[0, 1], [2, 71, 3], [10, 86, 9], [103, 7, 35], [13, 6, 89], [91, 104, 123], [56, 7, 114], [29, 16, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 27], []]
 b := ![[], [41, 46, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [43, 111, 90, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-277743711, 14473666, -7962180]
  a := ![2, 30, -68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2120181, 110486, -60780]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -2, 3]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-22, -2, 3]] 
 ![![137, 0, 0], ![12, 1, 0], ![92, 0, 1]] where
  M :=![![![-22, -2, 3], ![303, -24, -4], ![101, 29, -28]]]
  hmulB := by decide  
  f := ![![![788, 31, 80]], ![![128, 5, 13]], ![![611, 24, 62]]]
  g := ![![![-2, -2, 3], ![7, -24, -4], ![17, 29, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6611, -258, -670]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-6611, -258, -670]] 
 ![![137, 0, 0], ![14, 1, 0], ![1, 0, 1]] where
  M :=![![![-6611, -258, -670], ![-67670, -2641, -6858], ![-93728, -3658, -9499]]]
  hmulB := by decide  
  f := ![![![-295, -118, 106]], ![![48, -13, 6]], ![![-11, 8, -5]]]
  g := ![![![-17, -258, -670], ![-174, -2641, -6858], ![-241, -3658, -9499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -1, 2]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-18, -1, 2]] 
 ![![137, 0, 0], ![110, 1, 0], ![46, 0, 1]] where
  M :=![![![-18, -1, 2], ![202, -21, 1], ![101, 18, -20]]]
  hmulB := by decide  
  f := ![![![402, 16, 41]], ![![353, 14, 36]], ![![177, 7, 18]]]
  g := ![![![0, -1, 2], ![18, -21, 1], ![-7, 18, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-22, -2, 3]] ![![-6611, -258, -670]]
  ![![-402, -16, -41]] where
 M := ![![![-402, -16, -41]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-402, -16, -41]] ![![-18, -1, 2]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB148I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB148I2 : PrimesBelowBoundCertificateInterval O 79 137 148 where
  m := 11
  g := ![2, 3, 2, 2, 2, 1, 2, 2, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB148I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
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
      exact NI89N1
      exact NI89N2
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
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I101N1, I103N1, I109N1, I113N1, I127N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [I103N1], [], [I109N1], [I113N1], [I127N1], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
