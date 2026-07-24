
import IdealArithmetic.Examples.NF3_1_441484_2.RI3_1_441484_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4142, -378, -533]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![4142, -378, -533]] 
 ![![83, 0, 0], ![0, 83, 0], ![69, 44, 1]] where
  M :=![![![4142, -378, -533], ![67623, 3318, -2026], ![-7203, 6619, 5121]]]
  hmulB := by decide  
  f := ![![![-366284, 19183, -30534]], ![![3996435, -209301, 333149]], ![![1745649, -91423, 145520]]]
  g := ![![![493, 278, -533], ![2499, 1114, -2026], ![-4344, -2635, 5121]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [12, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 82], [0, 1]]
 g := ![![[44, 7], [43, 36], [10], [77], [31, 70], [1]], ![[0, 76], [42, 47], [10], [77], [6, 13], [1]]]
 h' := ![![[53, 82], [65, 16], [24, 77], [12, 33], [43, 34], [71, 53], [0, 1]], ![[0, 1], [0, 67], [38, 6], [18, 50], [19, 49], [58, 30], [53, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [59, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [12, 30, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4284, -1559, -275]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177, 127, -275]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![366284, -19183, 30534]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![366284, -19183, 30534]] 
 ![![83, 0, 0], ![18, 1, 0], ![23, 0, 1]] where
  M :=![![![366284, -19183, 30534], ![-3996435, 209301, -333149], ![5680677, -297508, 473550]]]
  hmulB := by decide  
  f := ![![![-4142, 378, 533]], ![![-1713, 42, 140]], ![![-1061, 25, 86]]]
  g := ![![![112, -19183, 30534], ![-1222, 209301, -333149], ![1737, -297508, 473550]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![4142, -378, -533]] ![![366284, -19183, 30534]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [60, 68, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 62, 87], [17, 26, 2], [0, 1]]
 g := ![![[64, 82, 87], [18, 17], [46, 71], [69, 19, 36], [37, 4, 1], []], ![[51, 76, 17, 50], [44, 20], [18, 8], [51, 6, 14, 22], [7, 35, 37, 72], [35, 4]], ![[74, 43, 22, 1], [78, 42], [70, 64], [81, 28, 25, 22], [3, 67, 3, 34], [31, 4]]]
 h' := ![![[76, 62, 87], [73, 10, 49], [68, 65, 27], [43, 67, 58], [5, 3, 83], [0, 0, 1], [0, 1]], ![[17, 26, 2], [20, 88, 8], [41, 37, 38], [26, 66, 39], [71, 35, 16], [27, 40, 26], [76, 62, 87]], ![[0, 1], [71, 80, 32], [52, 76, 24], [43, 45, 81], [48, 51, 79], [31, 49, 62], [17, 26, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 21], []]
 b := ![[], [84, 30, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [60, 68, 85, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27182914, -585709, 329211]
  a := ![7, 9, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![305426, -6581, 3699]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41875220, -2193086, 3490783]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![41875220, -2193086, 3490783]] 
 ![![97, 0, 0], ![0, 97, 0], ![69, 46, 1]] where
  M :=![![![41875220, -2193086, 3490783], ![-456890265, 23928224, -38087078], ![649440309, -34012441, 54138347]]]
  hmulB := by decide  
  f := ![![![6890, 387, -172]], ![![23349, 9169, 4945]], ![![15273, 4635, 2276]]]
  g := ![![![-2051431, -1678032, 3490783], ![22382661, 18308596, -38087078], ![-31815522, -26024499, 54138347]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [57, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[6, 65], [95], [95], [62], [96], [46, 1]], ![[86, 32], [95], [95], [62], [96], [92, 96]]]
 h' := ![![[46, 96], [18, 68], [96, 17], [46, 17], [66, 16], [94, 22], [0, 1]], ![[0, 1], [42, 29], [5, 80], [52, 80], [26, 81], [39, 75], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [70, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [57, 51, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8454878, -2401991, 96410]
  a := ![-131, -260, -459]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-155744, -70483, 96410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6890, -387, 172]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-6890, -387, 172]] 
 ![![97, 0, 0], ![80, 1, 0], ![17, 0, 1]] where
  M :=![![![-6890, -387, 172], ![-23349, -9169, -4945], ![67983, -1118, -5170]]]
  hmulB := by decide  
  f := ![![![-41875220, 2193086, -3490783]], ![![-29826055, 1562048, -2486346]], ![![-14034217, 734999, -1169914]]]
  g := ![![![218, -387, 172], ![8188, -9169, -4945], ![2529, -1118, -5170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![41875220, -2193086, 3490783]] ![![-6890, -387, 172]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![9, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![9, 1, 0]] 
 ![![101, 0, 0], ![9, 1, 0], ![99, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![9, 1, 0], ![3, 14, 11], ![-129, -2, 5]]]
  hmulB := by decide  
  f := ![![![667, 3149, 2475], ![101, -22725, 0]], ![![51, 279, 220], ![102, -2020, 0]], ![![648, 3086, 2426], ![164, -22275, 0]]]
  g := ![![![1, 0, 0], ![-9, 101, 0], ![-99, 0, 101]], ![![0, 1, 0], ![-12, 14, 11], ![-6, -2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1406, -244, -81]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1406, -244, -81]] 
 ![![101, 0, 0], ![16, 1, 0], ![34, 0, 1]] where
  M :=![![![-1406, -244, -81], ![9717, -2464, -2360], ![22971, 1379, -511]]]
  hmulB := by decide  
  f := ![![![4513544, -236383, 376256]], ![![227431, -11911, 18959]], ![![2212483, -115872, 184436]]]
  g := ![![![52, -244, -81], ![1281, -2464, -2360], ![181, 1379, -511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-26, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-26, 1, 0]] 
 ![![101, 0, 0], ![75, 1, 0], ![70, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-26, 1, 0], ![3, -21, 11], ![-129, -2, -30]]]
  hmulB := by decide  
  f := ![![![17329, -131613, 68970], ![-5757, -633270, 0]], ![![12874, -97713, 51205], ![-4241, -470155, 0]], ![![12012, -91217, 47801], ![-3983, -438900, 0]]]
  g := ![![![1, 0, 0], ![-75, 101, 0], ![-70, 0, 101]], ![![-1, 1, 0], ![8, -21, 11], ![21, -2, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![9, 1, 0]] ![![-1406, -244, -81]]
  ![![101, 0, 0], ![-5, -34, 1]] where
 M := ![![![-142006, -24644, -8181]], ![![-2937, -4660, -3089]]]
 hmul := by decide  
 g := ![![![![-1396, -176, -83], ![202, 0, 0]]], ![![![-27, -32, -31], ![42, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-5, -34, 1]] ![![101, 0, 0], ![-26, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2626, 101, 0]], ![![-505, -3434, 101], ![-101, 707, -404]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-26, 1, 0]]], ![![![-5, -34, 1]], ![![-1, 7, -4]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-29, 3, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-29, 3, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![74, 3, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-29, 3, 1], ![-120, -16, 29], ![-282, -17, -40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -3, 103]], ![![-1, 0, 1], ![-22, -1, 29], ![26, 1, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [35, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 102], [0, 1]]
 g := ![![[92, 28], [12, 34], [29, 25], [38], [8], [76, 1]], ![[57, 75], [21, 69], [75, 78], [38], [8], [49, 102]]]
 h' := ![![[76, 102], [95, 50], [15, 31], [91, 5], [44, 48], [18, 76], [0, 1]], ![[0, 1], [84, 53], [2, 72], [59, 98], [87, 55], [26, 27], [76, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [40, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [35, 27, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4095, -8106, -642]
  a := ![-7, -10, -26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![501, -60, -642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-29, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-29, 1, 0]] 
 ![![103, 0, 0], ![74, 1, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-29, 1, 0], ![3, -24, 11], ![-129, -2, -33]]]
  hmulB := by decide  
  f := ![![![17954, -158408, 72633], ![-6592, -680109, 0]], ![![12925, -113787, 52173], ![-4634, -488529, 0]], ![![6982, -61518, 28207], ![-2526, -264120, 0]]]
  g := ![![![1, 0, 0], ![-74, 103, 0], ![-40, 0, 103]], ![![-1, 1, 0], ![13, -24, 11], ![13, -2, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-29, 3, 1]] ![![103, 0, 0], ![-29, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2987, 103, 0]], ![![-2987, 309, 103], ![721, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-29, 1, 0]]], ![![![-29, 3, 1]], ![![7, -1, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [26, 79, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 43, 30], [18, 63, 77], [0, 1]]
 g := ![![[42, 95, 53], [15, 65, 23], [69, 14], [43, 21, 41], [33, 16], [1]], ![[56, 94, 85, 100], [50, 87, 2, 79], [81, 37], [50, 49, 92, 39], [62, 27], [74, 76, 75, 36]], ![[37, 59, 35, 67], [74, 8, 24, 78], [71, 1], [102, 101, 19, 70], [20, 47], [38, 12, 7, 71]]]
 h' := ![![[85, 43, 30], [38, 104, 38], [82, 61, 39], [59, 77, 96], [32, 15, 24], [81, 28, 103], [0, 1]], ![[18, 63, 77], [19, 84, 57], [86, 23, 7], [65, 14, 12], [20, 8, 36], [54, 44, 53], [85, 43, 30]], ![[0, 1], [23, 26, 12], [74, 23, 61], [23, 16, 106], [0, 84, 47], [29, 35, 58], [18, 63, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 71], []]
 b := ![[], [22, 67, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [26, 79, 4, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1957351, 41730, 76505]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18293, 390, 715]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [83, 14, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 38, 74], [90, 70, 35], [0, 1]]
 g := ![![[52, 54, 106], [0, 102], [78, 86, 82], [23, 40, 20], [101, 80], [1]], ![[79, 31, 98, 9], [27, 48], [55, 52, 36, 94], [105, 87, 55, 29], [67, 3], [54, 31, 52, 71]], ![[39, 92, 68, 35], [35, 21], [50, 79, 17, 20], [31, 52, 68, 105], [55, 31], [45, 97, 88, 38]]]
 h' := ![![[44, 38, 74], [105, 49, 18], [66, 29, 50], [53, 107, 55], [32, 47, 67], [26, 95, 25], [0, 1]], ![[90, 70, 35], [39, 99, 90], [99, 44, 87], [91, 90, 105], [18, 50, 102], [42, 29, 60], [44, 38, 74]], ![[0, 1], [43, 70, 1], [88, 36, 81], [100, 21, 58], [18, 12, 49], [88, 94, 24], [90, 70, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 28], []]
 b := ![[], [14, 87, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [83, 14, 84, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14020234, -4182112, -2036338]
  a := ![5, 28, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128626, -38368, -18682]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [5, 38, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 54, 93], [14, 58, 20], [0, 1]]
 g := ![![[26, 34, 85], [32, 85], [0, 91], [84, 13], [77, 88, 9], [1]], ![[4, 112, 90, 58], [2, 105], [46, 41], [27, 53], [15, 26, 57, 107], [80, 101, 95, 23]], ![[108, 33, 84, 74], [22, 16], [88, 30], [38, 18], [60, 92, 103, 39], [58, 111, 61, 90]]]
 h' := ![![[96, 54, 93], [67, 63, 57], [1, 61, 57], [1, 32, 59], [67, 49, 37], [108, 75, 110], [0, 1]], ![[14, 58, 20], [26, 10, 12], [107, 15, 52], [87, 23, 70], [83, 12, 36], [111, 107, 21], [96, 54, 93]], ![[0, 1], [55, 40, 44], [74, 37, 4], [47, 58, 97], [24, 52, 40], [81, 44, 95], [14, 58, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 88], []]
 b := ![[], [3, 109, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [5, 38, 3, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8706763, -45426, -136278]
  a := ![-5, -6, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77051, -402, -1206]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![362, 154, 85]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![362, 154, 85]] 
 ![![127, 0, 0], ![0, 127, 0], ![70, 81, 1]] where
  M :=![![![362, 154, 85], ![-10503, 962, 1354], ![-10941, -1243, -169]]]
  hmulB := by decide  
  f := ![![![11972, -627, 998]], ![![-130623, 6841, -10889]], ![![-75250, 3941, -6273]]]
  g := ![![![-44, -53, 85], ![-829, -856, 1354], ![7, 98, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [8, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 126], [0, 1]]
 g := ![![[111, 16], [64, 84], [9, 47], [119, 76], [34, 49], [1, 1]], ![[0, 111], [21, 43], [56, 80], [68, 51], [83, 78], [2, 126]]]
 h' := ![![[1, 126], [123, 4], [55, 46], [64, 89], [109, 87], [119, 120], [0, 1]], ![[0, 1], [0, 123], [101, 81], [26, 38], [69, 40], [112, 7], [1, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [86, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [8, 126, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10453, -4169, 2915]
  a := ![6, 11, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1689, -1892, 2915]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11972, -627, 998]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![11972, -627, 998]] 
 ![![127, 0, 0], ![2, 1, 0], ![126, 0, 1]] where
  M :=![![![11972, -627, 998], ![-130623, 6841, -10889], ![185673, -9724, 15478]]]
  hmulB := by decide  
  f := ![![![362, 154, 85]], ![![-77, 10, 12]], ![![273, 143, 83]]]
  g := ![![![-886, -627, 998], ![9667, 6841, -10889], ![-13741, -9724, 15478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![362, 154, 85]] ![![11972, -627, 998]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![23, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![23, 1, 0]] 
 ![![131, 0, 0], ![23, 1, 0], ![37, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![23, 1, 0], ![3, 28, 11], ![-129, -2, 19]]]
  hmulB := by decide  
  f := ![![![19647, 191482, 75240], ![4978, -896040, 0]], ![![3439, 33593, 13200], ![918, -157200, 0]], ![![5533, 54082, 21251], ![1498, -253080, 0]]]
  g := ![![![1, 0, 0], ![-23, 131, 0], ![-37, 0, 131]], ![![0, 1, 0], ![-8, 28, 11], ![-6, -2, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![24, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![24, 1, 0]] 
 ![![131, 0, 0], ![24, 1, 0], ![68, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![24, 1, 0], ![3, 29, 11], ![-129, -2, 20]]]
  hmulB := by decide  
  f := ![![![8539, 86461, 32802], ![2227, -390642, 0]], ![![1542, 15830, 6006], ![525, -71526, 0]], ![![4420, 44880, 17027], ![1224, -202776, 0]]]
  g := ![![![1, 0, 0], ![-24, 131, 0], ![-68, 0, 131]], ![![0, 1, 0], ![-11, 29, 11], ![-11, -2, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-48, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-48, 1, 0]] 
 ![![131, 0, 0], ![83, 1, 0], ![27, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-48, 1, 0], ![3, -43, 11], ![-129, -2, -52]]]
  hmulB := by decide  
  f := ![![![4987, -83832, 21450], ![-2358, -255450, 0]], ![![3178, -53094, 13585], ![-1440, -161785, 0]], ![![1059, -17279, 4421], ![-401, -52650, 0]]]
  g := ![![![1, 0, 0], ![-83, 131, 0], ![-27, 0, 131]], ![![-1, 1, 0], ![25, -43, 11], ![11, -2, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![23, 1, 0]] ![![131, 0, 0], ![24, 1, 0]]
  ![![131, 0, 0], ![-21, -31, 1]] where
 M := ![![![17161, 0, 0], ![3144, 131, 0]], ![![3013, 131, 0], ![555, 52, 11]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![23, 1, 0], ![0, 0, 0]], ![![6, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-21, -31, 1]] ![![131, 0, 0], ![-48, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-6288, 131, 0]], ![![-2751, -4061, 131], ![786, 1310, -393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-48, 1, 0]]], ![![![-21, -31, 1]], ![![6, 10, -3]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![19, 31, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![19, 31, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![19, 31, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![19, 31, 1], ![-36, 172, 337], ![-3894, -73, -104]]]
  hmulB := by decide  
  f := ![![![-18, -31, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -31, 137]], ![![0, 0, 1], ![-47, -75, 337], ![-14, 23, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [96, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 136], [0, 1]]
 g := ![![[12, 56], [36], [65], [4, 1], [69], [122], [1]], ![[27, 81], [36], [65], [85, 136], [69], [122], [1]]]
 h' := ![![[81, 136], [108, 78], [106, 6], [27, 32], [30, 1], [107, 84], [41, 81], [0, 1]], ![[0, 1], [124, 59], [44, 131], [16, 105], [111, 136], [61, 53], [26, 56], [81, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [41, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [96, 56, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51139, -14995, -1235]
  a := ![-10, -20, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-202, 170, -1235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-63, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-63, 1, 0]] 
 ![![137, 0, 0], ![74, 1, 0], ![104, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-63, 1, 0], ![3, -58, 11], ![-129, -2, -67]]]
  hmulB := by decide  
  f := ![![![3169, -78286, 14850], ![-1918, -184950, 0]], ![![1747, -42275, 8019], ![-958, -99873, 0]], ![![2419, -59429, 11273], ![-1427, -140400, 0]]]
  g := ![![![1, 0, 0], ![-74, 137, 0], ![-104, 0, 137]], ![![-1, 1, 0], ![23, -58, 11], ![51, -2, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![19, 31, 1]] ![![137, 0, 0], ![-63, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-8631, 137, 0]], ![![2603, 4247, 137], ![-1233, -1781, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-63, 1, 0]]], ![![![19, 31, 1]], ![![-9, -13, 2]]]]
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


lemma PB189I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB189I2 : PrimesBelowBoundCertificateInterval O 79 137 189 where
  m := 11
  g := ![2, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB189I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N1, I101N0, I101N1, I101N2, I103N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [], [], [], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
