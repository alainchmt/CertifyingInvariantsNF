
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148, 8, -3]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![148, 8, -3]] 
 ![![83, 0, 0], ![0, 83, 0], ![6, 25, 1]] where
  M :=![![![148, 8, -3], ![-1415, -72, 27], ![4766, 215, -91]]]
  hmulB := by decide  
  f := ![![![-9, -1, 0]], ![![1, -10, -3]], ![![-6, -4, -1]]]
  g := ![![![2, 1, -3], ![-19, -9, 27], ![64, 30, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [53, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 82], [0, 1]]
 g := ![![[37, 49], [19, 9], [17], [11], [28, 48], [1]], ![[62, 34], [49, 74], [17], [11], [22, 35], [1]]]
 h' := ![![[31, 82], [72, 7], [71, 80], [15, 10], [10, 54], [30, 31], [0, 1]], ![[0, 1], [40, 76], [61, 3], [76, 73], [24, 29], [78, 52], [31, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [57, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [53, 52, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2688, 1987, 531]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -136, 531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![83, 0, 0], ![9, 1, 0], ![25, 0, 1]] where
  M :=![![![9, 1, 0], ![-1, 10, 3], ![469, 76, 8]]]
  hmulB := by decide  
  f := ![![![-148, -8, 3]], ![![1, 0, 0]], ![![-102, -5, 2]]]
  g := ![![![0, 1, 0], ![-2, 10, 3], ![-5, 76, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![148, 8, -3]] ![![9, 1, 0]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-91, -40, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-91, -40, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![87, 49, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-91, -40, 1], ![509, -55, -121], ![-19098, -2909, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -49, 89]], ![![-2, -1, 1], ![124, 66, -121], ![-240, -47, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [73, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 88], [0, 1]]
 g := ![![[52, 50], [1], [55], [80, 22], [78, 71], [1]], ![[0, 39], [1], [55], [50, 67], [54, 18], [1]]]
 h' := ![![[31, 88], [48, 53], [78, 88], [34, 77], [2, 72], [16, 31], [0, 1]], ![[0, 1], [0, 36], [47, 1], [18, 12], [9, 17], [87, 58], [31, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [80, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [73, 58, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21724, 8384, 5344]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5468, -2848, 5344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 1, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![63, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 1, 0], ![-1, 33, 3], ![469, 76, 31]]]
  hmulB := by decide  
  f := ![![![705, -23232, -2112], ![0, 62656, 0]], ![![253, -8349, -759], ![1, 22517, 0]], ![![471, -16446, -1495], ![78, 44352, 0]]]
  g := ![![![1, 0, 0], ![-32, 89, 0], ![-63, 0, 89]], ![![0, 1, 0], ![-14, 33, 3], ![-44, 76, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-91, -40, 1]] ![![89, 0, 0], ![32, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2848, 89, 0]], ![![-8099, -3560, 89], ![-2403, -1335, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![32, 1, 0]]], ![![![-91, -40, 1]], ![![-27, -15, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-9, 42, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-9, 42, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![88, 42, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-9, 42, 1], ![427, 109, 125], ![19360, 3323, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -42, 97]], ![![-1, 0, 1], ![-109, -53, 125], ![176, 23, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [54, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 96], [0, 1]]
 g := ![![[4, 9], [62], [16], [65], [18], [75, 1]], ![[0, 88], [62], [16], [65], [18], [53, 96]]]
 h' := ![![[75, 96], [31, 94], [88, 16], [46, 4], [89, 68], [24, 42], [0, 1]], ![[0, 1], [0, 3], [27, 81], [55, 93], [48, 29], [70, 55], [75, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [60, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [54, 22, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2500843, 1242395, 347757]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-289709, -137767, 347757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-28, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-28, 1, 0]] 
 ![![97, 0, 0], ![69, 1, 0], ![71, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-28, 1, 0], ![-1, -27, 3], ![469, 76, -29]]]
  hmulB := by decide  
  f := ![![![-1186, -32806, 3645], ![97, -117855, 0]], ![![-835, -23329, 2592], ![98, -83808, 0]], ![![-886, -24012, 2668], ![9, -86265, 0]]]
  g := ![![![1, 0, 0], ![-69, 97, 0], ![-71, 0, 97]], ![![-1, 1, 0], ![17, -27, 3], ![-28, 76, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-9, 42, 1]] ![![97, 0, 0], ![-28, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2716, 97, 0]], ![![-873, 4074, 97], ![679, -1067, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-28, 1, 0]]], ![![![-9, 42, 1]], ![![7, -11, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-37, -48, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-37, -48, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![64, 53, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-37, -48, 1], ![517, -9, -145], ![-22850, -3517, 88]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -53, 101]], ![![-1, -1, 1], ![97, 76, -145], ![-282, -81, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [60, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 100], [0, 1]]
 g := ![![[80, 78], [88], [40, 49], [56], [80], [48, 1]], ![[87, 23], [88], [69, 52], [56], [80], [96, 100]]]
 h' := ![![[48, 100], [43, 49], [24, 54], [93, 94], [25, 37], [49, 22], [0, 1]], ![[0, 1], [72, 52], [91, 47], [60, 7], [84, 64], [95, 79], [48, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [47, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [60, 53, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13901, 9542, 4443]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2953, -2237, 4443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![44, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![44, 1, 0]] 
 ![![101, 0, 0], ![44, 1, 0], ![13, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![44, 1, 0], ![-1, 45, 3], ![469, 76, 43]]]
  hmulB := by decide  
  f := ![![![5209, -234360, -15624], ![0, 526008, 0]], ![![2268, -102060, -6804], ![1, 229068, 0]], ![![633, -30166, -2011], ![86, 67704, 0]]]
  g := ![![![1, 0, 0], ![-44, 101, 0], ![-13, 0, 101]], ![![0, 1, 0], ![-20, 45, 3], ![-34, 76, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-37, -48, 1]] ![![101, 0, 0], ![44, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4444, 101, 0]], ![![-3737, -4848, 101], ![-1111, -2121, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![44, 1, 0]]], ![![![-37, -48, 1]], ![![-11, -21, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![16, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![16, 1, 0]] 
 ![![103, 0, 0], ![16, 1, 0], ![12, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![16, 1, 0], ![-1, 17, 3], ![469, 76, 15]]]
  hmulB := by decide  
  f := ![![![-653, 10845, 1914], ![103, -65714, 0]], ![![-99, 1683, 297], ![1, -10197, 0]], ![![-84, 1263, 223], ![63, -7656, 0]]]
  g := ![![![1, 0, 0], ![-16, 103, 0], ![-12, 0, 103]], ![![0, 1, 0], ![-3, 17, 3], ![-9, 76, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-14, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-14, 1, 0]] 
 ![![103, 0, 0], ![89, 1, 0], ![42, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-14, 1, 0], ![-1, -13, 3], ![469, 76, -15]]]
  hmulB := by decide  
  f := ![![![-491, -6579, 1518], ![103, -52118, 0]], ![![-422, -5682, 1311], ![104, -45011, 0]], ![![-196, -2683, 619], ![73, -21252, 0]]]
  g := ![![![1, 0, 0], ![-89, 103, 0], ![-42, 0, 103]], ![![-1, 1, 0], ![10, -13, 3], ![-55, 76, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-2, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-2, 1, 0]] 
 ![![103, 0, 0], ![101, 1, 0], ![102, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-2, 1, 0], ![-1, -1, 3], ![469, 76, -3]]]
  hmulB := by decide  
  f := ![![![-3465, -3469, 10404], ![103, -357204, 0]], ![![-3397, -3401, 10200], ![104, -350200, 0]], ![![-3432, -3435, 10303], ![69, -353736, 0]]]
  g := ![![![1, 0, 0], ![-101, 103, 0], ![-102, 0, 103]], ![![-1, 1, 0], ![-2, -1, 3], ![-67, 76, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![16, 1, 0]] ![![103, 0, 0], ![-14, 1, 0]]
  ![![103, 0, 0], ![-75, 1, 1]] where
 M := ![![![10609, 0, 0], ![-1442, 103, 0]], ![![1648, 103, 0], ![-225, 3, 3]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![61, 0, -1], ![103, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-75, 1, 1]] ![![103, 0, 0], ![-2, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-206, 103, 0]], ![![-7725, 103, 103], ![618, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-2, 1, 0]]], ![![![-75, 1, 1]], ![![6, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![3, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![3, 1, 0]] 
 ![![107, 0, 0], ![3, 1, 0], ![67, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![3, 1, 0], ![-1, 4, 3], ![469, 76, 2]]]
  hmulB := by decide  
  f := ![![![-3566, 14255, 10692], ![107, -381348, 0]], ![![-99, 396, 297], ![1, -10593, 0]], ![![-2233, 8926, 6695], ![70, -238788, 0]]]
  g := ![![![1, 0, 0], ![-3, 107, 0], ![-67, 0, 107]], ![![0, 1, 0], ![-2, 4, 3], ![1, 76, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![26, 1, 0]] 
 ![![107, 0, 0], ![26, 1, 0], ![51, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![26, 1, 0], ![-1, 27, 3], ![469, 76, 25]]]
  hmulB := by decide  
  f := ![![![-2265, 60479, 6720], ![107, -239680, 0]], ![![-570, 14687, 1632], ![108, -58208, 0]], ![![-1091, 28826, 3203], ![98, -114240, 0]]]
  g := ![![![1, 0, 0], ![-26, 107, 0], ![-51, 0, 107]], ![![0, 1, 0], ![-8, 27, 3], ![-26, 76, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-290, -68, -11]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-290, -68, -11]] 
 ![![107, 0, 0], ![78, 1, 0], ![50, 0, 1]] where
  M :=![![![-290, -68, -11], ![-5091, -1194, -193], ![-28174, -6609, -1069]]]
  hmulB := by decide  
  f := ![![![-849, -7, 10]], ![![-575, -6, 7]], ![![-459, 4, 4]]]
  g := ![![![52, -68, -11], ![913, -1194, -193], ![5054, -6609, -1069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![3, 1, 0]] ![![107, 0, 0], ![26, 1, 0]]
  ![![-849, -7, 10]] where
 M := ![![![11449, 0, 0], ![2782, 107, 0]], ![![321, 107, 0], ![77, 30, 3]]]
 hmul := by decide  
 g := ![![![![-31030, -7276, -1177]], ![![-12631, -2962, -479]]], ![![![-5961, -1398, -226]], ![![-2426, -569, -92]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-849, -7, 10]] ![![-290, -68, -11]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-15, -45, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-15, -45, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![94, 64, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-15, -45, 1], ![514, 16, -136], ![-21443, -3289, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -64, 109]], ![![-1, -1, 1], ![122, 80, -136], ![-289, -93, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [50, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 108], [0, 1]]
 g := ![![[91, 80], [60], [52, 28], [56, 1], [78], [28, 1]], ![[42, 29], [60], [73, 81], [84, 108], [78], [56, 108]]]
 h' := ![![[28, 108], [90, 25], [16, 13], [34, 79], [95, 108], [17, 80], [0, 1]], ![[0, 1], [27, 84], [53, 96], [66, 30], [67, 1], [77, 29], [28, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [65, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [50, 81, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2714, 1929, 444]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-358, -243, 444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![27, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![27, 1, 0]] 
 ![![109, 0, 0], ![27, 1, 0], ![2, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![27, 1, 0], ![-1, 28, 3], ![469, 76, 26]]]
  hmulB := by decide  
  f := ![![![6196, -173460, -18585], ![0, 675255, 0]], ![![1534, -42952, -4602], ![1, 167206, 0]], ![![107, -3183, -341], ![27, 12390, 0]]]
  g := ![![![1, 0, 0], ![-27, 109, 0], ![-2, 0, 109]], ![![0, 1, 0], ![-7, 28, 3], ![-15, 76, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-15, -45, 1]] ![![109, 0, 0], ![27, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![2943, 109, 0]], ![![-1635, -4905, 109], ![109, -1199, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![27, 1, 0]]], ![![![-15, -45, 1]], ![![1, -11, -1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116, 10, -3]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![116, 10, -3]] 
 ![![113, 0, 0], ![53, 1, 0], ![25, 0, 1]] where
  M :=![![![116, 10, -3], ![-1417, -102, 33], ![5704, 367, -125]]]
  hmulB := by decide  
  f := ![![![-639, -149, -24]], ![![-398, -93, -15]], ![![-688, -161, -26]]]
  g := ![![![-3, 10, -3], ![28, -102, 33], ![-94, 367, -125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-33, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-33, 1, 0]] 
 ![![113, 0, 0], ![80, 1, 0], ![62, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-33, 1, 0], ![-1, -32, 3], ![469, 76, -34]]]
  hmulB := by decide  
  f := ![![![-144, -5697, 534], ![113, -20114, 0]], ![![-125, -4032, 378], ![1, -14238, 0]], ![![-72, -3126, 293], ![86, -11036, 0]]]
  g := ![![![1, 0, 0], ![-80, 113, 0], ![-62, 0, 113]], ![![-1, 1, 0], ![21, -32, 3], ![-31, 76, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-20, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-20, 1, 0]] 
 ![![113, 0, 0], ![93, 1, 0], ![99, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-20, 1, 0], ![-1, -19, 3], ![469, 76, -21]]]
  hmulB := by decide  
  f := ![![![-8715, -165985, 26208], ![113, -987168, 0]], ![![-7168, -136592, 21567], ![114, -812357, 0]], ![![-7625, -145421, 22961], ![157, -864864, 0]]]
  g := ![![![1, 0, 0], ![-93, 113, 0], ![-99, 0, 113]], ![![-1, 1, 0], ![13, -19, 3], ![-40, 76, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![116, 10, -3]] ![![113, 0, 0], ![-33, 1, 0]]
  ![![113, 0, 0], ![-56, 7, 1]] where
 M := ![![![13108, 1130, -339], ![-5245, -432, 132]]]
 hmul := by decide  
 g := ![![![![116, 10, -3], ![0, 0, 0]], ![![-37, -5, 1], ![19, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-56, 7, 1]] ![![113, 0, 0], ![-20, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2260, 113, 0]], ![![-6328, 791, 113], ![1582, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-20, 1, 0]]], ![![![-56, 7, 1]], ![![14, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![6, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![6, 1, 0]] 
 ![![127, 0, 0], ![6, 1, 0], ![28, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![6, 1, 0], ![-1, 7, 3], ![469, 76, 5]]]
  hmulB := by decide  
  f := ![![![-959, 6677, 2862], ![127, -121158, 0]], ![![-45, 315, 135], ![1, -5715, 0]], ![![-212, 1472, 631], ![40, -26712, 0]]]
  g := ![![![1, 0, 0], ![-6, 127, 0], ![-28, 0, 127]], ![![0, 1, 0], ![-1, 7, 3], ![-1, 76, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![54, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![54, 1, 0]] 
 ![![127, 0, 0], ![54, 1, 0], ![68, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![54, 1, 0], ![-1, 55, 3], ![469, 76, 53]]]
  hmulB := by decide  
  f := ![![![-4973, 270599, 14760], ![127, -624840, 0]], ![![-2145, 115004, 6273], ![128, -265557, 0]], ![![-2644, 144888, 7903], ![24, -334560, 0]]]
  g := ![![![1, 0, 0], ![-54, 127, 0], ![-68, 0, 127]], ![![0, 1, 0], ![-25, 55, 3], ![-57, 76, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-60, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-60, 1, 0]] 
 ![![127, 0, 0], ![67, 1, 0], ![5, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-60, 1, 0], ![-1, -59, 3], ![469, 76, -61]]]
  hmulB := by decide  
  f := ![![![-303, -21477, 1092], ![127, -46228, 0]], ![![-131, -11329, 576], ![128, -24384, 0]], ![![15, -846, 43], ![62, -1820, 0]]]
  g := ![![![1, 0, 0], ![-67, 127, 0], ![-5, 0, 127]], ![![-1, 1, 0], ![31, -59, 3], ![-34, 76, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![6, 1, 0]] ![![127, 0, 0], ![54, 1, 0]]
  ![![127, 0, 0], ![-104, -22, 1]] where
 M := ![![![16129, 0, 0], ![6858, 127, 0]], ![![762, 127, 0], ![323, 61, 3]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![54, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-104, -22, 1]] ![![127, 0, 0], ![-60, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7620, 127, 0]], ![![-13208, -2794, 127], ![6731, 1270, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-60, 1, 0]]], ![![![-104, -22, 1]], ![![53, 10, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![1, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![1, 1, 0]] 
 ![![131, 0, 0], ![1, 1, 0], ![130, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![1, 1, 0], ![-1, 2, 3], ![469, 76, 0]]]
  hmulB := by decide  
  f := ![![![-44, 87, 132], ![131, -5764, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-43, 87, 131], ![43, -5720, 0]]]
  g := ![![![1, 0, 0], ![-1, 131, 0], ![-130, 0, 131]], ![![0, 1, 0], ![-3, 2, 3], ![3, 76, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![37, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![37, 1, 0]] 
 ![![131, 0, 0], ![37, 1, 0], ![55, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![37, 1, 0], ![-1, 38, 3], ![469, 76, 36]]]
  hmulB := by decide  
  f := ![![![-4201, 158269, 12495], ![131, -545615, 0]], ![![-1213, 44687, 3528], ![132, -154056, 0]], ![![-1757, 66449, 5246], ![31, -229075, 0]]]
  g := ![![![1, 0, 0], ![-37, 131, 0], ![-55, 0, 131]], ![![0, 1, 0], ![-12, 38, 3], ![-33, 76, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-38, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-38, 1, 0]] 
 ![![131, 0, 0], ![93, 1, 0], ![55, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-38, 1, 0], ![-1, -37, 3], ![469, 76, -39]]]
  hmulB := by decide  
  f := ![![![683, 25234, -2046], ![0, 89342, 0]], ![![485, 17908, -1452], ![1, 63404, 0]], ![![303, 10594, -859], ![56, 37510, 0]]]
  g := ![![![1, 0, 0], ![-93, 131, 0], ![-55, 0, 131]], ![![-1, 1, 0], ![25, -37, 3], ![-34, 76, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![1, 1, 0]] ![![131, 0, 0], ![37, 1, 0]]
  ![![131, 0, 0], ![12, 13, 1]] where
 M := ![![![17161, 0, 0], ![4847, 131, 0]], ![![131, 131, 0], ![36, 39, 3]]]
 hmul := by decide  
 g := ![![![![119, -13, -1], ![131, 0, 0]], ![![25, -12, -1], ![131, 0, 0]]], ![![![-11, -12, -1], ![131, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![12, 13, 1]] ![![131, 0, 0], ![-38, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4978, 131, 0]], ![![1572, 1703, 131], ![0, -393, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-38, 1, 0]]], ![![![12, 13, 1]], ![![0, -3, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-16, 37, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-16, 37, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![121, 37, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-16, 37, 1], ![432, 97, 110], ![17015, 2943, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-121, -37, 137]], ![![-1, 0, 1], ![-94, -29, 110], ![103, 15, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [113, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 136], [0, 1]]
 g := ![![[85, 100], [105], [135], [13, 9], [88], [88], [1]], ![[92, 37], [105], [135], [15, 128], [88], [88], [1]]]
 h' := ![![[122, 136], [45, 10], [26, 70], [38, 51], [21, 134], [85, 15], [24, 122], [0, 1]], ![[0, 1], [32, 127], [72, 67], [95, 86], [66, 3], [134, 122], [112, 15], [122, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [23, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [113, 15, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73042, 15578, 2439]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1621, -545, 2439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![27, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![27, 1, 0]] 
 ![![137, 0, 0], ![27, 1, 0], ![113, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![27, 1, 0], ![-1, 28, 3], ![469, 76, 26]]]
  hmulB := by decide  
  f := ![![![-5702, 158927, 17028], ![137, -777612, 0]], ![![-1145, 31303, 3354], ![138, -153166, 0]], ![![-4697, 131086, 14045], ![82, -641388, 0]]]
  g := ![![![1, 0, 0], ![-27, 137, 0], ![-113, 0, 137]], ![![0, 1, 0], ![-8, 28, 3], ![-33, 76, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-16, 37, 1]] ![![137, 0, 0], ![27, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![3699, 137, 0]], ![![-2192, 5069, 137], ![0, 1096, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![27, 1, 0]]], ![![![-16, 37, 1]], ![![0, 8, 1]]]]
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


lemma PB231I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB231I2 : PrimesBelowBoundCertificateInterval O 79 137 231 where
  m := 11
  g := ![2, 2, 2, 2, 3, 3, 2, 3, 3, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB231I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I109N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [I109N1], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
