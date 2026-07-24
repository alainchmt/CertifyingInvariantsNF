
import IdealArithmetic.Examples.NF3_1_314847_3.RI3_1_314847_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![0, -14, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![0, -14, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 69, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, -14, 1], ![83, 23, -55], ![-1494, -96, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -69, 83]], ![![0, -1, 1], ![1, 46, -55], ![-18, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [41, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 82], [0, 1]]
 g := ![![[4, 81], [47, 12], [69], [23], [10, 4], [1]], ![[0, 2], [71, 71], [69], [23], [18, 79], [1]]]
 h' := ![![[2, 82], [65, 9], [18, 26], [78, 61], [5, 43], [42, 2], [0, 1]], ![[0, 1], [0, 74], [70, 57], [34, 22], [8, 40], [46, 81], [2, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [28, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [41, 81, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1411, 822, 1044]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -858, 1044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-28, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-28, 1, 0]] 
 ![![83, 0, 0], ![55, 1, 0], ![5, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-28, 1, 0], ![2, -29, 4], ![111, 9, -27]]]
  hmulB := by decide  
  f := ![![![2461, -41745, 5760], ![-1245, -119520, 0]], ![![1629, -27656, 3816], ![-829, -79182, 0]], ![![155, -2515, 347], ![-55, -7200, 0]]]
  g := ![![![1, 0, 0], ![-55, 83, 0], ![-5, 0, 83]], ![![-1, 1, 0], ![19, -29, 4], ![-3, 9, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![0, -14, 1]] ![![83, 0, 0], ![-28, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2324, 83, 0]], ![![0, -1162, 83], ![83, 415, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-28, 1, 0]]], ![![![0, -14, 1]], ![![1, 5, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![17, 23, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![17, 23, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![17, 23, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![17, 23, 1], ![157, 3, 93], ![2613, 237, 49]]]
  hmulB := by decide  
  f := ![![![-16, -23, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -23, 89]], ![![0, 0, 1], ![-16, -24, 93], ![20, -10, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [2, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 88], [0, 1]]
 g := ![![[23, 45], [81], [84], [44, 11], [36, 69], [1]], ![[0, 44], [81], [84], [72, 78], [66, 20], [1]]]
 h' := ![![[43, 88], [48, 32], [11, 9], [1, 23], [17, 79], [87, 43], [0, 1]], ![[0, 1], [0, 57], [42, 80], [11, 66], [32, 10], [67, 46], [43, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [8, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [2, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![247947, 129407, 44620]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5737, -10077, 44620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-4, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-4, 1, 0]] 
 ![![89, 0, 0], ![85, 1, 0], ![40, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-4, 1, 0], ![2, -5, 4], ![111, 9, -3]]]
  hmulB := by decide  
  f := ![![![-875, 2199, -1760], ![89, 39160, 0]], ![![-835, 2099, -1680], ![90, 37380, 0]], ![![-392, 988, -791], ![68, 17600, 0]]]
  g := ![![![1, 0, 0], ![-85, 89, 0], ![-40, 0, 89]], ![![-1, 1, 0], ![3, -5, 4], ![-6, 9, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![17, 23, 1]] ![![89, 0, 0], ![-4, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-356, 89, 0]], ![![1513, 2047, 89], ![89, -89, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-4, 1, 0]]], ![![![17, 23, 1]], ![![1, -1, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-39, -12, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-39, -12, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![58, 85, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-39, -12, 1], ![87, -18, -47], ![-1272, -78, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -85, 97]], ![![-1, -1, 1], ![29, 41, -47], ![12, 36, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [6, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 96], [0, 1]]
 g := ![![[84, 81], [11], [61], [47], [22], [78, 1]], ![[0, 16], [11], [61], [47], [22], [59, 96]]]
 h' := ![![[78, 96], [23, 88], [34, 60], [20, 62], [60, 12], [17, 64], [0, 1]], ![[0, 1], [0, 9], [58, 37], [6, 35], [26, 85], [62, 33], [78, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [27, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [6, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1170, 1968, 612]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-378, -516, 612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 1, 0]] 
 ![![97, 0, 0], ![47, 1, 0], ![42, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 1, 0], ![2, 46, 4], ![111, 9, 48]]]
  hmulB := by decide  
  f := ![![![-7743, -247232, -21504], ![-6208, 521472, 0]], ![![-3751, -119753, -10416], ![-3006, 252588, 0]], ![![-3357, -107049, -9311], ![-2679, 225792, 0]]]
  g := ![![![1, 0, 0], ![-47, 97, 0], ![-42, 0, 97]], ![![0, 1, 0], ![-24, 46, 4], ![-24, 9, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-39, -12, 1]] ![![97, 0, 0], ![47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4559, 97, 0]], ![![-3783, -1164, 97], ![-1746, -582, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![47, 1, 0]]], ![![![-39, -12, 1]], ![![-18, -6, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, 1, 0]] 
 ![![101, 0, 0], ![1, 1, 0], ![51, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, 1, 0], ![2, 0, 4], ![111, 9, 2]]]
  hmulB := by decide  
  f := ![![![-101, 0, -204], ![0, 5151, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-51, 0, -103], ![0, 2601, 0]]]
  g := ![![![1, 0, 0], ![-1, 101, 0], ![-51, 0, 101]], ![![0, 1, 0], ![-2, 0, 4], ![0, 9, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![15, 1, 0]] 
 ![![101, 0, 0], ![15, 1, 0], ![49, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![15, 1, 0], ![2, 14, 4], ![111, 9, 16]]]
  hmulB := by decide  
  f := ![![![-2516, -18139, -5184], ![-505, 130896, 0]], ![![-384, -2688, -768], ![1, 19392, 0]], ![![-1219, -8800, -2515], ![-256, 63504, 0]]]
  g := ![![![1, 0, 0], ![-15, 101, 0], ![-49, 0, 101]], ![![0, 1, 0], ![-4, 14, 4], ![-8, 9, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-16, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-16, 1, 0]] 
 ![![101, 0, 0], ![85, 1, 0], ![84, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-16, 1, 0], ![2, -17, 4], ![111, 9, -15]]]
  hmulB := by decide  
  f := ![![![12165, -107309, 25256], ![-2929, -637714, 0]], ![![10243, -90297, 21252], ![-2423, -536613, 0]], ![![10116, -89247, 21005], ![-2445, -530376, 0]]]
  g := ![![![1, 0, 0], ![-85, 101, 0], ![-84, 0, 101]], ![![-1, 1, 0], ![11, -17, 4], ![6, 9, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, 1, 0]] ![![101, 0, 0], ![15, 1, 0]]
  ![![101, 0, 0], ![-21, 29, 1]] where
 M := ![![![10201, 0, 0], ![1515, 101, 0]], ![![101, 101, 0], ![17, 15, 4]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![22, -28, -1], ![101, 0, 0]], ![![1, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-21, 29, 1]] ![![101, 0, 0], ![-16, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1616, 101, 0]], ![![-2121, 2929, 101], ![505, -505, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-16, 1, 0]]], ![![![-21, 29, 1]], ![![5, -5, 1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![29, -30, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![29, -30, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![29, 73, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![29, -30, 1], ![51, 68, -119], ![-3270, -240, 8]]]
  hmulB := by decide  
  f := ![![![-28, 30, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -73, 103]], ![![0, -1, 1], ![34, 85, -119], ![-34, -8, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [98, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 102], [0, 1]]
 g := ![![[93, 41], [86, 81], [25, 50], [83], [59], [53, 1]], ![[0, 62], [53, 22], [100, 53], [83], [59], [3, 102]]]
 h' := ![![[53, 102], [18, 91], [22, 94], [95, 16], [68, 17], [59, 33], [0, 1]], ![[0, 1], [0, 12], [60, 9], [16, 87], [42, 86], [57, 70], [53, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [29, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [98, 50, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![787, 1015, 52]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -27, 52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![16, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![16, 1, 0]] 
 ![![103, 0, 0], ![16, 1, 0], ![95, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![16, 1, 0], ![2, 15, 4], ![111, 9, 17]]]
  hmulB := by decide  
  f := ![![![-5723, -44358, -11832], ![-1236, 304674, 0]], ![![-902, -6884, -1836], ![-102, 47277, 0]], ![![-5267, -40912, -10913], ![-1214, 281010, 0]]]
  g := ![![![1, 0, 0], ![-16, 103, 0], ![-95, 0, 103]], ![![0, 1, 0], ![-6, 15, 4], ![-16, 9, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![29, -30, 1]] ![![103, 0, 0], ![16, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1648, 103, 0]], ![![2987, -3090, 103], ![515, -412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![16, 1, 0]]], ![![![29, -30, 1]], ![![5, -4, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-20, -29, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-20, -29, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![87, 78, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-20, -29, 1], ![53, 18, -115], ![-3159, -231, -40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -78, 107]], ![![-1, -1, 1], ![94, 84, -115], ![3, 27, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [89, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 106], [0, 1]]
 g := ![![[93, 101], [1, 14], [87], [], [12], [69, 1]], ![[0, 6], [4, 93], [87], [], [12], [31, 106]]]
 h' := ![![[69, 106], [18, 23], [68, 11], [0, 27], [54], [65, 71], [0, 1]], ![[0, 1], [0, 84], [78, 96], [44, 80], [54], [42, 36], [69, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [93, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [89, 38, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102805, 54613, 20085]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15370, -14131, 20085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![8, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![8, 1, 0]] 
 ![![107, 0, 0], ![8, 1, 0], ![40, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![8, 1, 0], ![2, 7, 4], ![111, 9, 9]]]
  hmulB := by decide  
  f := ![![![2121, 7501, 4288], ![321, -114704, 0]], ![![152, 559, 320], ![108, -8560, 0]], ![![792, 2804, 1603], ![132, -42880, 0]]]
  g := ![![![1, 0, 0], ![-8, 107, 0], ![-40, 0, 107]], ![![0, 1, 0], ![-2, 7, 4], ![-3, 9, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-20, -29, 1]] ![![107, 0, 0], ![8, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![856, 107, 0]], ![![-2140, -3103, 107], ![-107, -214, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![8, 1, 0]]], ![![![-20, -29, 1]], ![![-1, -2, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2255, 192, 20]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2255, 192, 20]] 
 ![![109, 0, 0], ![0, 109, 0], ![78, 75, 1]] where
  M :=![![![-2255, 192, 20], ![2604, -2267, 788], ![22512, 2328, -1883]]]
  hmulB := by decide  
  f := ![![![22333, 3744, 1804]], ![![207732, 34825, 16780]], ![![163722, 27447, 13225]]]
  g := ![![![-35, -12, 20], ![-540, -563, 788], ![1554, 1317, -1883]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [62, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 108], [0, 1]]
 g := ![![[23, 81], [60], [33, 26], [3, 28], [34], [100, 1]], ![[57, 28], [60], [17, 83], [78, 81], [34], [91, 108]]]
 h' := ![![[100, 108], [66, 9], [25, 96], [32, 74], [23, 79], [13, 19], [0, 1]], ![[0, 1], [94, 100], [33, 13], [20, 35], [75, 30], [60, 90], [100, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [96, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [62, 9, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346, 56, 24]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -16, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22333, 3744, 1804]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![22333, 3744, 1804]] 
 ![![109, 0, 0], ![26, 1, 0], ![56, 0, 1]] where
  M :=![![![22333, 3744, 1804], ![207732, 34825, 16780], ![523824, 87816, 42313]]]
  hmulB := by decide  
  f := ![![![-2255, 192, 20]], ![![-514, 25, 12]], ![![-952, 120, -7]]]
  g := ![![![-1615, 3744, 1804], ![-15022, 34825, 16780], ![-37880, 87816, 42313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2255, 192, 20]] ![![22333, 3744, 1804]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-31, -37, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-31, -37, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![82, 76, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-31, -37, 1], ![37, 15, -147], ![-4047, -303, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -76, 113]], ![![-1, -1, 1], ![107, 99, -147], ![7, 37, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [105, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 112], [0, 1]]
 g := ![![[89, 14], [2], [98], [7], [57, 26], [34, 1]], ![[0, 99], [2], [98], [7], [37, 87], [68, 112]]]
 h' := ![![[34, 112], [5, 63], [92, 62], [72, 95], [4, 81], [46, 34], [0, 1]], ![[0, 1], [0, 50], [53, 51], [25, 18], [46, 32], [72, 79], [34, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [98, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [105, 79, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2093, 2458, 1766]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1263, -1166, 1766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![34, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![34, 1, 0]] 
 ![![113, 0, 0], ![34, 1, 0], ![59, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![34, 1, 0], ![2, 33, 4], ![111, 9, 35]]]
  hmulB := by decide  
  f := ![![![1503, 28703, 3480], ![791, -98310, 0]], ![![454, 8611, 1044], ![227, -29493, 0]], ![![767, 14986, 1817], ![472, -51330, 0]]]
  g := ![![![1, 0, 0], ![-34, 113, 0], ![-59, 0, 113]], ![![0, 1, 0], ![-12, 33, 4], ![-20, 9, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-31, -37, 1]] ![![113, 0, 0], ![34, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![3842, 113, 0]], ![![-3503, -4181, 113], ![-1017, -1243, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![34, 1, 0]]], ![![![-31, -37, 1]], ![![-9, -11, -1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![61, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![61, 1, 0]] 
 ![![127, 0, 0], ![61, 1, 0], ![38, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![61, 1, 0], ![2, 60, 4], ![111, 9, 62]]]
  hmulB := by decide  
  f := ![![![3170, 133479, 8900], ![2667, -282575, 0]], ![![1526, 64070, 4272], ![1271, -135636, 0]], ![![912, 39938, 2663], ![874, -84550, 0]]]
  g := ![![![1, 0, 0], ![-61, 127, 0], ![-38, 0, 127]], ![![0, 1, 0], ![-30, 60, 4], ![-22, 9, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-37, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-37, 1, 0]] 
 ![![127, 0, 0], ![90, 1, 0], ![30, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-37, 1, 0], ![2, -38, 4], ![111, 9, -36]]]
  hmulB := by decide  
  f := ![![![-4052, 87537, -9216], ![1905, 292608, 0]], ![![-2856, 62005, -6528], ![1398, 207264, 0]], ![![-956, 20678, -2177], ![454, 69120, 0]]]
  g := ![![![1, 0, 0], ![-90, 127, 0], ![-30, 0, 127]], ![![-1, 1, 0], ![26, -38, 4], ![3, 9, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-24, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-24, 1, 0]] 
 ![![127, 0, 0], ![103, 1, 0], ![41, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-24, 1, 0], ![2, -25, 4], ![111, 9, -23]]]
  hmulB := by decide  
  f := ![![![-4767, 62889, -10064], ![1397, 319532, 0]], ![![-3863, 50991, -8160], ![1144, 259080, 0]], ![![-1521, 20302, -3249], ![546, 103156, 0]]]
  g := ![![![1, 0, 0], ![-103, 127, 0], ![-41, 0, 127]], ![![-1, 1, 0], ![19, -25, 4], ![1, 9, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![61, 1, 0]] ![![127, 0, 0], ![-37, 1, 0]]
  ![![127, 0, 0], ![-24, -26, 1]] where
 M := ![![![16129, 0, 0], ![-4699, 127, 0]], ![![7747, 127, 0], ![-2255, 23, 4]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![-13, 27, -1], ![127, 0, 0]]], ![![![61, 1, 0], ![0, 0, 0]], ![![-17, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-24, -26, 1]] ![![127, 0, 0], ![-24, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3048, 127, 0]], ![![-3048, -3302, 127], ![635, 635, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-24, 1, 0]]], ![![![-24, -26, 1]], ![![5, 5, -1]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [99, 95, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 71, 44], [119, 59, 87], [0, 1]]
 g := ![![[124, 58, 77], [47, 63, 16], [115, 112], [15, 33], [29, 105], [26, 1], []], ![[115, 45, 32, 61], [5, 62, 19, 13], [25, 121], [87, 12], [44, 21], [10, 75], [123, 102]], ![[19, 51, 97, 70], [50, 68, 96, 32], [60, 28], [103, 121], [118, 44], [67, 63], [80, 102]]]
 h' := ![![[38, 71, 44], [63, 53, 83], [12, 126, 127], [0, 21, 80], [31, 57, 65], [46, 51, 57], [0, 0, 1], [0, 1]], ![[119, 59, 87], [73, 16, 24], [48, 86, 68], [77, 7, 11], [31, 123, 55], [8, 55, 105], [9, 119, 59], [38, 71, 44]], ![[0, 1], [111, 62, 24], [129, 50, 67], [49, 103, 40], [91, 82, 11], [30, 25, 100], [84, 12, 71], [119, 59, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 43], []]
 b := ![[], [9, 106, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [99, 95, 105, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-346626, 0, 3275]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2646, 0, 25]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![24, -53, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![24, -53, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![24, 84, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![24, -53, 1], ![5, 86, -211], ![-5823, -447, -20]]]
  hmulB := by decide  
  f := ![![![-23, 53, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -84, 137]], ![![0, -1, 1], ![37, 130, -211], ![-39, 9, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [107, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 136], [0, 1]]
 g := ![![[110, 105], [135], [130], [16, 37], [50], [7], [1]], ![[0, 32], [135], [130], [49, 100], [50], [7], [1]]]
 h' := ![![[12, 136], [18, 67], [30, 86], [69, 33], [52, 96], [14, 119], [30, 12], [0, 1]], ![[0, 1], [0, 70], [103, 51], [54, 104], [108, 41], [72, 18], [37, 125], [12, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [81, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [107, 125, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10071, 3122, -214]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111, 154, -214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-63, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-63, 1, 0]] 
 ![![137, 0, 0], ![74, 1, 0], ![20, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-63, 1, 0], ![2, -64, 4], ![111, 9, -62]]]
  hmulB := by decide  
  f := ![![![5274, -227171, 14200], ![-3973, -486350, 0]], ![![2827, -122672, 7668], ![-2191, -262629, 0]], ![![792, -33164, 2073], ![-532, -71000, 0]]]
  g := ![![![1, 0, 0], ![-74, 137, 0], ![-20, 0, 137]], ![![-1, 1, 0], ![34, -64, 4], ![5, 9, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![24, -53, 1]] ![![137, 0, 0], ![-63, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-8631, 137, 0]], ![![3288, -7261, 137], ![-1507, 3425, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-63, 1, 0]]], ![![![24, -53, 1]], ![![-11, 25, -2]]]]
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


lemma PB159I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB159I2 : PrimesBelowBoundCertificateInterval O 79 137 159 where
  m := 11
  g := ![2, 2, 2, 3, 2, 2, 2, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB159I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
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
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
