
import IdealArithmetic.Examples.NF3_1_278343_2.RI3_1_278343_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![7, 3, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 3, 1], ![87, -5, 23], ![219, -33, -11]]]
  hmulB := by decide  
  f := ![![![-6, -3, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -3, 37]], ![![0, 0, 1], ![-2, -2, 23], ![8, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[19, 25], [25], [30, 30], [7], [1]], ![[22, 12], [25], [4, 7], [7], [1]]]
 h' := ![![[9, 36], [9, 5], [22, 32], [6, 17], [18, 9], [0, 1]], ![[0, 1], [17, 32], [14, 5], [11, 20], [25, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [24, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [19, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![384, 968, -2440]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![472, 224, -2440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![11, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![2, 15, 8], ![81, -15, 13]]]
  hmulB := by decide  
  f := ![![![-15, -120, -64], ![0, 296, 0]], ![![-6, -45, -24], ![1, 111, 0]], ![![-9, -36, -19], ![12, 88, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-11, 0, 37]], ![![0, 1, 0], ![-8, 15, 8], ![4, -15, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![7, 3, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![259, 111, 37], ![185, 37, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![7, 3, 1]], ![![5, 1, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![30, -19, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![30, -19, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![30, 22, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![30, -19, 1], ![43, -4, -153], ![-1563, 297, 34]]]
  hmulB := by decide  
  f := ![![![-29, 19, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -22, 41]], ![![0, -1, 1], ![113, 82, -153], ![-63, -11, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [23, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40], [0, 1]]
 g := ![![[32, 25], [2], [37], [39, 4], [1]], ![[0, 16], [2], [37], [6, 37], [1]]]
 h' := ![![[2, 40], [31, 5], [35, 17], [5, 23], [18, 2], [0, 1]], ![[0, 1], [0, 36], [28, 24], [10, 18], [22, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [27, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [23, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1839, 972, -828]
  a := ![2, 0, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![561, 468, -828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![7, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![2, -10, 8], ![81, -15, -12]]]
  hmulB := by decide  
  f := ![![![1831, -10122, 8112], ![-738, -41574, 0]], ![![1340, -7397, 5928], ![-532, -30381, 0]], ![![322, -1729, 1385], ![-91, -7098, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-7, 0, 41]], ![![-1, 1, 0], ![6, -10, 8], ![15, -15, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![30, -19, 1]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![1230, -779, 41], ![-287, 205, -164]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-11, 1, 0]]], ![![![30, -19, 1]], ![![-7, 5, -4]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![30, -12, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![30, -12, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![30, 31, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![30, -12, 1], ![57, 3, -97], ![-996, 192, 27]]]
  hmulB := by decide  
  f := ![![![-29, 12, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -31, 43]], ![![0, -1, 1], ![69, 70, -97], ![-42, -15, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [24, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42], [0, 1]]
 g := ![![[38, 9], [28, 9], [10], [4, 38], [1]], ![[0, 34], [33, 34], [10], [6, 5], [1]]]
 h' := ![![[34, 42], [16, 40], [32, 40], [33, 15], [19, 34], [0, 1]], ![[0, 1], [0, 3], [16, 3], [27, 28], [14, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [35, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [24, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-193264, 1603840, -2977100]
  a := ![-129, -64, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2072552, 2183580, -2977100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![11, 1, 0]] 
 ![![43, 0, 0], ![11, 1, 0], ![16, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![11, 1, 0], ![2, 12, 8], ![81, -15, 10]]]
  hmulB := by decide  
  f := ![![![78, 527, 352], ![43, -1892, 0]], ![![11, 131, 88], ![44, -473, 0]], ![![28, 196, 131], ![20, -704, 0]]]
  g := ![![![1, 0, 0], ![-11, 43, 0], ![-16, 0, 43]], ![![0, 1, 0], ![-6, 12, 8], ![2, -15, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![30, -12, 1]] ![![43, 0, 0], ![11, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![473, 43, 0]], ![![1290, -516, 43], ![387, -129, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![11, 1, 0]]], ![![![30, -12, 1]], ![![9, -3, -2]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42649401, 1719200, 2421556]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![42649401, 1719200, 2421556]] 
 ![![47, 0, 0], ![0, 47, 0], ![45, 40, 1]] where
  M :=![![![42649401, 1719200, 2421556], ![199584436, 8045261, 11332044], ![81137856, 3270672, 4606861]]]
  hmulB := by decide  
  f := ![![![2599, -544, -28]], ![![-3356, 2475, -4324]], ![![-1291, 1752, -3631]]]
  g := ![![![-1411077, -2024320, 2421556], ![-6603352, -9473117, 11332044], ![-2684487, -3851144, 4606861]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [1, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[38, 1], [9, 2], [4, 18], [6, 34], [1]], ![[0, 46], [27, 45], [25, 29], [30, 13], [1]]]
 h' := ![![[9, 46], [38, 1], [43, 7], [41, 21], [46, 9], [0, 1]], ![[0, 1], [0, 46], [12, 40], [42, 26], [33, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [1, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2052, 1607, -2969]
  a := ![-3, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2799, 2561, -2969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2599, -544, -28]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2599, -544, -28]] 
 ![![47, 0, 0], ![10, 1, 0], ![10, 0, 1]] where
  M :=![![![2599, -544, -28], ![-3356, 2475, -4324], ![-43392, 7824, 3563]]]
  hmulB := by decide  
  f := ![![![42649401, 1719200, 2421556]], ![![13320818, 536963, 756332]], ![![10800678, 435376, 613243]]]
  g := ![![![177, -544, -28], ![322, 2475, -4324], ![-3346, 7824, 3563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![42649401, 1719200, 2421556]] ![![2599, -544, -28]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [15, 5, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 35, 21], [10, 17, 32], [0, 1]]
 g := ![![[2, 49, 11], [18, 7], [44, 15, 46], [44, 29], [1]], ![[43, 51, 40, 41], [24, 52], [51, 47, 52, 39], [30, 17], [5, 18, 51, 39]], ![[1, 18, 9, 21], [49, 11], [30, 36, 37, 23], [14, 38], [49, 14, 4, 14]]]
 h' := ![![[23, 35, 21], [41, 40, 8], [29, 47, 31], [42, 25, 24], [38, 48, 33], [0, 1]], ![[10, 17, 32], [26, 6, 22], [11, 46, 30], [38, 32, 32], [8, 24, 32], [23, 35, 21]], ![[0, 1], [44, 7, 23], [14, 13, 45], [2, 49, 50], [0, 34, 41], [10, 17, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 35], []]
 b := ![[], [10, 31, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [15, 5, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1256895, 438628, -428240]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23715, 8276, -8080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![21, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![2, 18, 8], ![81, -15, 16]]]
  hmulB := by decide  
  f := ![![![177, 1888, 840], ![118, -6195, 0]], ![![43, 539, 240], ![60, -1770, 0]], ![![63, 672, 299], ![42, -2205, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-21, 0, 59]], ![![0, 1, 0], ![-8, 18, 8], ![0, -15, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-13, 1, 0]] 
 ![![59, 0, 0], ![46, 1, 0], ![25, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-13, 1, 0], ![2, -12, 8], ![81, -15, -14]]]
  hmulB := by decide  
  f := ![![![-22, 215, -144], ![59, 1062, 0]], ![![-14, 167, -112], ![60, 826, 0]], ![![-8, 91, -61], ![31, 450, 0]]]
  g := ![![![1, 0, 0], ![-46, 59, 0], ![-25, 0, 59]], ![![-1, 1, 0], ![6, -12, 8], ![19, -15, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-4, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-4, 1, 0]] 
 ![![59, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-4, 1, 0], ![2, -3, 8], ![81, -15, -5]]]
  hmulB := by decide  
  f := ![![![3065, -4616, 12320], ![-236, -90860, 0]], ![![2855, -4301, 11480], ![-235, -84665, 0]], ![![2233, -3364, 8979], ![-184, -66220, 0]]]
  g := ![![![1, 0, 0], ![-55, 59, 0], ![-43, 0, 59]], ![![-1, 1, 0], ![-3, -3, 8], ![19, -15, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![17, 1, 0]] ![![59, 0, 0], ![-13, 1, 0]]
  ![![59, 0, 0], ![39, 8, 1]] where
 M := ![![![3481, 0, 0], ![-767, 59, 0]], ![![1003, 59, 0], ![-219, 5, 8]]]
 hmul := by decide  
 g := ![![![![20, -8, -1], ![59, 0, 0]], ![![-13, 1, 0], ![0, 0, 0]]], ![![![-22, -7, -1], ![59, 0, 0]], ![![-9, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![39, 8, 1]] ![![59, 0, 0], ![-4, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-236, 59, 0]], ![![2301, 472, 59], ![-59, 0, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-4, 1, 0]]], ![![![39, 8, 1]], ![![-1, 0, 1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 1, 0]] 
 ![![61, 0, 0], ![12, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 1, 0], ![2, 13, 8], ![81, -15, 11]]]
  hmulB := by decide  
  f := ![![![837, 5819, 3584], ![305, -27328, 0]], ![![164, 1143, 704], ![62, -5368, 0]], ![![789, 5438, 3349], ![250, -25536, 0]]]
  g := ![![![1, 0, 0], ![-12, 61, 0], ![-57, 0, 61]], ![![0, 1, 0], ![-10, 13, 8], ![-6, -15, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-24, 1, 0]] 
 ![![61, 0, 0], ![37, 1, 0], ![38, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-24, 1, 0], ![2, -23, 8], ![81, -15, -25]]]
  hmulB := by decide  
  f := ![![![1963, -28063, 9768], ![-1220, -74481, 0]], ![![1193, -17008, 5920], ![-731, -45140, 0]], ![![1226, -17482, 6085], ![-752, -46398, 0]]]
  g := ![![![1, 0, 0], ![-37, 61, 0], ![-38, 0, 61]], ![![-1, 1, 0], ![9, -23, 8], ![26, -15, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![12, 1, 0]] ![![61, 0, 0], ![12, 1, 0]]
  ![![61, 0, 0], ![3, 26, 1]] where
 M := ![![![3721, 0, 0], ![732, 61, 0]], ![![732, 61, 0], ![146, 25, 8]]]
 hmul := by decide  
 g := ![![![![58, -26, -1], ![61, 0, 0]], ![![9, -25, -1], ![61, 0, 0]]], ![![![9, -25, -1], ![61, 0, 0]], ![![2, -3, 0], ![8, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![3, 26, 1]] ![![61, 0, 0], ![-24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1464, 61, 0]], ![![183, 1586, 61], ![61, -610, 183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-24, 1, 0]]], ![![![3, 26, 1]], ![![1, -10, 3]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 26, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 26, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![11, 26, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 26, 1], ![133, 22, 207], ![2082, -378, -30]]]
  hmulB := by decide  
  f := ![![![-10, -26, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -26, 67]], ![![0, 0, 1], ![-32, -80, 207], ![36, 6, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [49, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 66], [0, 1]]
 g := ![![[7, 26], [1, 4], [15], [16], [64], [1]], ![[0, 41], [36, 63], [15], [16], [64], [1]]]
 h' := ![![[59, 66], [18, 19], [42, 65], [24, 22], [2, 4], [18, 59], [0, 1]], ![[0, 1], [0, 48], [58, 2], [49, 45], [37, 63], [15, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [63, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [49, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-658, 205, -139]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 57, -139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-6, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-6, 1, 0]] 
 ![![67, 0, 0], ![61, 1, 0], ![30, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-6, 1, 0], ![2, -5, 8], ![81, -15, -7]]]
  hmulB := by decide  
  f := ![![![-103, 274, -440], ![67, 3685, 0]], ![![-93, 249, -400], ![68, 3350, 0]], ![![-48, 123, -197], ![9, 1650, 0]]]
  g := ![![![1, 0, 0], ![-61, 67, 0], ![-30, 0, 67]], ![![-1, 1, 0], ![1, -5, 8], ![18, -15, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 26, 1]] ![![67, 0, 0], ![-6, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-402, 67, 0]], ![![737, 1742, 67], ![67, -134, 201]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-6, 1, 0]]], ![![![11, 26, 1]], ![![1, -2, 3]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [59, 7, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 21, 59], [24, 49, 12], [0, 1]]
 g := ![![[38, 3, 9], [44, 23, 48], [10, 42, 30], [47, 4], [54, 1], []], ![[53, 53, 20, 42], [51, 33, 43, 7], [30, 65, 35, 22], [52, 20], [38, 58], [30, 2]], ![[65, 15, 13, 43], [35, 62, 21, 30], [54, 44, 30, 8], [32, 30], [6, 15], [6, 2]]]
 h' := ![![[30, 21, 59], [31, 26, 3], [49, 44, 41], [6, 18, 39], [9, 60, 69], [0, 0, 1], [0, 1]], ![[24, 49, 12], [47, 5, 48], [63, 15, 61], [57, 19, 62], [70, 35, 34], [53, 9, 49], [30, 21, 59]], ![[0, 1], [43, 40, 20], [54, 12, 40], [8, 34, 41], [11, 47, 39], [9, 62, 21], [24, 49, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 21], []]
 b := ![[], [37, 31, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [59, 7, 17, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6331070, -1975575, 1658844]
  a := ![5, 3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89170, -27825, 23364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![219697, 8856, 12474]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![219697, 8856, 12474]] 
 ![![73, 0, 0], ![39, 1, 0], ![6, 0, 1]] where
  M :=![![![219697, 8856, 12474], ![1028106, 41443, 58374], ![417960, 16848, 23731]]]
  hmulB := by decide  
  f := ![![![-1319, 216, 162]], ![![-519, 67, 108]], ![![78, 0, -41]]]
  g := ![![![-2747, 8856, 12474], ![-12855, 41443, 58374], ![-5226, 16848, 23731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-27, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-27, 1, 0]] 
 ![![73, 0, 0], ![46, 1, 0], ![22, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-27, 1, 0], ![2, -26, 8], ![81, -15, -28]]]
  hmulB := by decide  
  f := ![![![2323, -36486, 11232], ![-1314, -102492, 0]], ![![1472, -22973, 7072], ![-802, -64532, 0]], ![![706, -10996, 3385], ![-380, -30888, 0]]]
  g := ![![![1, 0, 0], ![-46, 73, 0], ![-22, 0, 73]], ![![-1, 1, 0], ![14, -26, 8], ![19, -15, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-12, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-12, 1, 0]] 
 ![![73, 0, 0], ![61, 1, 0], ![2, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-12, 1, 0], ![2, -11, 8], ![81, -15, -13]]]
  hmulB := by decide  
  f := ![![![-611, 3561, -2592], ![219, 23652, 0]], ![![-515, 2968, -2160], ![147, 19710, 0]], ![![-10, 97, -71], ![47, 648, 0]]]
  g := ![![![1, 0, 0], ![-61, 73, 0], ![-2, 0, 73]], ![![-1, 1, 0], ![9, -11, 8], ![14, -15, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![219697, 8856, 12474]] ![![73, 0, 0], ![-27, 1, 0]]
  ![![73, 0, 0], ![42, 29, 1]] where
 M := ![![![16037881, 646488, 910602], ![-4903713, -197669, -278424]]]
 hmul := by decide  
 g := ![![![![169423, -25857, 11277], ![87381, 0, 0]], ![![-51843, 7878, -3449], ![-26647, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![42, 29, 1]] ![![73, 0, 0], ![-12, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-876, 73, 0]], ![![3066, 2117, 73], ![-365, -292, 219]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-12, 1, 0]]], ![![![42, 29, 1]], ![![-5, -4, 3]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2287, -544, 136]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![2287, -544, 136]] 
 ![![79, 0, 0], ![0, 79, 0], ![72, 75, 1]] where
  M :=![![![2287, -544, 136], ![9928, -297, -4488], ![-47328, 9792, 791]]]
  hmulB := by decide  
  f := ![![![-553311, -22304, -31416]], ![![-2589304, -104375, -147016]], ![![-2975808, -119955, -168961]]]
  g := ![![![-95, -136, 136], ![4216, 4257, -4488], ![-1320, -627, 791]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [22, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 78], [0, 1]]
 g := ![![[36, 18], [24, 22], [66, 46], [0, 1], [4], [1]], ![[0, 61], [59, 57], [53, 33], [77, 78], [4], [1]]]
 h' := ![![[77, 78], [25, 52], [49, 41], [0, 58], [1, 1], [57, 77], [0, 1]], ![[0, 1], [0, 27], [46, 38], [42, 21], [78, 78], [61, 2], [77, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [32, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [22, 2, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-898, 9565, -17895]
  a := ![-10, -5, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16298, 17110, -17895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![553311, 22304, 31416]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![553311, 22304, 31416]] 
 ![![79, 0, 0], ![33, 1, 0], ![18, 0, 1]] where
  M :=![![![553311, 22304, 31416], ![2589304, 104375, 147016], ![1052640, 42432, 59767]]]
  hmulB := by decide  
  f := ![![![-2287, 544, -136]], ![![-1081, 231, 0]], ![![78, 0, -41]]]
  g := ![![![-9471, 22304, 31416], ![-44321, 104375, 147016], ![-18018, 42432, 59767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![2287, -544, 136]] ![![553311, 22304, 31416]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB150I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB150I1 : PrimesBelowBoundCertificateInterval O 31 79 150 where
  m := 11
  g := ![2, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB150I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N1, I59N0, I59N1, I59N2, I61N0, I61N1, I67N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [], [I59N0, I59N1, I59N2], [I61N0, I61N0, I61N1], [I67N1], [], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
