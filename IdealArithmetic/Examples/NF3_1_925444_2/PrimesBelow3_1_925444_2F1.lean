
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![3, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![-2, 14, 5], ![232, 32, 11]]]
  hmulB := by decide  
  f := ![![![1493, -10954, -3910], ![222, 28934, 0]], ![![482, -3544, -1265], ![75, 9361, 0]], ![![111, -889, -317], ![49, 2346, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-3, 0, 37]], ![![0, 1, 0], ![-5, 14, 5], ![-5, 32, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 1, 0]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0], ![-16, -17, 1]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![444, 37, 0], ![142, 26, 5]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![6, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-16, -17, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-592, -629, 37], ![74, -222, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-16, -17, 1]], ![![2, -6, -2]]]]
 hle2 := by decide  

def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [37, 15, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 37, 30], [15, 3, 11], [0, 1]]
 g := ![![[8, 34, 10], [40, 1], [14, 1], [21, 6, 1], []], ![[9, 2, 39, 38], [26, 31], [], [28, 37, 30, 24], [35, 39]], ![[14, 20, 19, 24], [15, 33], [3, 1], [23, 28, 19, 12], [13, 39]]]
 h' := ![![[32, 37, 30], [29, 29, 25], [19, 24, 40], [2, 37, 40], [0, 0, 1], [0, 1]], ![[15, 3, 11], [4, 3, 2], [33, 37, 20], [22, 26], [16, 31, 3], [32, 37, 30]], ![[0, 1], [9, 9, 14], [20, 21, 22], [34, 19, 1], [31, 10, 37], [15, 3, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 9], []]
 b := ![[], [6, 21, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [37, 15, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2099815, -505817, -137965]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51215, -12337, -3365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, 16, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, 16, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![39, 16, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, 16, 1], ![200, 60, 79], ![3560, 552, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -16, 43]], ![![-1, 0, 1], ![-67, -28, 79], ![71, 8, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [16, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 42], [0, 1]]
 g := ![![[9, 35], [13, 41], [25], [29, 10], [1]], ![[0, 8], [0, 2], [25], [8, 33], [1]]]
 h' := ![![[28, 42], [7, 32], [25, 16], [9, 5], [27, 28], [0, 1]], ![[0, 1], [0, 11], [0, 27], [20, 38], [37, 15], [28, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [17, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [16, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10794, 7314, 4784]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4590, -1610, 4784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![7, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![7, 1, 0]] 
 ![![43, 0, 0], ![7, 1, 0], ![30, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![7, 1, 0], ![-2, 9, 5], ![232, 32, 6]]]
  hmulB := by decide  
  f := ![![![2126, -9660, -5365], ![129, 46139, 0]], ![![341, -1567, -870], ![44, 7482, 0]], ![![1480, -6740, -3743], ![110, 32190, 0]]]
  g := ![![![1, 0, 0], ![-7, 43, 0], ![-30, 0, 43]], ![![0, 1, 0], ![-5, 9, 5], ![-4, 32, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-4, 16, 1]] ![![43, 0, 0], ![7, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![301, 43, 0]], ![![-172, 688, 43], ![172, 172, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![7, 1, 0]]], ![![![-4, 16, 1]], ![![4, 4, 2]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883762633, 207857608, 61919808]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![883762633, 207857608, 61919808]] 
 ![![47, 0, 0], ![0, 47, 0], ![46, 17, 1]] where
  M :=![![![883762633, 207857608, 61919808], ![13949680240, 3280911705, 977368232], ![38811154240, 9128235776, 2719258689]]]
  hmulB := by decide  
  f := ![![![-110921, -2232, 3328]], ![![776560, -8889, -14488]], ![![150542, -4087, -1959]]]
  g := ![![![-41798905, -17974024, 61919808], ![-659771456, -283709537, 977368232], ![-1835632882, -789343871, 2719258689]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 46], [0, 1]]
 g := ![![[30, 32], [6, 6], [28, 3], [2, 4], [1]], ![[0, 15], [18, 41], [34, 44], [10, 43], [1]]]
 h' := ![![[2, 46], [38, 28], [5, 37], [44, 12], [22, 2], [0, 1]], ![[0, 1], [0, 19], [32, 10], [21, 35], [26, 45], [2, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [46, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5866733, 3189241, 1278207]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1126187, -394474, 1278207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![110921, 2232, -3328]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![110921, 2232, -3328]] 
 ![![47, 0, 0], ![10, 1, 0], ![32, 0, 1]] where
  M :=![![![110921, 2232, -3328], ![-776560, 8889, 14488], ![1023680, -61696, -1135]]]
  hmulB := by decide  
  f := ![![![-883762633, -207857608, -61919808]], ![![-484836310, -114031655, -33969496]], ![![-1427479968, -335737856, -100014735]]]
  g := ![![![4151, 2232, -3328], ![-28278, 8889, 14488], ![35680, -61696, -1135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![883762633, 207857608, 61919808]] ![![110921, 2232, -3328]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [28, 6, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 28, 37], [50, 24, 16], [0, 1]]
 g := ![![[33, 15, 44], [34, 13], [30, 48, 10], [14, 40], [1]], ![[25, 25, 23, 43], [5, 11], [10, 35, 37, 36], [8, 4], [0, 49, 5, 38]], ![[23, 22, 51, 46], [19, 49], [41, 30, 10, 29], [27, 46], [45, 37, 22, 15]]]
 h' := ![![[30, 28, 37], [13, 18, 16], [8, 30, 38], [21, 33, 40], [25, 47, 27], [0, 1]], ![[50, 24, 16], [48, 45, 43], [20, 48, 8], [40, 15, 8], [23, 28, 2], [30, 28, 37]], ![[0, 1], [11, 43, 47], [15, 28, 7], [52, 5, 5], [38, 31, 24], [50, 24, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 30], []]
 b := ![[], [4, 9, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [28, 6, 26, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17334445, -5527635, -1629114]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-327065, -104295, -30738]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-37, -3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-37, -3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![22, 56, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-37, -3, 1], ![238, -11, -16], ![-848, -56, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -56, 59]], ![![-1, -1, 1], ![10, 15, -16], ![-14, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [46, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 58], [0, 1]]
 g := ![![[30, 9], [31, 27], [5], [20, 3], [36, 1]], ![[0, 50], [0, 32], [5], [10, 56], [13, 58]]]
 h' := ![![[36, 58], [49, 56], [51, 33], [24, 8], [55, 11], [0, 1]], ![[0, 1], [0, 3], [0, 26], [17, 51], [38, 48], [36, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [55, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [46, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3238, 1897, 705]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-208, -637, 705]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![16, 1, 0]] 
 ![![59, 0, 0], ![16, 1, 0], ![1, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![16, 1, 0], ![-2, 18, 5], ![232, 32, 15]]]
  hmulB := by decide  
  f := ![![![1393, -12963, -3600], ![177, 42480, 0]], ![![374, -3511, -975], ![60, 11505, 0]], ![![19, -220, -61], ![20, 720, 0]]]
  g := ![![![1, 0, 0], ![-16, 59, 0], ![-1, 0, 59]], ![![0, 1, 0], ![-5, 18, 5], ![-5, 32, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-37, -3, 1]] ![![59, 0, 0], ![16, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![944, 59, 0]], ![![-2183, -177, 59], ![-354, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![16, 1, 0]]], ![![![-37, -3, 1]], ![![-6, -1, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, 1, 0]] 
 ![![61, 0, 0], ![26, 1, 0], ![37, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, 1, 0], ![-2, 28, 5], ![232, 32, 25]]]
  hmulB := by decide  
  f := ![![![1301, -19660, -3510], ![244, 42822, 0]], ![![546, -8374, -1495], ![123, 18239, 0]], ![![787, -11925, -2129], ![153, 25974, 0]]]
  g := ![![![1, 0, 0], ![-26, 61, 0], ![-37, 0, 61]], ![![0, 1, 0], ![-15, 28, 5], ![-25, 32, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-16, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-16, 1, 0]] 
 ![![61, 0, 0], ![45, 1, 0], ![28, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-16, 1, 0], ![-2, -14, 5], ![232, 32, -17]]]
  hmulB := by decide  
  f := ![![![-1015, -7451, 2660], ![183, -32452, 0]], ![![-751, -5490, 1960], ![123, -23912, 0]], ![![-468, -3420, 1221], ![76, -14896, 0]]]
  g := ![![![1, 0, 0], ![-45, 61, 0], ![-28, 0, 61]], ![![-1, 1, 0], ![8, -14, 5], ![-12, 32, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-11, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-11, 1, 0]] 
 ![![61, 0, 0], ![50, 1, 0], ![53, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-11, 1, 0], ![-2, -9, 5], ![232, 32, -12]]]
  hmulB := by decide  
  f := ![![![-1011, -4655, 2585], ![122, -31537, 0]], ![![-823, -3809, 2115], ![123, -25803, 0]], ![![-873, -4045, 2246], ![136, -27401, 0]]]
  g := ![![![1, 0, 0], ![-50, 61, 0], ![-53, 0, 61]], ![![-1, 1, 0], ![3, -9, 5], ![-12, 32, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![26, 1, 0]] ![![61, 0, 0], ![-16, 1, 0]]
  ![![61, 0, 0], ![-47, -22, 1]] where
 M := ![![![3721, 0, 0], ![-976, 61, 0]], ![![1586, 61, 0], ![-418, 12, 5]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![31, 23, -1], ![61, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![-3, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-47, -22, 1]] ![![61, 0, 0], ![-11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-671, 61, 0]], ![![-2867, -1342, 61], ![793, 183, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-11, 1, 0]]], ![![![-47, -22, 1]], ![![13, 3, -2]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-32, 14, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-32, 14, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![35, 14, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-32, 14, 1], ![204, 28, 69], ![3096, 488, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -14, 67]], ![![-1, 0, 1], ![-33, -14, 69], ![53, 10, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [4, 8, 1] where
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
 g := ![![[2, 17], [66, 25], [49], [39], [64], [1]], ![[0, 50], [0, 42], [49], [39], [64], [1]]]
 h' := ![![[59, 66], [4, 34], [27, 62], [25, 60], [28, 21], [63, 59], [0, 1]], ![[0, 1], [0, 33], [0, 5], [14, 7], [61, 46], [60, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [11, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [4, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74579, 15440, 4405]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1188, -690, 4405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-2, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-2, 1, 0]] 
 ![![67, 0, 0], ![65, 1, 0], ![13, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-2, 1, 0], ![-2, 0, 5], ![232, 32, -3]]]
  hmulB := by decide  
  f := ![![![-4351, -2, 10890], ![134, -145926, 0]], ![![-4219, -2, 10560], ![135, -141504, 0]], ![![-843, -1, 2113], ![67, -28314, 0]]]
  g := ![![![1, 0, 0], ![-65, 67, 0], ![-13, 0, 67]], ![![-1, 1, 0], ![-1, 0, 5], ![-27, 32, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-32, 14, 1]] ![![67, 0, 0], ![-2, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-134, 67, 0]], ![![-2144, 938, 67], ![268, 0, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-2, 1, 0]]], ![![![-32, 14, 1]], ![![4, 0, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 6, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 6, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![59, 6, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 6, 1], ![220, 32, 29], ![1240, 232, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -6, 71]], ![![-1, 0, 1], ![-21, -2, 29], ![5, 2, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [4, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 70], [0, 1]]
 g := ![![[56, 18], [28, 9], [26, 54], [18], [50], [1]], ![[0, 53], [0, 62], [0, 17], [18], [50], [1]]]
 h' := ![![[60, 70], [30, 35], [38, 68], [59, 57], [29, 35], [67, 60], [0, 1]], ![[0, 1], [0, 36], [0, 3], [0, 14], [70, 36], [46, 11], [60, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [31, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [4, 11, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5972, 3057, 1965]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1717, -123, 1965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, 1, 0]] 
 ![![71, 0, 0], ![42, 1, 0], ![56, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, 1, 0], ![-2, -27, 5], ![232, 32, -30]]]
  hmulB := by decide  
  f := ![![![-1849, -27330, 5060], ![426, -71852, 0]], ![![-1079, -16150, 2990], ![285, -42458, 0]], ![![-1460, -21556, 3991], ![332, -56672, 0]]]
  g := ![![![1, 0, 0], ![-42, 71, 0], ![-56, 0, 71]], ![![-1, 1, 0], ![12, -27, 5], ![8, 32, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-12, 6, 1]] ![![71, 0, 0], ![-29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2059, 71, 0]], ![![-852, 426, 71], ![568, -142, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-29, 1, 0]]], ![![![-12, 6, 1]], ![![8, -2, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [57, 6, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 58, 55], [3, 14, 18], [0, 1]]
 g := ![![[40, 52, 25], [13, 24], [43, 54], [14, 19, 38], [59, 1], []], ![[57, 7, 20, 8], [35, 37], [50, 9], [15, 55, 15, 64], [50, 50], [19, 32]], ![[23, 72, 27, 32], [36, 72], [38, 41], [27, 41, 30, 23], [0, 6], [56, 32]]]
 h' := ![![[56, 58, 55], [59, 62, 68], [56, 63, 30], [5, 26, 28], [68, 27, 44], [0, 0, 1], [0, 1]], ![[3, 14, 18], [55, 5, 55], [58, 15, 16], [34, 68, 70], [5, 54, 57], [9, 32, 14], [56, 58, 55]], ![[0, 1], [27, 6, 23], [20, 68, 27], [19, 52, 48], [38, 65, 45], [29, 41, 58], [3, 14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 21], []]
 b := ![[], [22, 57, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [57, 6, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15566593, 4308460, 1274945]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![213241, 59020, 17465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-49, 9, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-49, 9, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![30, 9, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-49, 9, 1], ![214, 1, 44], ![1936, 328, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -9, 79]], ![![-1, 0, 1], ![-14, -5, 44], ![34, 7, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [46, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 78], [0, 1]]
 g := ![![[61, 67], [33, 22], [27, 18], [67, 44], [22], [1]], ![[0, 12], [0, 57], [0, 61], [1, 35], [22], [1]]]
 h' := ![![[38, 78], [62, 15], [22, 41], [78, 52], [77, 26], [33, 38], [0, 1]], ![[0, 1], [0, 64], [0, 38], [0, 27], [38, 53], [55, 41], [38, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [30, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [46, 41, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35476, 18290, 6860]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2156, -550, 6860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![35, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![35, 1, 0]] 
 ![![79, 0, 0], ![35, 1, 0], ![25, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![35, 1, 0], ![-2, 37, 5], ![232, 32, 34]]]
  hmulB := by decide  
  f := ![![![6966, -139877, -18900], ![1343, 298620, 0]], ![![3068, -61946, -8370], ![633, 132246, 0]], ![![2200, -44265, -5981], ![435, 94500, 0]]]
  g := ![![![1, 0, 0], ![-35, 79, 0], ![-25, 0, 79]], ![![0, 1, 0], ![-18, 37, 5], ![-22, 32, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-49, 9, 1]] ![![79, 0, 0], ![35, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2765, 79, 0]], ![![-3871, 711, 79], ![-1501, 316, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![35, 1, 0]]], ![![![-49, 9, 1]], ![![-19, 4, 1]]]]
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


lemma PB273I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB273I1 : PrimesBelowBoundCertificateInterval O 31 79 273 where
  m := 11
  g := ![3, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB273I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I43N1, I47N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I79N1]
  Il := ![[I37N0, I37N0, I37N0], [], [I43N1], [I47N1], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
