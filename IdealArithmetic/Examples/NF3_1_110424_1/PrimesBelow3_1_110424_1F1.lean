
import IdealArithmetic.Examples.NF3_1_110424_1.RI3_1_110424_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8192547, 701928, 633034]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![8192547, 701928, 633034]] 
 ![![37, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![8192547, 701928, 633034], ![38119828, 3266063, 2945500], ![14124396, 1210162, 1091385]]]
  hmulB := by decide  
  f := ![![![-3745, 1228, -1142]], ![![-1825, 307, 230]], ![![2614, -534, -75]]]
  g := ![![![99795, 701928, 633034], ![464345, 3266063, 2945500], ![172052, 1210162, 1091385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![2, 9, 6], ![58, -10, 5]]]
  hmulB := by decide  
  f := ![![![-878, -4169, -2784], ![-259, 17168, 0]], ![![-167, -782, -522], ![-36, 3219, 0]], ![![-781, -3718, -2483], ![-242, 15312, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-33, 0, 37]], ![![0, 1, 0], ![-7, 9, 6], ![-1, -10, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![17, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![2, -6, 6], ![58, -10, -10]]]
  hmulB := by decide  
  f := ![![![1385, -4405, 4416], ![-407, -27232, 0]], ![![1089, -3448, 3456], ![-295, -21312, 0]], ![![637, -2024, 2029], ![-184, -12512, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-17, 0, 37]], ![![-1, 1, 0], ![2, -6, 6], ![14, -10, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![8192547, 701928, 633034]] ![![37, 0, 0], ![7, 1, 0]]
  ![![37, 0, 0], ![20, 14, 1]] where
 M := ![![![303124239, 25971336, 23422258], ![95467657, 8179559, 7376738]]]
 hmul := by decide  
 g := ![![![![6419287, -539354, 544371], ![3280531, 0, 0]], ![![2021721, -169871, 171447], ![1033199, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![20, 14, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![740, 518, 37], ![-74, -74, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![20, 14, 1]], ![![-2, -2, 2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-3, -19, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-3, -19, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![38, 22, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-3, -19, 1], ![20, -51, -116], ![-1144, 203, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -22, 41]], ![![-1, -1, 1], ![108, 61, -116], ![-52, -9, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[31, 31], [36], [9], [23, 2], [1]], ![[37, 10], [36], [9], [30, 39], [1]]]
 h' := ![![[24, 40], [16, 20], [39, 6], [35, 38], [14, 24], [0, 1]], ![[0, 1], [4, 21], [19, 35], [4, 3], [16, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [40, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![337, -25, -126]
  a := ![-1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125, 67, -126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![15, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![2, -5, 6], ![58, -10, -9]]]
  hmulB := by decide  
  f := ![![![407, -1048, 1260], ![-82, -8610, 0]], ![![342, -869, 1044], ![-40, -7134, 0]], ![![153, -384, 461], ![-6, -3150, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-15, 0, 41]], ![![-1, 1, 0], ![2, -5, 6], ![13, -10, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-3, -19, 1]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![-123, -779, 41], ![41, 82, -123]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-7, 1, 0]]], ![![![-3, -19, 1]], ![![1, 2, -3]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 20, 18]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![233, 20, 18]] 
 ![![43, 0, 0], ![10, 1, 0], ![9, 0, 1]] where
  M :=![![![233, 20, 18], ![1084, 93, 84], ![404, 34, 31]]]
  hmulB := by decide  
  f := ![![![27, -8, 6]], ![![14, -3, 0]], ![![-11, 2, 1]]]
  g := ![![![-3, 20, 18], ![-14, 93, 84], ![-5, 34, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![43, 0, 0], ![38, 1, 0], ![5, 0, 1]] where
  M :=![![![-5, 1, 0], ![2, -3, 6], ![58, -10, -7]]]
  hmulB := by decide  
  f := ![![![-81, -7, -6]], ![![-80, -7, -6]], ![![-13, -1, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 6], ![11, -10, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![233, 20, 18]] ![![-5, 1, 0]]
  ![![-81, -7, -6]] where
 M := ![![![-81, -7, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-81, -7, -6]] ![![-5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, 17, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, 17, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 17, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, 17, 1], ![92, 8, 100], ![944, -157, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -17, 47]], ![![-1, 0, 1], ![-64, -36, 100], ![59, 18, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [7, 45, 1] where
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
 g := ![![[40, 27], [30, 32], [8, 32], [27, 4], [1]], ![[0, 20], [0, 15], [25, 15], [35, 43], [1]]]
 h' := ![![[2, 46], [25, 11], [38, 28], [46, 28], [40, 2], [0, 1]], ![[0, 1], [0, 36], [0, 19], [8, 19], [44, 45], [2, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [43, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [7, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1957, 637, -98]
  a := ![2, 0, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23, 49, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![12, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![2, -4, 6], ![58, -10, -8]]]
  hmulB := by decide  
  f := ![![![307, -623, 936], ![-47, -7332, 0]], ![![273, -544, 816], ![1, -6392, 0]], ![![84, -160, 239], ![32, -1872, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-12, 0, 47]], ![![-1, 1, 0], ![2, -4, 6], ![12, -10, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-16, 17, 1]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![-752, 799, 47], ![188, -94, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-6, 1, 0]]], ![![![-16, 17, 1]], ![![4, -2, 2]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 29, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 9, 17], [12, 43, 36], [0, 1]]
 g := ![![[5, 11, 49], [3, 52], [0, 28, 9], [14, 13], [1]], ![[32, 30, 1, 16], [45, 37], [27, 41, 25, 40], [51, 49], [9, 13, 37, 37]], ![[48, 31, 2, 9], [38, 44], [37, 11, 11, 29], [36, 11], [41, 25, 50, 16]]]
 h' := ![![[3, 9, 17], [23, 29, 46], [0, 48, 30], [13, 44, 3], [43, 24, 15], [0, 1]], ![[12, 43, 36], [27, 21, 33], [0, 22, 39], [14, 37, 29], [43, 11, 46], [3, 9, 17]], ![[0, 1], [27, 3, 27], [6, 36, 37], [7, 25, 21], [46, 18, 45], [12, 43, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 45], []]
 b := ![[], [14, 6, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 29, 38, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-824846208, 221763660, -230753838]
  a := ![-65, -64, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15563136, 4184220, -4353846]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![10, -19, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![10, -19, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![10, 40, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![10, -19, 1], ![20, -38, -116], ![-1144, 203, 39]]]
  hmulB := by decide  
  f := ![![![-9, 19, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -40, 59]], ![![0, -1, 1], ![20, 78, -116], ![-26, -23, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [54, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 58], [0, 1]]
 g := ![![[10, 19], [27, 4], [57], [36, 21], [50, 1]], ![[16, 40], [50, 55], [57], [24, 38], [41, 58]]]
 h' := ![![[50, 58], [17, 14], [58, 57], [3, 36], [14, 27], [0, 1]], ![[0, 1], [9, 45], [17, 2], [33, 23], [7, 32], [50, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [4, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [54, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1204, 494, -498]
  a := ![-2, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64, 346, -498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-2, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-2, 1, 0]] 
 ![![59, 0, 0], ![57, 1, 0], ![20, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-2, 1, 0], ![2, 0, 6], ![58, -10, -4]]]
  hmulB := by decide  
  f := ![![![-3359, -2, -10092], ![118, 99238, 0]], ![![-3243, -2, -9744], ![119, 95816, 0]], ![![-1138, -1, -3421], ![59, 33640, 0]]]
  g := ![![![1, 0, 0], ![-57, 59, 0], ![-20, 0, 59]], ![![-1, 1, 0], ![-2, 0, 6], ![12, -10, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![10, -19, 1]] ![![59, 0, 0], ![-2, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-118, 59, 0]], ![![590, -1121, 59], ![0, 0, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-2, 1, 0]]], ![![![10, -19, 1]], ![![0, 0, -2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [35, 11, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 40, 44], [54, 20, 17], [0, 1]]
 g := ![![[0, 23, 42], [38, 49], [33, 42, 46], [53, 55, 49], [1]], ![[49, 5, 36, 29], [0, 57], [46, 18, 36, 28], [39, 31, 44, 23], [14, 4, 19, 28]], ![[36, 8, 14, 35], [58, 42], [43, 16, 40, 38], [13, 39, 17, 55], [18, 40, 29, 33]]]
 h' := ![![[0, 40, 44], [28, 37, 15], [4, 12, 54], [36, 59, 31], [26, 50, 54], [0, 1]], ![[54, 20, 17], [27, 43, 37], [37, 16, 22], [38, 49, 44], [59, 11, 47], [0, 40, 44]], ![[0, 1], [53, 42, 9], [3, 33, 46], [31, 14, 47], [3, 0, 21], [54, 20, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 8], []]
 b := ![[], [19, 47, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [35, 11, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-366, 1037, -3843]
  a := ![-1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 17, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [49, 44, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40, 32], [30, 26, 35], [0, 1]]
 g := ![![[12, 45, 55], [25, 65, 40], [54, 15], [20, 37], [45, 1], []], ![[16, 44, 30, 43], [25, 7, 66, 28], [51, 37], [11, 15], [7, 6], [65, 19]], ![[13, 22, 30, 15], [27, 49, 25, 4], [4, 55], [11, 55], [24, 59], [62, 19]]]
 h' := ![![[15, 40, 32], [48, 12, 16], [3, 49, 24], [61, 27, 22], [6, 48, 38], [0, 0, 1], [0, 1]], ![[30, 26, 35], [36, 28, 63], [48, 9, 48], [1, 23, 29], [2, 9, 45], [55, 22, 26], [15, 40, 32]], ![[0, 1], [35, 27, 55], [9, 9, 62], [65, 17, 16], [66, 10, 51], [6, 45, 40], [30, 26, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 66], []]
 b := ![[], [51, 36, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [49, 44, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2057101, -52729, -160867]
  a := ![2, 21, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30703, -787, -2401]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-13, 28, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-13, 28, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![58, 28, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-13, 28, 1], ![114, 33, 166], ![1582, -267, -78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -28, 71]], ![![-1, 0, 1], ![-134, -65, 166], ![86, 27, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [32, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 70], [0, 1]]
 g := ![![[70, 20], [34, 30], [32, 9], [32], [30], [1]], ![[0, 51], [0, 41], [36, 62], [32], [30], [1]]]
 h' := ![![[32, 70], [48, 34], [41, 32], [19, 68], [64, 48], [39, 32], [0, 1]], ![[0, 1], [0, 37], [0, 39], [65, 3], [38, 23], [69, 39], [32, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [33, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [32, 39, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1670, 462, -374]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![282, 154, -374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 1, 0]] 
 ![![71, 0, 0], ![47, 1, 0], ![7, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 1, 0], ![2, -22, 6], ![58, -10, -26]]]
  hmulB := by decide  
  f := ![![![3593, -46350, 12648], ![-1846, -149668, 0]], ![![2383, -30673, 8370], ![-1206, -99045, 0]], ![![361, -4570, 1247], ![-162, -14756, 0]]]
  g := ![![![1, 0, 0], ![-47, 71, 0], ![-7, 0, 71]], ![![-1, 1, 0], ![14, -22, 6], ![10, -10, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-13, 28, 1]] ![![71, 0, 0], ![-24, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1704, 71, 0]], ![![-923, 1988, 71], ![426, -639, 142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-24, 1, 0]]], ![![![-13, 28, 1]], ![![6, -9, 2]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [35, 16, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 70, 16], [72, 2, 57], [0, 1]]
 g := ![![[26, 30, 16], [62, 1], [7, 70], [31, 56, 2], [38, 1], []], ![[58, 26, 0, 49], [31, 41], [8, 41], [41, 55, 40, 70], [59, 4], [69, 37]], ![[36, 69, 44, 55], [66, 65], [24, 64], [10, 28, 65, 72], [20, 9], [28, 37]]]
 h' := ![![[39, 70, 16], [21, 19, 4], [1, 12, 1], [10, 63, 56], [57, 14, 41], [0, 0, 1], [0, 1]], ![[72, 2, 57], [33, 69, 20], [13, 32, 48], [72, 42, 25], [11, 45, 14], [55, 68, 2], [39, 70, 16]], ![[0, 1], [28, 58, 49], [32, 29, 24], [19, 41, 65], [54, 14, 18], [43, 5, 70], [72, 2, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 63], []]
 b := ![[], [37, 57, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [35, 16, 35, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95849, -15768, 11826]
  a := ![2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1313, -216, 162]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![4, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![4, 1, 0]] 
 ![![79, 0, 0], ![4, 1, 0], ![49, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![4, 1, 0], ![2, 6, 6], ![58, -10, 2]]]
  hmulB := by decide  
  f := ![![![-279, -840, -840], ![0, 11060, 0]], ![![-14, -42, -42], ![1, 553, 0]], ![![-173, -521, -521], ![-1, 6860, 0]]]
  g := ![![![1, 0, 0], ![-4, 79, 0], ![-49, 0, 79]], ![![0, 1, 0], ![-4, 6, 6], ![0, -10, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10703, 1989, 840]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-10703, 1989, 840]] 
 ![![79, 0, 0], ![29, 1, 0], ![48, 0, 1]] where
  M :=![![![-10703, 1989, 840], ![52698, -15125, 10254], ![80082, -8970, -22241]]]
  hmulB := by decide  
  f := ![![![428373505, 36702549, 33100206]], ![![182481629, 15634816, 14100264]], ![![269626170, 23101260, 20833879]]]
  g := ![![![-1376, 1989, 840], ![-11, -15125, 10254], ![17820, -8970, -22241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-33, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-33, 1, 0]] 
 ![![79, 0, 0], ![46, 1, 0], ![1, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-33, 1, 0], ![2, -31, 6], ![58, -10, -35]]]
  hmulB := by decide  
  f := ![![![4744, -93426, 18090], ![-3081, -238185, 0]], ![![2752, -54382, 10530], ![-1816, -138645, 0]], ![![73, -1183, 229], ![-8, -3015, 0]]]
  g := ![![![1, 0, 0], ![-46, 79, 0], ![-1, 0, 79]], ![![-1, 1, 0], ![18, -31, 6], ![7, -10, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![4, 1, 0]] ![![-10703, 1989, 840]]
  ![![79, 0, 0], ![-33, 19, 1]] where
 M := ![![![-845537, 157131, 66360]], ![![9886, -7169, 13614]]]
 hmul := by decide  
 g := ![![![![-9020, 1020, 789], ![4029, 0, 0]]], ![![![103, -78, 173], ![-53, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-33, 19, 1]] ![![79, 0, 0], ![-33, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2607, 79, 0]], ![![-2607, 1501, 79], ![1185, -632, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-33, 1, 0]]], ![![![-33, 19, 1]], ![![15, -8, 1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB95I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB95I1 : PrimesBelowBoundCertificateInterval O 31 79 95 where
  m := 11
  g := ![3, 2, 3, 2, 1, 2, 1, 1, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB95I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N2
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I43N1, I47N1, I59N1, I71N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N1], [I47N1], [], [I59N1], [], [], [I71N1], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
