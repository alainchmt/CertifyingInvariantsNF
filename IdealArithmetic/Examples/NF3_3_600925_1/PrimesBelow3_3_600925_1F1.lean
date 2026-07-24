
import IdealArithmetic.Examples.NF3_3_600925_1.RI3_3_600925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-19, 13, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-19, 13, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![18, 13, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-19, 13, 1], ![146, 15, 41], ![2044, 691, 56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -13, 37]], ![![-1, 0, 1], ![-16, -14, 41], ![28, -1, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [12, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36], [0, 1]]
 g := ![![[29, 34], [21], [21, 28], [3], [1]], ![[0, 3], [21], [8, 9], [3], [1]]]
 h' := ![![[22, 36], [19, 21], [7, 24], [34, 19], [25, 22], [0, 1]], ![[0, 1], [0, 16], [17, 13], [8, 18], [28, 15], [22, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [25, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [12, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1180, 918, 711]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-314, -225, 711]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-4, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-4, 1, 0]] 
 ![![37, 0, 0], ![33, 1, 0], ![18, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-4, 1, 0], ![0, -5, 3], ![146, 47, -2]]]
  hmulB := by decide  
  f := ![![![121, -30, 0], ![1110, 0, 0]], ![![109, -27, 0], ![1000, 0, 0]], ![![58, -11, -2], ![532, 25, 0]]]
  g := ![![![1, 0, 0], ![-33, 37, 0], ![-18, 0, 37]], ![![-1, 1, 0], ![3, -5, 3], ![-37, 47, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-19, 13, 1]] ![![37, 0, 0], ![-4, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-148, 37, 0]], ![![-703, 481, 37], ![222, -37, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-4, 1, 0]]], ![![![-19, 13, 1]], ![![6, -1, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1147, 275, -73]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1147, 275, -73]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 26, 1]] where
  M :=![![![1147, 275, -73], ![-10658, -2559, 679], ![29492, 7085, -1880]]]
  hmulB := by decide  
  f := ![![![5, -5, -2]], ![![-292, -84, -19]], ![![-209, -64, -15]]]
  g := ![![![44, 53, -73], ![-409, -493, 679], ![1132, 1365, -1880]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[1, 25], [18], [33], [20, 32], [1]], ![[23, 16], [18], [33], [17, 9], [1]]]
 h' := ![![[14, 40], [39, 36], [19, 31], [34, 22], [14, 14], [0, 1]], ![[0, 1], [10, 5], [2, 10], [14, 19], [5, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [16, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1023, 1862, 2519]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-528, -1552, 2519]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -5, -2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![5, -5, -2]] 
 ![![41, 0, 0], ![2, 1, 0], ![13, 0, 1]] where
  M :=![![![5, -5, -2], ![-292, -84, -19], ![-1022, -395, -103]]]
  hmulB := by decide  
  f := ![![![1147, 275, -73]], ![![-204, -49, 13]], ![![1083, 260, -69]]]
  g := ![![![1, -5, -2], ![3, -84, -19], ![27, -395, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1147, 275, -73]] ![![5, -5, -2]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -51, 12]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-109, -51, 12]] 
 ![![43, 0, 0], ![14, 1, 0], ![11, 0, 1]] where
  M :=![![![-109, -51, 12], ![1752, 506, -129], ![-5694, -1437, 377]]]
  hmulB := by decide  
  f := ![![![-5389, -1983, -507]], ![![-3476, -1279, -327]], ![![-9833, -3618, -925]]]
  g := ![![![11, -51, 12], ![-91, 506, -129], ![239, -1437, 377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-109, -51, 12]] ![![-109, -51, 12]]
  ![![-145799, -37491, 9795]] where
 M := ![![![-145799, -37491, 9795]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-145799, -37491, 9795]] ![![-109, -51, 12]]
  ![![43, 0, 0]] where
 M := ![![![-105564871, -25610112, 6779466]]]
 hmul := by decide  
 g := ![![![![-2454997, -595584, 157662]]]]
 hle2 := by decide  

def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1037, -229, 62]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1037, -229, 62]] 
 ![![47, 0, 0], ![0, 47, 0], ![28, 38, 1]] where
  M :=![![![-1037, -229, 62], ![9052, 2106, -563], ![-24382, -5803, 1543]]]
  hmulB := by decide  
  f := ![![![-373, -137, -35]], ![![-5110, -1881, -481]], ![![-4888, -1799, -460]]]
  g := ![![![-59, -55, 62], ![528, 500, -563], ![-1438, -1371, 1543]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [5, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[7, 16], [13, 25], [14, 27], [10, 3], [1]], ![[11, 31], [31, 22], [9, 20], [46, 44], [1]]]
 h' := ![![[12, 46], [29, 43], [24, 42], [44, 36], [42, 12], [0, 1]], ![[0, 1], [28, 4], [11, 5], [6, 11], [45, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [38, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [5, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1861, 38, 377]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-185, -304, 377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373, -137, -35]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-373, -137, -35]] 
 ![![47, 0, 0], ![25, 1, 0], ![35, 0, 1]] where
  M :=![![![-373, -137, -35], ![-5110, -1881, -481], ![-25112, -9239, -2362]]]
  hmulB := by decide  
  f := ![![![-1037, -229, 62]], ![![-359, -77, 21]], ![![-1291, -294, 79]]]
  g := ![![![91, -137, -35], ![1250, -1881, -481], ![6139, -9239, -2362]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1037, -229, 62]] ![![-373, -137, -35]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [38, 25, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 15, 50], [49, 37, 3], [0, 1]]
 g := ![![[6, 4, 7], [18, 43], [18, 31, 44], [49, 29], [1]], ![[32, 5, 36, 48], [37, 29], [12, 13, 1, 35], [49, 46], [17, 41, 44, 26]], ![[4, 50, 52, 19], [13, 37], [25, 0, 48, 23], [39, 16], [41, 26, 35, 27]]]
 h' := ![![[37, 15, 50], [30, 16, 31], [5, 51, 19], [6, 50, 16], [15, 28, 33], [0, 1]], ![[49, 37, 3], [32, 45, 39], [31, 30, 20], [35, 39, 18], [28, 50, 24], [37, 15, 50]], ![[0, 1], [11, 45, 36], [44, 25, 14], [19, 17, 19], [21, 28, 49], [49, 37, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 38], []]
 b := ![[], [8, 1, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [38, 25, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5519738, -2539601, -1152538]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104146, -47917, -21746]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 22, -12]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![509, 22, -12]] 
 ![![59, 0, 0], ![0, 59, 0], ![51, 8, 1]] where
  M :=![![![509, 22, -12], ![-1752, -77, 42], ![1460, 74, -35]]]
  hmulB := by decide  
  f := ![![![7, 2, 0]], ![![0, 5, 6]], ![![11, 4, 1]]]
  g := ![![![19, 2, -12], ![-66, -7, 42], ![55, 6, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [49, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 58], [0, 1]]
 g := ![![[35, 53], [54, 46], [4], [54, 27], [55, 1]], ![[0, 6], [47, 13], [4], [5, 32], [51, 58]]]
 h' := ![![[55, 58], [9, 17], [3, 20], [9, 2], [19, 26], [0, 1]], ![[0, 1], [0, 42], [41, 39], [1, 57], [33, 33], [55, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [21, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [49, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1217, 907, 755]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-632, -87, 755]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -2, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-7, -2, 0]] 
 ![![59, 0, 0], ![33, 1, 0], ![2, 0, 1]] where
  M :=![![![-7, -2, 0], ![0, -5, -6], ![-292, -94, -11]]]
  hmulB := by decide  
  f := ![![![-509, -22, 12]], ![![-255, -11, 6]], ![![-42, -2, 1]]]
  g := ![![![1, -2, 0], ![3, -5, -6], ![48, -94, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![509, 22, -12]] ![![-7, -2, 0]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![19, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![19, 1, 0]] 
 ![![61, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![19, 1, 0], ![0, 18, 3], ![146, 47, 21]]]
  hmulB := by decide  
  f := ![![![704, 37, 0], ![-2257, 0, 0]], ![![190, 10, 0], ![-609, 0, 0]], ![![78, -8, -2], ![-250, 41, 0]]]
  g := ![![![1, 0, 0], ![-19, 61, 0], ![-8, 0, 61]], ![![0, 1, 0], ![-6, 18, 3], ![-15, 47, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![36, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 19, 3], ![146, 47, 22]]]
  hmulB := by decide  
  f := ![![![641, 32, 0], ![-1952, 0, 0]], ![![220, 11, 0], ![-670, 0, 0]], ![![396, 7, -2], ![-1206, 41, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-36, 0, 61]], ![![0, 1, 0], ![-8, 19, 3], ![-26, 47, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![21, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![21, 1, 0]] 
 ![![61, 0, 0], ![21, 1, 0], ![43, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![21, 1, 0], ![0, 20, 3], ![146, 47, 23]]]
  hmulB := by decide  
  f := ![![![295, 14, 0], ![-854, 0, 0]], ![![63, 3, 0], ![-182, 0, 0]], ![![199, -4, -2], ![-576, 41, 0]]]
  g := ![![![1, 0, 0], ![-21, 61, 0], ![-43, 0, 61]], ![![0, 1, 0], ![-9, 20, 3], ![-30, 47, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![19, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0], ![-36, -28, 1]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![1159, 61, 0], ![380, 38, 3]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![8, 2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-36, -28, 1]] ![![61, 0, 0], ![21, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1281, 61, 0]], ![![-2196, -1708, 61], ![-610, -549, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![21, 1, 0]]], ![![![-36, -28, 1]], ![![-10, -9, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-23, -29, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-23, -29, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![44, 38, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-23, -29, 1], ![146, 53, -85], ![-4088, -1283, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -38, 67]], ![![-1, -1, 1], ![58, 49, -85], ![-40, -1, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [29, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 66], [0, 1]]
 g := ![![[19, 37], [15, 1], [64], [6], [24], [1]], ![[0, 30], [0, 66], [64], [6], [24], [1]]]
 h' := ![![[52, 66], [34, 38], [15, 1], [14, 8], [11, 41], [38, 52], [0, 1]], ![[0, 1], [0, 29], [0, 66], [28, 59], [66, 26], [62, 15], [52, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [14, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [29, 15, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64285, 36634, 24005]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14805, -13068, 24005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![18, 1, 0]] 
 ![![67, 0, 0], ![18, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![18, 1, 0], ![0, 17, 3], ![146, 47, 20]]]
  hmulB := by decide  
  f := ![![![703, 39, 0], ![-2613, 0, 0]], ![![162, 9, 0], ![-602, 0, 0]], ![![332, 7, -2], ![-1234, 45, 0]]]
  g := ![![![1, 0, 0], ![-18, 67, 0], ![-32, 0, 67]], ![![0, 1, 0], ![-6, 17, 3], ![-20, 47, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-23, -29, 1]] ![![67, 0, 0], ![18, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1206, 67, 0]], ![![-1541, -1943, 67], ![-268, -469, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![18, 1, 0]]], ![![![-23, -29, 1]], ![![-4, -7, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-61, -10, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-61, -10, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![10, 61, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-61, -10, 1], ![146, -4, -28], ![-1314, -390, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -61, 71]], ![![-1, -1, 1], ![6, 24, -28], ![-14, 22, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [2, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 70], [0, 1]]
 g := ![![[22, 36], [10, 40], [66, 27], [15], [19], [1]], ![[0, 35], [25, 31], [14, 44], [15], [19], [1]]]
 h' := ![![[27, 70], [51, 6], [10, 53], [61, 58], [37, 50], [69, 27], [0, 1]], ![[0, 1], [0, 65], [21, 18], [65, 13], [38, 21], [17, 44], [27, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [67, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [2, 44, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41, 41, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -2, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![28, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![28, 1, 0]] 
 ![![71, 0, 0], ![28, 1, 0], ![32, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![28, 1, 0], ![0, 27, 3], ![146, 47, 30]]]
  hmulB := by decide  
  f := ![![![477, 17, 0], ![-1207, 0, 0]], ![![140, 5, 0], ![-354, 0, 0]], ![![200, -2, -1], ![-506, 24, 0]]]
  g := ![![![1, 0, 0], ![-28, 71, 0], ![-32, 0, 71]], ![![0, 1, 0], ![-12, 27, 3], ![-30, 47, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-61, -10, 1]] ![![71, 0, 0], ![28, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1988, 71, 0]], ![![-4331, -710, 71], ![-1562, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![28, 1, 0]]], ![![![-61, -10, 1]], ![![-22, -4, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![0, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![0, 1, 0]] 
 ![![73, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![0, 1, 0], ![0, -1, 3], ![146, 47, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![49, 49, 0]]]
  g := ![![![1, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![0, 1, 0], ![0, -1, 3], ![2, 47, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![1, -25, 1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![1, -25, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![1, 48, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![1, -25, 1], ![146, 73, -73], ![-3504, -1095, 0]]]
  hmulB := by decide  
  f := ![![![0, 25, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -48, 73]], ![![0, -1, 1], ![3, 49, -73], ![-48, -15, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [3, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 72], [0, 1]]
 g := ![![[20, 49], [35], [65], [31, 4], [23], [1]], ![[0, 24], [35], [65], [10, 69], [23], [1]]]
 h' := ![![[13, 72], [18, 66], [59, 53], [53, 49], [13, 2], [70, 13], [0, 1]], ![[0, 1], [0, 7], [18, 20], [33, 24], [39, 71], [20, 60], [13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [41, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [3, 60, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3069, 2480, 2777]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -1792, 2777]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![0, 1, 0]] ![![73, 0, 0], ![1, -25, 1]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![73, -1825, 73]], ![![0, 73, 0], ![146, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![1, -25, 1]]], ![![![0, 1, 0]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [8, 78, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 7, 38], [50, 71, 41], [0, 1]]
 g := ![![[34, 78, 72], [23, 70, 22], [76, 74, 5], [75, 2, 42], [15, 1], []], ![[19, 3, 1, 36], [15, 17, 11, 49], [35, 59, 77, 38], [33, 9, 13, 46], [36, 64], [72, 22]], ![[5, 8, 15, 6], [50, 14, 41, 41], [18, 8, 60, 69], [33, 16, 11, 27], [45, 49], [69, 22]]]
 h' := ![![[44, 7, 38], [53, 39, 54], [24, 34, 38], [32, 2, 59], [38, 7, 68], [0, 0, 1], [0, 1]], ![[50, 71, 41], [1, 34, 23], [33, 23, 40], [17, 44, 78], [1, 26, 38], [17, 38, 71], [44, 7, 38]], ![[0, 1], [71, 6, 2], [66, 22, 1], [40, 33, 21], [53, 46, 52], [52, 41, 7], [50, 71, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 6], []]
 b := ![[], [53, 58, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [8, 78, 64, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1582212, -588076, -156104]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20028, -7444, -1976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB173I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB173I1 : PrimesBelowBoundCertificateInterval O 31 79 173 where
  m := 11
  g := ![2, 2, 3, 2, 1, 2, 3, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB173I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![73, 5329]
    · exact ![493039]
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
      exact NI43N0
      exact NI43N0
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N0, I47N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N0]
  Il := ![[I37N1], [I41N1], [I43N0, I43N0, I43N0], [I47N1], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N0], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
