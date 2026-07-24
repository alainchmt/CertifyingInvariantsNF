
import IdealArithmetic.Examples.NF3_1_138580_1.RI3_1_138580_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![16, -17, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![16, -17, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![16, 20, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![16, -17, 1], ![38, 29, -67], ![-1190, 85, -5]]]
  hmulB := by decide  
  f := ![![![-15, 17, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -20, 37]], ![![0, -1, 1], ![30, 37, -67], ![-30, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[34, 21], [12], [10, 3], [25], [1]], ![[28, 16], [12], [25, 34], [25], [1]]]
 h' := ![![[5, 36], [7, 24], [8, 7], [31, 22], [23, 5], [0, 1]], ![[0, 1], [16, 13], [6, 30], [30, 15], [11, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [7, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [14, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![289, 685, -308]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![141, 185, -308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 1, 0]] 
 ![![37, 0, 0], ![30, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 1, 0], ![2, -8, 4], ![72, -4, -6]]]
  hmulB := by decide  
  f := ![![![680, -2851, 1428], ![-185, -13209, 0]], ![![551, -2308, 1156], ![-147, -10693, 0]], ![![97, -386, 193], ![2, -1785, 0]]]
  g := ![![![1, 0, 0], ![-30, 37, 0], ![-5, 0, 37]], ![![-1, 1, 0], ![6, -8, 4], ![6, -4, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, -17, 1]] ![![37, 0, 0], ![-7, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-259, 37, 0]], ![![592, -629, 37], ![-74, 148, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-7, 1, 0]]], ![![![16, -17, 1]], ![![-2, 4, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![8, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![8, 1, 0]] 
 ![![41, 0, 0], ![8, 1, 0], ![7, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![8, 1, 0], ![2, 7, 4], ![72, -4, 9]]]
  hmulB := by decide  
  f := ![![![1977, 7294, 4176], ![574, -42804, 0]], ![![382, 1418, 812], ![124, -8323, 0]], ![![335, 1245, 713], ![111, -7308, 0]]]
  g := ![![![1, 0, 0], ![-8, 41, 0], ![-7, 0, 41]], ![![0, 1, 0], ![-2, 7, 4], ![1, -4, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-16, 1, 0]] 
 ![![41, 0, 0], ![25, 1, 0], ![35, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-16, 1, 0], ![2, -17, 4], ![72, -4, -15]]]
  hmulB := by decide  
  f := ![![![487, -5076, 1196], ![-287, -12259, 0]], ![![301, -3090, 728], ![-163, -7462, 0]], ![![413, -4333, 1021], ![-252, -10465, 0]]]
  g := ![![![1, 0, 0], ![-25, 41, 0], ![-35, 0, 41]], ![![-1, 1, 0], ![7, -17, 4], ![17, -4, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![8, 1, 0]] ![![41, 0, 0], ![8, 1, 0]]
  ![![41, 0, 0], ![-4, 14, 1]] where
 M := ![![![1681, 0, 0], ![328, 41, 0]], ![![328, 41, 0], ![66, 15, 4]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![8, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![2, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, 14, 1]] ![![41, 0, 0], ![-16, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-656, 41, 0]], ![![-164, 574, 41], ![164, -246, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-16, 1, 0]]], ![![![-4, 14, 1]], ![![4, -6, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [24, 10, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 17, 34], [1, 25, 9], [0, 1]]
 g := ![![[2, 42, 16], [8, 31, 14], [28, 21], [6, 39, 1], []], ![[31, 15, 22, 27], [42, 9, 1, 7], [42, 21], [5, 9, 16, 8], [15, 38]], ![[10, 19, 12, 21], [42, 28, 33, 17], [11, 41], [9, 26, 14, 21], [40, 38]]]
 h' := ![![[38, 17, 34], [23, 24, 4], [26, 28, 10], [28, 36, 35], [0, 0, 1], [0, 1]], ![[1, 25, 9], [25, 38, 13], [19, 24, 41], [34, 19, 35], [9, 15, 25], [38, 17, 34]], ![[0, 1], [38, 24, 26], [10, 34, 35], [39, 31, 16], [30, 28, 17], [1, 25, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 4], []]
 b := ![[], [35, 14, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [24, 10, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![472269, -34529, -10277]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10983, -803, -239]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2745, 461, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-2745, 461, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![28, 38, 1]] where
  M :=![![![-2745, 461, 1], ![994, -3210, 1845], ![33226, -1827, -2288]]]
  hmulB := by decide  
  f := ![![![227985, 22403, 18165]], ![![1352686, 132922, 107777]], ![![1276942, 125479, 101742]]]
  g := ![![![-59, 9, 1], ![-1078, -1560, 1845], ![2070, 1811, -2288]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 46], [0, 1]]
 g := ![![[46, 21], [19, 4], [16, 4], [26, 28], [1]], ![[37, 26], [24, 43], [21, 43], [14, 19], [1]]]
 h' := ![![[13, 46], [35, 31], [27, 2], [38, 2], [34, 13], [0, 1]], ![[0, 1], [15, 16], [6, 45], [17, 45], [15, 34], [13, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [21, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 34, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![140630, 74483, -11216]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9674, 10653, -11216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227985, 22403, 18165]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![227985, 22403, 18165]] 
 ![![47, 0, 0], ![35, 1, 0], ![32, 0, 1]] where
  M :=![![![227985, 22403, 18165], ![1352686, 132922, 107777], ![2230626, 219193, 177728]]]
  hmulB := by decide  
  f := ![![![-2745, 461, 1]], ![![-2023, 275, 40]], ![![-1162, 275, -48]]]
  g := ![![![-24200, 22403, 18165], ![-143584, 132922, 107777], ![-236775, 219193, 177728]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-2745, 461, 1]] ![![227985, 22403, 18165]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [36, 38, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 27, 25], [37, 25, 28], [0, 1]]
 g := ![![[45, 43, 17], [15, 36], [39, 22, 43], [23, 49], [1]], ![[10, 52, 36, 43], [46, 37], [45, 30, 40, 24], [17, 29], [23, 28, 46, 43]], ![[10, 8, 34, 24], [40, 29], [35, 2, 22, 11], [28, 40], [48, 34, 40, 10]]]
 h' := ![![[23, 27, 25], [30, 22, 32], [27, 33, 47], [44, 45, 34], [17, 15, 7], [0, 1]], ![[37, 25, 28], [41, 13, 25], [1, 36, 39], [33, 18, 14], [50, 51, 20], [23, 27, 25]], ![[0, 1], [51, 18, 49], [22, 37, 20], [35, 43, 5], [6, 40, 26], [37, 25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [43, 21, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [36, 38, 46, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1023536, 158364, -7632]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19312, 2988, -144]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![14, 12, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![14, 12, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![14, 12, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![14, 12, 1], ![96, -2, 49], ![898, -31, 22]]]
  hmulB := by decide  
  f := ![![![-13, -12, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -12, 59]], ![![0, 0, 1], ![-10, -10, 49], ![10, -5, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [47, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 58], [0, 1]]
 g := ![![[35, 51], [47, 53], [45], [10, 4], [7, 1]], ![[38, 8], [5, 6], [45], [38, 55], [14, 58]]]
 h' := ![![[7, 58], [33, 13], [13, 42], [2, 35], [25, 2], [0, 1]], ![[0, 1], [6, 46], [12, 17], [11, 24], [39, 57], [7, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [39, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [47, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![262, 705, -428]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106, 99, -428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![10, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![10, 1, 0]] 
 ![![59, 0, 0], ![10, 1, 0], ![37, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![10, 1, 0], ![2, 9, 4], ![72, -4, 11]]]
  hmulB := by decide  
  f := ![![![-239, -1080, -480], ![0, 7080, 0]], ![![-40, -180, -80], ![1, 1180, 0]], ![![-147, -677, -301], ![-17, 4440, 0]]]
  g := ![![![1, 0, 0], ![-10, 59, 0], ![-37, 0, 59]], ![![0, 1, 0], ![-4, 9, 4], ![-5, -4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![14, 12, 1]] ![![59, 0, 0], ![10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![590, 59, 0]], ![![826, 708, 59], ![236, 118, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![10, 1, 0]]], ![![![14, 12, 1]], ![![4, 2, 1]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [48, 37, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 38, 48], [43, 22, 13], [0, 1]]
 g := ![![[41, 10, 13], [18, 58], [46, 47, 34], [34, 56, 58], [1]], ![[47, 17, 51, 13], [48, 60], [55, 3, 1, 25], [52, 12, 4, 16], [6, 2, 24, 60]], ![[55, 51, 1, 12], [10, 41], [13, 31, 51, 46], [43, 28, 56, 25], [49, 12, 18, 1]]]
 h' := ![![[45, 38, 48], [12, 10, 47], [49, 49, 34], [15, 5, 41], [13, 24, 27], [0, 1]], ![[43, 22, 13], [26, 17, 50], [45, 16, 50], [18, 20, 44], [8, 13, 38], [45, 38, 48]], ![[0, 1], [4, 34, 25], [39, 57, 38], [40, 36, 37], [51, 24, 57], [43, 22, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 53], []]
 b := ![[], [58, 22, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [48, 37, 34, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93616090, -7812087, 4350581]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1534690, -128067, 71321]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-9, -18, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-9, -18, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![58, 49, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-9, -18, 1], ![36, 5, -71], ![-1262, 89, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -49, 67]], ![![-1, -1, 1], ![62, 52, -71], ![8, 24, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [45, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 66], [0, 1]]
 g := ![![[53, 60], [42, 29], [29], [17], [59], [1]], ![[65, 7], [21, 38], [29], [17], [59], [1]]]
 h' := ![![[27, 66], [53, 44], [58, 30], [31, 30], [40, 34], [22, 27], [0, 1]], ![[0, 1], [35, 23], [64, 37], [37, 37], [20, 33], [14, 40], [27, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [33, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [45, 40, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![225, 48, 42]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -30, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![4, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![4, 1, 0]] 
 ![![67, 0, 0], ![4, 1, 0], ![31, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![4, 1, 0], ![2, 3, 4], ![72, -4, 5]]]
  hmulB := by decide  
  f := ![![![-441, -663, -884], ![0, 14807, 0]], ![![-26, -39, -52], ![1, 871, 0]], ![![-205, -307, -409], ![16, 6851, 0]]]
  g := ![![![1, 0, 0], ![-4, 67, 0], ![-31, 0, 67]], ![![0, 1, 0], ![-2, 3, 4], ![-1, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-9, -18, 1]] ![![67, 0, 0], ![4, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![268, 67, 0]], ![![-603, -1206, 67], ![0, -67, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![4, 1, 0]]], ![![![-9, -18, 1]], ![![0, -1, -1]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [69, 58, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 70, 2], [67, 0, 69], [0, 1]]
 g := ![![[5, 59, 32], [66, 20, 24], [3, 16, 6], [23, 58], [6, 1], []], ![[44, 45, 7, 45], [69, 49, 50, 27], [49, 62, 1, 15], [28, 40], [], [20, 4]], ![[8, 34, 64, 68], [47, 50, 54, 66], [28, 50, 6, 53], [8, 16], [5, 1], [24, 4]]]
 h' := ![![[10, 70, 2], [61, 11, 23], [6, 32, 38], [48, 63, 19], [12, 9, 49], [0, 0, 1], [0, 1]], ![[67, 0, 69], [54, 13, 22], [37, 20, 64], [1, 34, 55], [4, 2, 18], [69, 35], [10, 70, 2]], ![[0, 1], [69, 47, 26], [38, 19, 40], [18, 45, 68], [59, 60, 4], [64, 36, 70], [67, 0, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 21], []]
 b := ![[], [64, 17, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [69, 58, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1290141, -142, 710]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18171, -2, 10]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109305769, 104710566, -74669886]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![109305769, 104710566, -74669886]] 
 ![![73, 0, 0], ![0, 73, 0], ![71, 51, 1]] where
  M :=![![![109305769, 104710566, -74669886], ![-5166810660, 303274747, 344172378], ![5000384628, -1688230326, 512695879]]]
  hmulB := by decide  
  f := ![![![10089451491819217, 991442332989114, 803890072426230]], ![![59862969880666788, 5882448869125183, 4769659404382686]], ![![52987378496861351, 5206817258450697, 4221837784943599]]]
  g := ![![![74121475, 53601024, -74669886], ![-405521226, -236294747, 344172378], ![-430150997, -381311235, 512695879]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [72, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 72], [0, 1]]
 g := ![![[36, 72], [35], [36], [61, 64], [55], [1]], ![[0, 1], [35], [36], [29, 9], [55], [1]]]
 h' := ![![[36, 72], [23, 46], [34, 53], [61, 67], [56, 8], [1, 36], [0, 1]], ![[0, 1], [0, 27], [44, 20], [64, 6], [52, 65], [56, 37], [36, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [60, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [72, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![762, 425, -235]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239, 170, -235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419607, 103273, -105513]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![419607, 103273, -105513]] 
 ![![73, 0, 0], ![14, 1, 0], ![28, 0, 1]] where
  M :=![![![419607, 103273, -105513], ![-7390390, 738386, 307579], ![3848214, -2206813, 944932]]]
  hmulB := by decide  
  f := ![![![1376493895479, 135261497633, 109673928085]], ![![375862470604, 36934214416, 29947327559]], ![![712459869286, 70010037269, 56766159824]]]
  g := ![![![26413, 103273, -105513], ![-360822, 738386, 307579], ![113500, -2206813, 944932]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![109305769, 104710566, -74669886]] ![![419607, 103273, -105513]]
  ![![73, 0, 0]] where
 M := ![![![-1015332154731561, 253387625801731, -49884373142535]]]
 hmul := by decide  
 g := ![![![![-13908659653857, 3471063367147, -683347577295]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [16, 16, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 30, 61], [7, 48, 18], [0, 1]]
 g := ![![[11, 8, 40], [23, 73, 25], [77, 15, 36], [71, 15, 44], [68, 1], []], ![[24, 23, 68, 3], [49, 9, 33, 37], [30, 71, 41, 71], [31, 58, 67, 71], [56, 13], [17, 8]], ![[37, 58, 48, 51], [65, 30, 20, 65], [11, 78, 50, 10], [31, 9, 64, 2], [58, 31], [60, 8]]]
 h' := ![![[61, 30, 61], [27, 41, 44], [32, 60, 74], [49, 54, 6], [18, 2, 26], [0, 0, 1], [0, 1]], ![[7, 48, 18], [76, 21, 31], [35, 36, 23], [21, 8, 27], [70, 53, 27], [52, 21, 48], [61, 30, 61]], ![[0, 1], [46, 17, 4], [30, 62, 61], [17, 17, 46], [46, 24, 26], [37, 58, 30], [7, 48, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 63], []]
 b := ![[], [26, 23, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [16, 16, 11, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-951792, 106176, -103016]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12048, 1344, -1304]
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



lemma PB106I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB106I1 : PrimesBelowBoundCertificateInterval O 31 79 106 where
  m := 11
  g := ![2, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB106I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
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
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
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
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I47N1, I59N1, I67N1, I73N1]
  Il := ![[I37N1], [I41N0, I41N0, I41N1], [], [I47N1], [], [I59N1], [], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
