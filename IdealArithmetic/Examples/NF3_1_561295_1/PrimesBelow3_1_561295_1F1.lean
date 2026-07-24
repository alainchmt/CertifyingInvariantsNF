
import IdealArithmetic.Examples.NF3_1_561295_1.RI3_1_561295_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-1, -11, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-1, -11, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 26, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-1, -11, 1], ![-90, 9, -95], ![805, 234, -65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -26, 37]], ![![-1, -1, 1], ![90, 67, -95], ![85, 52, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 36], [0, 1]]
 g := ![![[21, 16], [36], [24, 4], [27], [1]], ![[4, 21], [36], [29, 33], [27], [1]]]
 h' := ![![[29, 36], [14, 4], [12, 6], [23, 35], [19, 29], [0, 1]], ![[0, 1], [19, 33], [1, 31], [2, 2], [9, 8], [29, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [1, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [18, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2325, -711, -1782]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1671, 1233, -1782]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-16, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-16, 1, 0]] 
 ![![37, 0, 0], ![21, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-16, 1, 0], ![1, -19, 9], ![-79, -23, -12]]]
  hmulB := by decide  
  f := ![![![75, -1709, 810], ![-37, -3330, 0]], ![![36, -968, 459], ![-36, -1887, 0]], ![![52, -1293, 613], ![-39, -2520, 0]]]
  g := ![![![1, 0, 0], ![-21, 37, 0], ![-28, 0, 37]], ![![-1, 1, 0], ![4, -19, 9], ![20, -23, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-1, -11, 1]] ![![37, 0, 0], ![-16, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-592, 37, 0]], ![![-37, -407, 37], ![-74, 185, -111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-16, 1, 0]]], ![![![-1, -11, 1]], ![![-2, 5, -3]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![1, 9, 9], ![-79, -23, 16]]]
  hmulB := by decide  
  f := ![![![-227, -2373, -2376], ![-123, 10824, 0]], ![![-77, -693, -693], ![1, 3157, 0]], ![![-116, -1158, -1159], ![-42, 5280, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-7, 9, 9], ![-3, -23, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![24, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![1, -14, 9], ![-79, -23, -7]]]
  hmulB := by decide  
  f := ![![![-874, 14545, -9360], ![615, 42640, 0]], ![![-638, 10629, -6840], ![452, 31160, 0]], ![![-510, 8514, -5479], ![366, 24960, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-24, 0, 41]], ![![-1, 1, 0], ![5, -14, 9], ![19, -23, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-2, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-2, 1, 0]] 
 ![![41, 0, 0], ![39, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-2, 1, 0], ![1, -5, 9], ![-79, -23, 2]]]
  hmulB := by decide  
  f := ![![![-455, 2298, -4140], ![82, 18860, 0]], ![![-432, 2183, -3933], ![83, 17917, 0]], ![![-444, 2242, -4039], ![78, 18400, 0]]]
  g := ![![![1, 0, 0], ![-39, 41, 0], ![-40, 0, 41]], ![![-1, 1, 0], ![-4, -5, 9], ![18, -23, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![12, 1, 0]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0], ![31, 18, 1]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![492, 41, 0], ![-131, -2, 9]]]
 hmul := by decide  
 g := ![![![![10, -18, -1], ![41, 0, 0]], ![![-11, 1, 0], ![0, 0, 0]]], ![![![-19, -17, -1], ![41, 0, 0]], ![![-10, -4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![31, 18, 1]] ![![41, 0, 0], ![-2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-82, 41, 0]], ![![1271, 738, 41], ![-123, -82, 164]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-2, 1, 0]]], ![![![31, 18, 1]], ![![-3, -2, 4]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 7, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 7, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![40, 7, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 7, 1], ![-72, -47, 67], ![-617, -180, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -7, 43]], ![![-1, 0, 1], ![-64, -12, 67], ![-19, -5, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 42], [0, 1]]
 g := ![![[8, 23], [42, 15], [21], [6, 40], [1]], ![[10, 20], [19, 28], [21], [2, 3], [1]]]
 h' := ![![[30, 42], [7, 25], [26, 12], [1, 35], [36, 30], [0, 1]], ![[0, 1], [26, 18], [42, 31], [19, 8], [33, 13], [30, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [24, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4032, 611, -7536]
  a := ![2, -9, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7104, 1241, -7536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![38, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![1, 16, 9], ![-79, -23, 23]]]
  hmulB := by decide  
  f := ![![![-293, -6522, -3672], ![-258, 17544, 0]], ![![-142, -2878, -1620], ![-85, 7740, 0]], ![![-266, -5764, -3245], ![-212, 15504, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-38, 0, 43]], ![![0, 1, 0], ![-15, 16, 9], ![-12, -23, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-3, 7, 1]] ![![43, 0, 0], ![19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![817, 43, 0]], ![![-129, 301, 43], ![-129, 86, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![19, 1, 0]]], ![![![-3, 7, 1]], ![![-3, 2, 2]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 20, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 20, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![3, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 20, 1], ![-59, -80, 184], ![-1644, -479, 63]]]
  hmulB := by decide  
  f := ![![![-2, -20, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -20, 47]], ![![0, 0, 1], ![-13, -80, 184], ![-39, -37, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [4, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 46], [0, 1]]
 g := ![![[20, 12], [10, 6], [12, 21], [0, 8], [1]], ![[0, 35], [0, 41], [24, 26], [18, 39], [1]]]
 h' := ![![[14, 46], [7, 23], [46, 37], [0, 31], [43, 14], [0, 1]], ![[0, 1], [0, 24], [0, 10], [11, 16], [4, 33], [14, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [10, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [4, 33, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6486740, -2058943, -5771643]
  a := ![-65, 132, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![230387, 2412211, -5771643]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, 1, 0]] 
 ![![47, 0, 0], ![4, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, 1, 0], ![1, 1, 9], ![-79, -23, 8]]]
  hmulB := by decide  
  f := ![![![-359, -360, -3240], ![0, 16920, 0]], ![![-30, -30, -270], ![1, 1410, 0]], ![![-235, -237, -2137], ![-21, 11160, 0]]]
  g := ![![![1, 0, 0], ![-4, 47, 0], ![-31, 0, 47]], ![![0, 1, 0], ![-6, 1, 9], ![-5, -23, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![3, 20, 1]] ![![47, 0, 0], ![4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![188, 47, 0]], ![![141, 940, 47], ![-47, 0, 188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![4, 1, 0]]], ![![![3, 20, 1]], ![![-1, 0, 4]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [18, 21, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 47, 39], [20, 5, 14], [0, 1]]
 g := ![![[41, 52, 42], [17, 37], [41, 35, 37], [43, 46], [1]], ![[7, 28, 4, 5], [5, 4], [20, 28, 22, 3], [21, 47], [45, 49, 46, 12]], ![[15, 25, 52, 18], [14, 44], [5, 19, 11, 50], [16, 37], [39, 19, 2, 41]]]
 h' := ![![[4, 47, 39], [28, 36, 25], [4, 33, 39], [27, 32, 14], [35, 32, 24], [0, 1]], ![[20, 5, 14], [40, 40, 45], [17, 36, 51], [9, 51, 46], [49, 5, 43], [4, 47, 39]], ![[0, 1], [26, 30, 36], [38, 37, 16], [21, 23, 46], [37, 16, 39], [20, 5, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 24], []]
 b := ![[], [5, 41, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [18, 21, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4656739, -1409800, -3435831]
  a := ![-2, 8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87863, -26600, -64827]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![32, -11, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![32, -11, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![32, 48, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![32, -11, 1], ![-90, 42, -95], ![805, 234, -32]]]
  hmulB := by decide  
  f := ![![![-31, 11, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -48, 59]], ![![0, -1, 1], ![50, 78, -95], ![31, 30, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [55, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 58], [0, 1]]
 g := ![![[28, 35], [23, 21], [19], [44, 7], [53, 1]], ![[54, 24], [15, 38], [19], [2, 52], [47, 58]]]
 h' := ![![[53, 58], [33, 34], [18, 32], [58, 45], [35, 40], [0, 1]], ![[0, 1], [6, 25], [3, 27], [24, 14], [31, 19], [53, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [43, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [55, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2286, -715, -1764]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![918, 1423, -1764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![32, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![1, -26, 9], ![-79, -23, -19]]]
  hmulB := by decide  
  f := ![![![650, -23441, 8118], ![-649, -53218, 0]], ![![413, -14294, 4950], ![-353, -32450, 0]], ![![358, -12714, 4403], ![-338, -28864, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-32, 0, 59]], ![![-1, 1, 0], ![11, -26, 9], ![23, -23, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![32, -11, 1]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![1888, -649, 59], ![-826, 295, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-23, 1, 0]]], ![![![32, -11, 1]], ![![-14, 5, -2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![14, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![14, 1, 0]] 
 ![![61, 0, 0], ![14, 1, 0], ![44, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![14, 1, 0], ![1, 11, 9], ![-79, -23, 18]]]
  hmulB := by decide  
  f := ![![![-1443, -17414, -14256], ![-610, 96624, 0]], ![![-335, -3991, -3267], ![-121, 22143, 0]], ![![-1042, -12561, -10283], ![-435, 69696, 0]]]
  g := ![![![1, 0, 0], ![-14, 61, 0], ![-44, 0, 61]], ![![0, 1, 0], ![-9, 11, 9], ![-9, -23, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![15, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![15, 1, 0]] 
 ![![61, 0, 0], ![15, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![15, 1, 0], ![1, 12, 9], ![-79, -23, 19]]]
  hmulB := by decide  
  f := ![![![-977, -12989, -9747], ![-427, 66063, 0]], ![![-251, -3191, -2394], ![-60, 16226, 0]], ![![-223, -2981, -2237], ![-103, 15162, 0]]]
  g := ![![![1, 0, 0], ![-15, 61, 0], ![-14, 0, 61]], ![![0, 1, 0], ![-5, 12, 9], ![0, -23, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-30, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-30, 1, 0]] 
 ![![61, 0, 0], ![31, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-30, 1, 0], ![1, -33, 9], ![-79, -23, -26]]]
  hmulB := by decide  
  f := ![![![17, 461, -126], ![61, 854, 0]], ![![24, 230, -63], ![62, 427, 0]], ![![2, 348, -95], ![24, 644, 0]]]
  g := ![![![1, 0, 0], ![-31, 61, 0], ![-46, 0, 61]], ![![-1, 1, 0], ![10, -33, 9], ![30, -23, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![14, 1, 0]] ![![61, 0, 0], ![15, 1, 0]]
  ![![61, 0, 0], ![37, -31, 1]] where
 M := ![![![3721, 0, 0], ![915, 61, 0]], ![![854, 61, 0], ![211, 26, 9]]]
 hmul := by decide  
 g := ![![![![24, 31, -1], ![61, 0, 0]], ![![-22, 32, -1], ![61, 0, 0]]], ![![![-23, 32, -1], ![61, 0, 0]], ![![-2, 5, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![37, -31, 1]] ![![61, 0, 0], ![-30, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1830, 61, 0]], ![![2257, -1891, 61], ![-1220, 1037, -305]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-30, 1, 0]]], ![![![37, -31, 1]], ![![-20, 17, -5]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 9, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 9, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![11, 9, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 9, 1], ![-70, -39, 85], ![-775, -226, 27]]]
  hmulB := by decide  
  f := ![![![-10, -9, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -9, 67]], ![![0, 0, 1], ![-15, -12, 85], ![-16, -7, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [46, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 66], [0, 1]]
 g := ![![[63, 37], [54, 33], [25], [1], [21], [1]], ![[37, 30], [29, 34], [25], [1], [21], [1]]]
 h' := ![![[50, 66], [62, 38], [53, 57], [8, 5], [11, 1], [21, 50], [0, 1]], ![[0, 1], [19, 29], [22, 10], [57, 62], [61, 66], [42, 17], [50, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [26, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [46, 17, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55820, -16733, -1755]
  a := ![2, 14, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-545, -14, -1755]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-18, 1, 0]] 
 ![![67, 0, 0], ![49, 1, 0], ![40, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-18, 1, 0], ![1, -21, 9], ![-79, -23, -14]]]
  hmulB := by decide  
  f := ![![![-205, 5457, -2340], ![201, 17420, 0]], ![![-153, 3988, -1710], ![135, 12730, 0]], ![![-124, 3258, -1397], ![114, 10400, 0]]]
  g := ![![![1, 0, 0], ![-49, 67, 0], ![-40, 0, 67]], ![![-1, 1, 0], ![10, -21, 9], ![24, -23, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 9, 1]] ![![67, 0, 0], ![-18, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1206, 67, 0]], ![![737, 603, 67], ![-268, -201, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-18, 1, 0]]], ![![![11, 9, 1]], ![![-4, -3, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 16, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 16, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![25, 16, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 16, 1], ![-63, -46, 148], ![-1328, -387, 69]]]
  hmulB := by decide  
  f := ![![![-24, -16, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -16, 71]], ![![0, 0, 1], ![-53, -34, 148], ![-43, -21, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [54, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 70], [0, 1]]
 g := ![![[5, 25], [25, 54], [1, 5], [57], [54], [1]], ![[0, 46], [0, 17], [0, 66], [57], [54], [1]]]
 h' := ![![[14, 70], [70, 66], [17, 14], [46, 17], [0, 25], [17, 14], [0, 1]], ![[0, 1], [0, 5], [0, 57], [0, 54], [66, 46], [0, 57], [14, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [49, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [54, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3000, 997, -7193]
  a := ![-2, 8, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2575, 1635, -7193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-6, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-6, 1, 0]] 
 ![![71, 0, 0], ![65, 1, 0], ![2, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-6, 1, 0], ![1, -9, 9], ![-79, -23, -2]]]
  hmulB := by decide  
  f := ![![![-2718, 24948, -24957], ![639, 196883, 0]], ![![-2489, 22834, -22842], ![569, 180198, 0]], ![![-72, 702, -703], ![72, 5546, 0]]]
  g := ![![![1, 0, 0], ![-65, 71, 0], ![-2, 0, 71]], ![![-1, 1, 0], ![8, -9, 9], ![20, -23, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![25, 16, 1]] ![![71, 0, 0], ![-6, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-426, 71, 0]], ![![1775, 1136, 71], ![-213, -142, 142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-6, 1, 0]]], ![![![25, 16, 1]], ![![-3, -2, 2]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [20, 25, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 20, 34], [47, 52, 39], [0, 1]]
 g := ![![[41, 10, 71], [64, 6], [40, 71], [16, 37, 1], [30, 1], []], ![[44, 15, 5, 10], [1, 48], [22, 23], [43, 46, 65, 7], [69, 3], [51, 61]], ![[18, 51, 55, 13], [8, 19], [62, 1], [0, 14, 61, 11], [8, 35], [46, 61]]]
 h' := ![![[56, 20, 34], [71, 64, 61], [57, 72, 58], [45, 65, 12], [57, 33, 72], [0, 0, 1], [0, 1]], ![[47, 52, 39], [17, 33, 19], [16, 9, 62], [23, 65, 60], [8, 39, 48], [72, 37, 52], [56, 20, 34]], ![[0, 1], [21, 49, 66], [20, 65, 26], [26, 16, 1], [27, 1, 26], [48, 36, 20], [47, 52, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 69], []]
 b := ![[], [9, 36, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [20, 25, 43, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7946123, 2346585, 2139192]
  a := ![2, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108851, 32145, 29304]
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


def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![19, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![19, 1, 0]] 
 ![![79, 0, 0], ![19, 1, 0], ![19, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![19, 1, 0], ![1, 16, 9], ![-79, -23, 23]]]
  hmulB := by decide  
  f := ![![![-1004, -17595, -9900], ![-395, 86900, 0]], ![![-245, -4223, -2376], ![-78, 20856, 0]], ![![-247, -4232, -2381], ![-72, 20900, 0]]]
  g := ![![![1, 0, 0], ![-19, 79, 0], ![-19, 0, 79]], ![![0, 1, 0], ![-6, 16, 9], ![-1, -23, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-10, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-10, 1, 0]] 
 ![![79, 0, 0], ![69, 1, 0], ![12, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-10, 1, 0], ![1, -13, 9], ![-79, -23, -6]]]
  hmulB := by decide  
  f := ![![![4314, -58133, 40257], ![-1264, -353367, 0]], ![![3767, -50764, 35154], ![-1105, -308574, 0]], ![![662, -8831, 6115], ![-139, -53676, 0]]]
  g := ![![![1, 0, 0], ![-69, 79, 0], ![-12, 0, 79]], ![![-1, 1, 0], ![10, -13, 9], ![20, -23, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![19, 1, 0]] ![![79, 0, 0], ![-10, 1, 0]]
  ![![79, 0, 0], ![-21, 27, 1]] where
 M := ![![![6241, 0, 0], ![-790, 79, 0]], ![![1501, 79, 0], ![-189, 6, 9]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![11, -26, -1], ![79, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![0, -3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-21, 27, 1]] ![![79, 0, 0], ![-10, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-790, 79, 0]], ![![-1659, 2133, 79], ![158, -395, 237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-10, 1, 0]]], ![![![-21, 27, 1]], ![![2, -5, 3]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB212I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB212I1 : PrimesBelowBoundCertificateInterval O 31 79 212 where
  m := 11
  g := ![2, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB212I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N1]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I79N0, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [], [I79N0, I79N1, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
