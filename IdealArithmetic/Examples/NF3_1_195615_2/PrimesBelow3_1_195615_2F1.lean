
import IdealArithmetic.Examples.NF3_1_195615_2.RI3_1_195615_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [23, 7, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 6, 28], [30, 30, 9], [0, 1]]
 g := ![![[31, 26, 9], [20, 25], [2, 11, 11], [20, 1], []], ![[5, 17, 17, 36], [22, 26], [18, 5, 20, 21], [21, 12], [32, 7]], ![[5, 15, 23, 26], [28, 25], [26, 28, 35, 7], [9, 36], [14, 7]]]
 h' := ![![[27, 6, 28], [28, 1, 34], [28, 26, 5], [21, 22, 23], [0, 0, 1], [0, 1]], ![[30, 30, 9], [2, 4, 12], [29, 36, 27], [10, 24, 11], [30, 13, 30], [27, 6, 28]], ![[0, 1], [26, 32, 28], [35, 12, 5], [26, 28, 3], [23, 24, 6], [30, 30, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 30], []]
 b := ![[], [23, 19, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [23, 7, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-201354, -15207, -8140]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5442, -411, -220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 29, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36, 20], [25, 4, 21], [0, 1]]
 g := ![![[30, 34, 9], [20, 23], [3, 39], [7, 6, 1], []], ![[35, 23], [1, 5], [16, 4], [35, 20, 32, 33], [27, 31]], ![[10, 21, 30, 25], [21, 25], [5, 40], [16, 35, 16, 33], [26, 31]]]
 h' := ![![[22, 36, 20], [21, 24, 3], [26, 33, 33], [27, 31, 30], [0, 0, 1], [0, 1]], ![[25, 4, 21], [35, 6], [18, 32, 13], [38, 39, 2], [20, 1, 4], [22, 36, 20]], ![[0, 1], [3, 11, 38], [39, 17, 36], [34, 12, 9], [40, 40, 36], [25, 4, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 20], []]
 b := ![[], [26, 21, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 29, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1942908, 381833, 1312]
  a := ![-5, -7, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47388, 9313, 32]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76491, -10911, -8110]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-76491, -10911, -8110]] 
 ![![43, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![-76491, -10911, -8110], ![-667528, -95219, -70775], ![-1462695, -208645, -155083]]]
  hmulB := by decide  
  f := ![![![1698, -337, 65]], ![![697, -47, -15]], ![![-211, -81, 48]]]
  g := ![![![3471, -10911, -8110], ![30291, -95219, -70775], ![66374, -208645, -155083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1044213525, 274447743, -70642610]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1044213525, 274447743, -70642610]] 
 ![![43, 0, 0], ![33, 1, 0], ![10, 0, 1]] where
  M :=![![![-1044213525, 274447743, -70642610], ![-6553517336, -1946322061, 1230953495], ![18665645895, 30029125, -989816309]]]
  hmulB := by decide  
  f := ![![![1889536862173750974, 269531516223624337, 200339138151092575]], ![![1833592561909986101, 261551385020036472, 194407614335031670]], ![![1279719316714364845, 182544566702909860, 135682912632315661]]]
  g := ![![![-218478208, 274447743, -70642610], ![1055013389, -1946322061, 1230953495], ![641229020, 30029125, -989816309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5782060075470, -824777462793, -613045956100]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-5782060075470, -824777462793, -613045956100]] 
 ![![43, 0, 0], ![39, 1, 0], ![12, 0, 1]] where
  M :=![![![-5782060075470, -824777462793, -613045956100], ![-50459351342914, -7197734930384, -5349979226165], ![-110567117440005, -15771760479865, -11722936693756]]]
  hmulB := by decide  
  f := ![![![-23814579, 1494008, 563555]], ![![-20554754, 797244, 711065]], ![![-2827666, 839667, -235326]]]
  g := ![![![784670056899, -824777462793, -613045956100], ![6847722364094, -7197734930384, -5349979226165], ![15004808874414, -15771760479865, -11722936693756]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-76491, -10911, -8110]] ![![-1044213525, 274447743, -70642610]]
  ![![-23814579, 1494008, 563555]] where
 M := ![![![-23814579, 1494008, 563555]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-23814579, 1494008, 563555]] ![![-5782060075470, -824777462793, -613045956100]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4021, 1095, -710]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![4021, 1095, -710]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 16, 1]] where
  M :=![![![4021, 1095, -710], ![-62540, -1719, 4055], ![46215, -8015, 1241]]]
  hmulB := by decide  
  f := ![![![-646118, -92165, -68505]], ![![-5638595, -804313, -597835]], ![![-2498587, -356409, -264914]]]
  g := ![![![433, 265, -710], ![-3315, -1417, 4055], ![376, -593, 1241]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [35, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 46], [0, 1]]
 g := ![![[45, 18], [32, 12], [11, 37], [29, 12], [1]], ![[36, 29], [26, 35], [16, 10], [23, 35], [1]]]
 h' := ![![[23, 46], [8, 21], [38, 24], [19, 15], [12, 23], [0, 1]], ![[0, 1], [21, 26], [26, 23], [35, 32], [24, 24], [23, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [9, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [35, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314561, 606855, 210580]
  a := ![66, 67, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96357, -58775, 210580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![646118, 92165, 68505]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![646118, 92165, 68505]] 
 ![![47, 0, 0], ![12, 1, 0], ![32, 0, 1]] where
  M :=![![![646118, 92165, 68505], ![5638595, 804313, 597835], ![12355355, 1762420, 1309983]]]
  hmulB := by decide  
  f := ![![![-4021, -1095, 710]], ![![304, -243, 95]], ![![-3721, -575, 457]]]
  g := ![![![-56426, 92165, 68505], ![-492423, 804313, 597835], ![-1079003, 1762420, 1309983]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![4021, 1095, -710]] ![![646118, 92165, 68505]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27966982, -5987187, 4194885]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-27966982, -5987187, 4194885]] 
 ![![53, 0, 0], ![0, 53, 0], ![4, 30, 1]] where
  M :=![![![-27966982, -5987187, 4194885], ![368539599, 4981817, -21546165], ![-232048485, 49766880, -10577161]]]
  hmulB := by decide  
  f := ![![![-19237583538371, -2744130142881, -2039674897770]], ![![-167884106024688, -23947697741459, -17800000509945]], ![![-103421568307393, -14752489180893, -10965326094301]]]
  g := ![![![-844274, -2487429, 4194885], ![8579703, 12289939, -21546165], ![-3579997, 6926070, -10577161]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [20, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 52], [0, 1]]
 g := ![![[15, 28], [44], [3, 10], [37], [18, 1]], ![[42, 25], [44], [24, 43], [37], [36, 52]]]
 h' := ![![[18, 52], [17, 9], [46, 37], [17, 40], [11, 39], [0, 1]], ![[0, 1], [20, 44], [23, 16], [48, 13], [24, 14], [18, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [37, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [20, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2588, 2214, 360]
  a := ![5, 6, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -162, 360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19237583538371, -2744130142881, -2039674897770]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-19237583538371, -2744130142881, -2039674897770]] 
 ![![53, 0, 0], ![7, 1, 0], ![35, 0, 1]] where
  M :=![![![-19237583538371, -2744130142881, -2039674897770], ![-167884106024688, -23947697741459, -17800000509945], ![-367869605397705, -52474473772035, -39003568108523]]]
  hmulB := by decide  
  f := ![![![-27966982, -5987187, 4194885]], ![![3259825, -696764, 147510]], ![![-22847035, -3014805, 2570638]]]
  g := ![![![1346414129882, -2744130142881, -2039674897770], ![11749996151200, -23947697741459, -17800000509945], ![25746728203865, -52474473772035, -39003568108523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-27966982, -5987187, 4194885]] ![![-19237583538371, -2744130142881, -2039674897770]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [17, 5, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 24, 32], [46, 34, 27], [0, 1]]
 g := ![![[51, 3, 9], [57, 49, 7], [27, 51], [46, 16, 25], [1]], ![[15, 35, 19, 40], [37, 25, 5, 2], [35, 4], [32, 40, 31, 14], [29, 22, 34, 23]], ![[57, 55, 54, 27], [38, 2, 29, 1], [55, 3], [36, 21, 21, 57], [52, 53, 21, 36]]]
 h' := ![![[18, 24, 32], [34, 7, 56], [2, 19, 19], [44, 23, 13], [42, 54, 5], [0, 1]], ![[46, 34, 27], [43, 16, 4], [23, 42, 15], [21, 11, 57], [29, 35, 10], [18, 24, 32]], ![[0, 1], [15, 36, 58], [7, 57, 25], [23, 25, 48], [46, 29, 44], [46, 34, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 9], []]
 b := ![[], [58, 5, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [17, 5, 54, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171690, 590, -2950]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2910, 10, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179938800, -11405124, -4204883]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![179938800, -11405124, -4204883]] 
 ![![61, 0, 0], ![9, 1, 0], ![48, 0, 1]] where
  M :=![![![179938800, -11405124, -4204883], ![-334604807, 181724633, -65435386], ![-1246957818, -136918397, 127694371]]]
  hmulB := by decide  
  f := ![![![14245904547944601, 2032095975289555, 1510429511300803]], ![![4139925531827714, 590536457893041, 438937778700928]], ![![15675736458144361, 2236053236148552, 1662028190492916]]]
  g := ![![![7941300, -11405124, -4204883], ![19192984, 181724633, -65435386], ![-100721673, -136918397, 127694371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-440292, 61071, -4846]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-440292, 61071, -4846]] 
 ![![61, 0, 0], ![10, 1, 0], ![8, 0, 1]] where
  M :=![![![-440292, 61071, -4846], ![-534052, -586664, 295663], ![4871199, 213281, -352072]]]
  hmulB := by decide  
  f := ![![![-143488667505, -20467829386, -15213461329]], ![![-44050741463, -6283583758, -4670502998]], ![![-63799398124, -9100615529, -6764364692]]]
  g := ![![![-16594, 61071, -4846], ![48644, -586664, 295663], ![91065, 213281, -352072]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17163, 33702, -14483]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-17163, 33702, -14483]] 
 ![![61, 0, 0], ![42, 1, 0], ![54, 0, 1]] where
  M :=![![![-17163, 33702, -14483], ![-1298459, -156982, 139544], ![1908792, -106667, -51140]]]
  hmulB := by decide  
  f := ![![![22912799328, 3268378441, 2429341582]], ![![19054013924, 2717944998, 2020211833]], ![![27466227469, 3917898657, 2912121192]]]
  g := ![![![-10665, 33702, -14483], ![-36731, -156982, 139544], ![150006, -106667, -51140]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![179938800, -11405124, -4204883]] ![![-440292, 61071, -4846]]
  ![![-93617506711869, 16783196470013, -2763635034436]] where
 M := ![![![-93617506711869, 16783196470013, -2763635034436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-93617506711869, 16783196470013, -2763635034436]] ![![-17163, 33702, -14483]]
  ![![61, 0, 0]] where
 M := ![![![-25460739682211963632, -5494968301240804992, 3839189013580549839]]]
 hmul := by decide  
 g := ![![![![-417389175118228912, -90081447561324672, 62937524812795899]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [47, 48, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 37, 28], [60, 29, 39], [0, 1]]
 g := ![![[65, 20, 23], [53, 20, 59], [37, 25], [17, 21], [20, 1], []], ![[23, 31, 33, 42], [56, 34, 1, 52], [51, 1], [24, 19], [3, 37], [64, 47]], ![[4, 15, 9, 62], [4, 48, 6, 14], [2, 36], [13, 24], [44, 29], [53, 47]]]
 h' := ![![[27, 37, 28], [55, 21, 31], [17, 48, 27], [9, 14, 5], [65, 65, 17], [0, 0, 1], [0, 1]], ![[60, 29, 39], [55, 40, 13], [13, 34, 50], [47, 49, 1], [61, 60, 35], [66, 0, 29], [27, 37, 28]], ![[0, 1], [50, 6, 23], [10, 52, 57], [29, 4, 61], [38, 9, 15], [37, 0, 37], [60, 29, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 64], []]
 b := ![[], [64, 18, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [47, 48, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6482987, 1015184, 674824]
  a := ![-3, 16, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96761, 15152, 10072]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24349, 4362, -3264]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![24349, 4362, -3264]] 
 ![![71, 0, 0], ![0, 71, 0], ![69, 51, 1]] where
  M :=![![![24349, 4362, -3264], ![-286164, -695, 15282], ![155346, -40206, 10225]]]
  hmulB := by decide  
  f := ![![![8553827, 1220154, 906924]], ![![74648232, 10648139, 7914618]], ![![64237239, 9163071, 6810787]]]
  g := ![![![3515, 2406, -3264], ![-18882, -10987, 15282], ![-7749, -7911, 10225]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [34, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 70], [0, 1]]
 g := ![![[27, 30], [39, 60], [3, 9], [4], [25], [1]], ![[35, 41], [55, 11], [48, 62], [4], [25], [1]]]
 h' := ![![[5, 70], [23, 39], [40, 42], [64, 3], [22, 69], [37, 5], [0, 1]], ![[0, 1], [5, 32], [37, 29], [8, 68], [12, 2], [62, 66], [5, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [62, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [34, 66, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3767, 1096, -140]
  a := ![3, 6, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![83, 116, -140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8553827, -1220154, -906924]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-8553827, -1220154, -906924]] 
 ![![71, 0, 0], ![27, 1, 0], ![35, 0, 1]] where
  M :=![![![-8553827, -1220154, -906924], ![-74648232, -10648139, -7914618], ![-163570074, -23332326, -17342603]]]
  hmulB := by decide  
  f := ![![![-24349, -4362, 3264]], ![![-5229, -1649, 1026]], ![![-14191, -1584, 1465]]]
  g := ![![![790601, -1220154, -906924], ![6899481, -10648139, -7914618], ![15118223, -23332326, -17342603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![24349, 4362, -3264]] ![![-8553827, -1220154, -906924]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [68, 23, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 39, 12], [60, 33, 61], [0, 1]]
 g := ![![[68, 45, 24], [40, 19], [49, 36], [26, 3, 61], [35, 1], []], ![[23, 52, 16, 64], [25, 25], [31, 8], [52, 70, 68, 32], [1, 67], [63, 71]], ![[49, 57, 21, 1], [34, 3], [16, 6], [23, 25, 39, 23], [54, 61], [14, 71]]]
 h' := ![![[48, 39, 12], [8, 5, 30], [63, 68, 26], [57, 39, 6], [29, 3, 34], [0, 0, 1], [0, 1]], ![[60, 33, 61], [51, 52, 28], [27, 12, 68], [50, 47, 9], [13, 62, 63], [64, 22, 33], [48, 39, 12]], ![[0, 1], [32, 16, 15], [64, 66, 52], [35, 60, 58], [13, 8, 49], [20, 51, 39], [60, 33, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 50], []]
 b := ![[], [44, 33, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [68, 23, 38, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1646369, 235352, 76650]
  a := ![-4, -3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22553, 3224, 1050]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3971658, -379367, -34565]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![3971658, -379367, -34565]] 
 ![![79, 0, 0], ![0, 79, 0], ![11, 51, 1]] where
  M :=![![![3971658, -379367, -34565], ![-2179291, 4557567, -1965965], ![-34527485, -2553570, 2970969]]]
  hmulB := by decide  
  f := ![![![107850139587, 15384199287, 11434867690]], ![![941195355076, 134256079463, 99790731815]], ![![648730036092, 92537591485, 68781942774]]]
  g := ![![![55087, 17512, -34565], ![246156, 1326858, -1965965], ![-850736, -1950291, 2970969]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [15, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 78], [0, 1]]
 g := ![![[56, 40], [48, 13], [49, 72], [49, 55], [51], [1]], ![[31, 39], [30, 66], [4, 7], [64, 24], [51], [1]]]
 h' := ![![[29, 78], [70, 35], [55, 48], [55, 54], [13, 56], [64, 29], [0, 1]], ![[0, 1], [58, 44], [25, 31], [41, 25], [57, 23], [36, 50], [29, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [67, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [15, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2340, 3775, 500]
  a := ![5, 5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -275, 500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105860507356401341450878036531237347222622933440, 15100389744790956193481569272932346160552272291, 11223915887843988437623149491440973940132698116]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![105860507356401341450878036531237347222622933440, 15100389744790956193481569272932346160552272291, 11223915887843988437623149491440973940132698116]] 
 ![![79, 0, 0], ![59, 1, 0], ![38, 0, 1]] where
  M :=![![![105860507356401341450878036531237347222622933440, 15100389744790956193481569272932346160552272291, 11223915887843988437623149491440973940132698116], ![923832070977157104811004568226618092590174795278, 131779307306039371252030645442577524602181879438, 97949780499642757842654145347543678683026757687], ![2024311576904934513329061254634353703695701220391, 288756350592990561282247686702040235665282625659, 214628698060891172901203221517188857124656364834]]]
  hmulB := by decide  
  f := ![![![3634487812445286209192559, 412923928756857877543750, -378509465048408660387891]], ![![2296653525919537144991174, 319982334510685340851226, -266132376255299226530919]], ![![1876296786380491442467534, 133722140514242078316599, -159146712116701110799684]]]
  g := ![![![-15336345459801729551825496598057317543987388103, 15100389744790956193481569272932346160552272291, 11223915887843988437623149491440973940132698116], ![-133838464798298615152907101722685008213842694730, 131779307306039371252030645442577524602181879438, 97949780499642757842654145347543678683026757687], ![-293268400435384470538851578208091098370796399458, 288756350592990561282247686702040235665282625659, 214628698060891172901203221517188857124656364834]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![3971658, -379367, -34565]] ![![105860507356401341450878036531237347222622933440, 15100389744790956193481569272932346160552272291, 11223915887843988437623149491440973940132698116]]
  ![![79, 0, 0]] where
 M := ![![![18150055988512717198295609400337399579, 2589000621294925607565800289650069397, 1924369218153074240079661992300064989]]]
 hmul := by decide  
 g := ![![![![229747544158388825294881131649840501, 32772159763226906424883547970254043, 24359104027254104304805848003798291]]]]
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


lemma PB126I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB126I1 : PrimesBelowBoundCertificateInterval O 31 79 126 where
  m := 11
  g := ![1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB126I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
  β := ![I43N0, I43N1, I43N2, I47N1, I53N1, I61N0, I61N1, I61N2, I71N1, I79N1]
  Il := ![[], [], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [], [I61N0, I61N1, I61N2], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
