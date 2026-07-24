
import IdealArithmetic.Examples.NF3_1_236708_1.RI3_1_236708_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80531, -40330, 4872]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![80531, -40330, 4872]] 
 ![![37, 0, 0], ![0, 37, 0], ![20, 0, 1]] where
  M :=![![![80531, -40330, 4872], ![457968, -16909, -35458], ![-3333052, 1167128, -52367]]]
  hmulB := by decide  
  f := ![![![1142418871, 96602338, 40875724]], ![![3842318056, 324904391, 137478062]], ![![966792304, 81751448, 34591809]]]
  g := ![![![-457, -1090, 4872], ![31544, -457, -35458], ![-61776, 31544, -52367]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [13, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 36], [0, 1]]
 g := ![![[14, 7], [36], [20, 11], [9], [1]], ![[35, 30], [36], [16, 26], [9], [1]]]
 h' := ![![[3, 36], [14, 9], [36, 31], [15, 23], [24, 3], [0, 1]], ![[0, 1], [4, 28], [18, 6], [10, 14], [33, 34], [3, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [18, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [13, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![295, 0, -50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 0, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1142418871, 96602338, 40875724]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1142418871, 96602338, 40875724]] 
 ![![37, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![1142418871, 96602338, 40875724], ![3842318056, 324904391, 137478062], ![12922937828, 1092756816, 462382453]]]
  hmulB := by decide  
  f := ![![![80531, -40330, 4872]], ![![90732, -39697, 3782]], ![![-11728, -7696, 3325]]]
  g := ![![![-102886253, 96602338, 40875724], ![-346039196, 324904391, 137478062], ![-1163839888, 1092756816, 462382453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![80531, -40330, 4872]] ![![1142418871, 96602338, 40875724]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76245851, -6447309, -2728075]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-76245851, -6447309, -2728075]] 
 ![![41, 0, 0], ![0, 41, 0], ![7, 30, 1]] where
  M :=![![![-76245851, -6447309, -2728075], ![-256439050, -21684351, -9175384], ![-862486096, -72931370, -30859735]]]
  hmulB := by decide  
  f := ![![![-2705, -235, 309]], ![![29046, -8885, 74]], ![![20961, -5869, -108]]]
  g := ![![![-1393886, 1838901, -2728075], ![-4688082, 6184809, -9175384], ![-15767511, 20801480, -30859735]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[23, 10], [36], [37], [14, 18], [1]], ![[0, 31], [36], [37], [30, 23], [1]]]
 h' := ![![[10, 40], [37, 25], [4, 35], [15, 23], [4, 10], [0, 1]], ![[0, 1], [0, 16], [26, 6], [40, 18], [22, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [22, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [37, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-275, 848, -92]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 88, -92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2705, -235, 309]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-2705, -235, 309]] 
 ![![41, 0, 0], ![10, 1, 0], ![23, 0, 1]] where
  M :=![![![-2705, -235, 309], ![29046, -8885, 74], ![6956, 27566, -8811]]]
  hmulB := by decide  
  f := ![![![-76245851, -6447309, -2728075]], ![![-24851160, -2101401, -889174]], ![![-63808309, -5395597, -2283060]]]
  g := ![![![-182, -235, 309], ![2834, -8885, 74], ![-1611, 27566, -8811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-76245851, -6447309, -2728075]] ![![-2705, -235, 309]]
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
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-902983995, -76355851, -32308749]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-902983995, -76355851, -32308749]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 37, 1]] where
  M :=![![![-902983995, -76355851, -32308749], ![-3037022406, -256809015, -108664600], ![-10214472400, -863730406, -365473615]]]
  hmulB := by decide  
  f := ![![![-18875, 5797, -55]], ![![-5170, -17775, 5742]], ![![5031, -17142, 4652]]]
  g := ![![![-15740064, 26024834, -32308749], ![-52938842, 87529795, -108664600], ![-178050165, 294390543, -365473615]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [17, 15, 1] where
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
 g := ![![[11, 38], [30, 13], [21], [16, 10], [1]], ![[0, 5], [7, 30], [21], [38, 33], [1]]]
 h' := ![![[28, 42], [6, 9], [11, 20], [29, 8], [26, 28], [0, 1]], ![[0, 1], [0, 34], [12, 23], [38, 35], [36, 15], [28, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [17, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3059, 1, 93]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56, -80, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18875, -5797, 55]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![18875, -5797, 55]] 
 ![![43, 0, 0], ![5, 1, 0], ![18, 0, 1]] where
  M :=![![![18875, -5797, 55], ![5170, 17775, -5742], ![-539748, 120010, 12033]]]
  hmulB := by decide  
  f := ![![![902983995, 76355851, 32308749]], ![![175626567, 14850890, 6283915]], ![![615539170, 52049668, 22023979]]]
  g := ![![![1090, -5797, 55], ![457, 17775, -5742], ![-31544, 120010, 12033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-902983995, -76355851, -32308749]] ![![18875, -5797, 55]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![334321, 28270, 11962]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![334321, 28270, 11962]] 
 ![![47, 0, 0], ![0, 47, 0], ![20, 46, 1]] where
  M :=![![![334321, 28270, 11962], ![1124428, 95081, 40232], ![3781808, 319788, 135313]]]
  hmulB := by decide  
  f := ![![![-329, 118, -6]], ![![-564, -209, 112]], ![![-468, -214, 105]]]
  g := ![![![2023, -11106, 11962], ![6804, -37353, 40232], ![22884, -125630, 135313]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 46], [0, 1]]
 g := ![![[45, 4], [7, 7], [29, 18], [27, 18], [1]], ![[8, 43], [1, 40], [27, 29], [25, 29], [1]]]
 h' := ![![[26, 46], [3, 45], [46, 17], [25, 26], [34, 26], [0, 1]], ![[0, 1], [45, 2], [18, 30], [43, 21], [5, 21], [26, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [2, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![317, 809, -245]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111, 257, -245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-329, 118, -6]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-329, 118, -6]] 
 ![![47, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-329, 118, -6], ![-564, -209, 112], ![10528, -2804, -97]]]
  hmulB := by decide  
  f := ![![![334321, 28270, 11962]], ![![23924, 2023, 856]], ![![80464, 6804, 2879]]]
  g := ![![![-7, 118, -6], ![-12, -209, 112], ![224, -2804, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![334321, 28270, 11962]] ![![-329, 118, -6]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![7, -2, 0]] 
 ![![53, 0, 0], ![23, 1, 0], ![1, 0, 1]] where
  M :=![![![7, -2, 0], ![0, 7, -2], ![-188, 40, 5]]]
  hmulB := by decide  
  f := ![![![115, 10, 4]], ![![57, 5, 2]], ![![27, 2, 1]]]
  g := ![![![1, -2, 0], ![-3, 7, -2], ![-21, 40, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8085, -3016, 182]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![8085, -3016, 182]] 
 ![![53, 0, 0], ![34, 1, 0], ![10, 0, 1]] where
  M :=![![![8085, -3016, 182], ![17108, 4445, -2834], ![-266396, 73788, 1611]]]
  hmulB := by decide  
  f := ![![![-216276087, -18288192, -7738354]], ![![-152467778, -12892595, -5455294]], ![![-86967098, -7353892, -3111681]]]
  g := ![![![2053, -3016, 182], ![-1994, 4445, -2834], ![-52666, 73788, 1611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-791165737, -66900558, -28307894]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-791165737, -66900558, -28307894]] 
 ![![53, 0, 0], ![48, 1, 0], ![28, 0, 1]] where
  M :=![![![-791165737, -66900558, -28307894], ![-2660942036, -225007857, -95208452], ![-8949594488, -756772996, -320216309]]]
  hmulB := by decide  
  f := ![![![22379, -30002, 6942]], ![![32580, -29369, 5852]], ![![-29076, 5164, 1035]]]
  g := ![![![60616643, -66900558, -28307894], ![203873052, -225007857, -95208452], ![685689924, -756772996, -320216309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![7, -2, 0]] ![![8085, -3016, 182]]
  ![![22379, -30002, 6942]] where
 M := ![![![22379, -30002, 6942]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![22379, -30002, 6942]] ![![-791165737, -66900558, -28307894]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1255083157959, -106129170763, -44906849899]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1255083157959, -106129170763, -44906849899]] 
 ![![59, 0, 0], ![39, 1, 0], ![13, 0, 1]] where
  M :=![![![-1255083157959, -106129170763, -44906849899], ![-4221243890506, -356946159979, -151036020662], ![-14197385942228, -1200523477266, -507982180641]]]
  hmulB := by decide  
  f := ![![![503553, 902949, -312985]], ![![-165797, 711496, -196889]], ![![1050895, -499687, 55668]]]
  g := ![![![58775314415, -106129170763, -44906849899], ![197680078259, -356946159979, -151036020662], ![664860983381, -1200523477266, -507982180641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1255083157959, -106129170763, -44906849899]] ![![-1255083157959, -106129170763, -44906849899]]
  ![![2660790726545923375156731, 224995062352214221942828, 95203038150841205106506]] where
 M := ![![![2660790726545923375156731, 224995062352214221942828, 95203038150841205106506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI59N1 : IdealMulLeCertificate' Table 
  ![![2660790726545923375156731, 224995062352214221942828, 95203038150841205106506]] ![![-1255083157959, -106129170763, -44906849899]]
  ![![59, 0, 0]] where
 M := ![![![-5640906935589729229378671542581998365, -476992119310193218931462210667228961, -201831535579438572943845270743582651]]]
 hmul := by decide  
 g := ![![![![-95608592128639478464045280382745735, -8084612191698190151380715435037779, -3420873484397263948200767300738689]]]]
 hle2 := by decide  

def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N0, I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N0
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3857, 326, 138]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![3857, 326, 138]] 
 ![![61, 0, 0], ![0, 61, 0], ![39, 28, 1]] where
  M :=![![![3857, 326, 138], ![12972, 1097, 464], ![43616, 3692, 1561]]]
  hmulB := by decide  
  f := ![![![-11, 10, -2]], ![![-188, 29, 8]], ![![-81, 14, 3]]]
  g := ![![![-25, -58, 138], ![-84, -195, 464], ![-283, -656, 1561]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [41, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 60], [0, 1]]
 g := ![![[21, 3], [1], [32, 42], [57, 3], [54, 1]], ![[0, 58], [1], [43, 19], [36, 58], [47, 60]]]
 h' := ![![[54, 60], [5, 53], [30, 1], [42, 46], [43, 8], [0, 1]], ![[0, 1], [0, 8], [23, 60], [25, 15], [48, 53], [54, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [60, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [41, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![323, 27, -23]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 11, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -10, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![11, -10, 2]] 
 ![![61, 0, 0], ![32, 1, 0], ![13, 0, 1]] where
  M :=![![![11, -10, 2], ![188, -29, -8], ![-752, 348, -37]]]
  hmulB := by decide  
  f := ![![![-3857, -326, -138]], ![![-2236, -189, -80]], ![![-1537, -130, -55]]]
  g := ![![![5, -10, 2], ![20, -29, -8], ![-187, 348, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![3857, 326, 138]] ![![11, -10, 2]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16458135741, 7165193012, -675455206]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-16458135741, 7165193012, -675455206]] 
 ![![67, 0, 0], ![0, 67, 0], ![65, 19, 1]] where
  M :=![![![-16458135741, 7165193012, -675455206], ![-63492789364, -2949031621, 6489737806], ![610035353764, -193287545484, 3540706185]]]
  hmulB := by decide  
  f := ![![![18566325923227225257, 1569958740863021052, 664302764420900638]], ![![62444459855564659972, 5280270634809212497, 2234261505283921690]], ![![38854873190480400299, 3285547611453098985, 1390226573549943101]]]
  g := ![![![409648547, 298490178, -675455206], ![-7243667862, -1884388805, 6489737806], ![5669991817, -3888969597, 3540706185]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [27, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 66], [0, 1]]
 g := ![![[43, 10], [52, 25], [24], [35], [15], [1]], ![[24, 57], [38, 42], [24], [35], [15], [1]]]
 h' := ![![[45, 66], [3, 55], [20, 5], [47, 52], [56, 54], [40, 45], [0, 1]], ![[0, 1], [66, 12], [44, 62], [42, 15], [7, 13], [55, 22], [45, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [6, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-464, 254, -36]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 14, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34618907, -45182143, 16494195]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-34618907, -45182143, 16494195]] 
 ![![67, 0, 0], ![47, 1, 0], ![2, 0, 1]] where
  M :=![![![-34618907, -45182143, 16494195], ![1550454330, -364502807, -28687948], ![-2696667112, 2124213290, -393190755]]]
  hmulB := by decide  
  f := ![![![204258454288378205, 17271987308163585, 7308363345617929]], ![![153539306060326283, 12983202848652360, 5493633252206331]], ![![40583132388540578, 3431688298937048, 1452063652552791]]]
  g := ![![![30685872, -45182143, 16494195], ![279693465, -364502807, -28687948], ![-1518631496, 2124213290, -393190755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-16458135741, 7165193012, -675455206]] ![![-34618907, -45182143, 16494195]]
  ![![67, 0, 0]] where
 M := ![![![13500545041001582119, -3302930048392399461, -211435642370922341]]]
 hmul := by decide  
 g := ![![![![201500672253754957, -49297463408841783, -3155755856282423]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [36, 60, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 31, 66], [3, 39, 5], [0, 1]]
 g := ![![[18, 37, 60], [20, 20, 64], [62, 2, 16], [20, 8], [65, 1], []], ![[22, 65, 44, 22], [30, 37, 17, 28], [63, 52, 49, 33], [], [60, 30], [37, 25]], ![[0, 69, 64, 50], [60, 0, 12, 29], [18, 35, 47, 3], [9, 8], [40, 38], [27, 25]]]
 h' := ![![[62, 31, 66], [61, 35, 29], [40, 43, 8], [70, 30, 4], [3, 40, 47], [0, 0, 1], [0, 1]], ![[3, 39, 5], [32, 0, 33], [11, 25, 26], [50, 63, 6], [60, 52], [27, 14, 39], [62, 31, 66]], ![[0, 1], [0, 36, 9], [62, 3, 37], [0, 49, 61], [18, 50, 24], [31, 57, 31], [3, 39, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 40], []]
 b := ![[], [60, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [36, 60, 6, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25134, -15620, 4473]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![354, -220, 63]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![325629, 27535, 11651]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![325629, 27535, 11651]] 
 ![![73, 0, 0], ![0, 73, 0], ![26, 70, 1]] where
  M :=![![![325629, 27535, 11651], ![1095194, 92609, 39186], ![3683484, 311474, 131795]]]
  hmulB := by decide  
  f := ![![![-233, 113, -13]], ![![-1222, 27, 100]], ![![-1126, 22, 93]]]
  g := ![![![311, -10795, 11651], ![1046, -36307, 39186], ![3518, -122112, 131795]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [12, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 72], [0, 1]]
 g := ![![[58, 67], [64], [27], [54, 70], [61], [1]], ![[0, 6], [64], [27], [25, 3], [61], [1]]]
 h' := ![![[34, 72], [27, 40], [49, 8], [9, 63], [69, 17], [61, 34], [0, 1]], ![[0, 1], [0, 33], [29, 65], [34, 10], [63, 56], [49, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [70, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [12, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3290, 666, 70]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -58, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233, 113, -13]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-233, 113, -13]] 
 ![![73, 0, 0], ![2, 1, 0], ![69, 0, 1]] where
  M :=![![![-233, 113, -13], ![-1222, 27, 100], ![9400, -3222, 127]]]
  hmulB := by decide  
  f := ![![![325629, 27535, 11651]], ![![23924, 2023, 856]], ![![358245, 30293, 12818]]]
  g := ![![![6, 113, -13], ![-112, 27, 100], ![97, -3222, 127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![325629, 27535, 11651]] ![![-233, 113, -13]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [33, 40, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 8, 64], [23, 70, 15], [0, 1]]
 g := ![![[51, 7, 8], [22, 36, 18], [38], [6, 66, 20], [78, 1], []], ![[22, 49, 77, 9], [34, 47, 5, 21], [65, 18, 70, 46], [23, 35, 69, 49], [21, 2], [9, 67]], ![[74, 55, 77, 27], [0, 62, 76, 66], [73, 0, 34, 33], [19, 2, 11, 70], [53, 64], [58, 67]]]
 h' := ![![[55, 8, 64], [64, 7, 18], [10, 1, 27], [39, 14], [33, 7, 40], [0, 0, 1], [0, 1]], ![[23, 70, 15], [20, 33, 49], [14, 13, 58], [19, 33, 27], [44, 40, 9], [42, 47, 70], [55, 8, 64]], ![[0, 1], [22, 39, 12], [5, 65, 73], [45, 32, 52], [15, 32, 30], [37, 32, 8], [23, 70, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 32], []]
 b := ![[], [15, 30, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [33, 40, 1, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9875, -79, 79]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125, -1, 1]
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



lemma PB138I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB138I1 : PrimesBelowBoundCertificateInterval O 31 79 138 where
  m := 11
  g := ![2, 2, 2, 2, 3, 3, 2, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB138I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N0, I59N0]
    · exact ![I61N0, I61N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
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
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N0
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N1, I53N0, I53N1, I53N2, I59N0, I61N1, I67N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [I59N0, I59N0, I59N0], [I61N1], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
