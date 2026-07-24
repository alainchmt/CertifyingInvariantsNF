
import IdealArithmetic.Examples.NF3_1_391287_1.RI3_1_391287_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [28, 6, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18, 26], [12, 18, 11], [0, 1]]
 g := ![![[13, 22, 4], [28, 36], [7, 27, 3], [18, 1], []], ![[20, 24, 20, 16], [13, 4], [15, 35, 28, 21], [12, 28], [6, 10]], ![[11, 31, 24, 3], [5, 16], [33, 34, 7, 27], [34, 28], [21, 10]]]
 h' := ![![[6, 18, 26], [3, 6, 2], [26, 27, 31], [14, 12, 22], [0, 0, 1], [0, 1]], ![[12, 18, 11], [34, 19, 7], [18, 13, 2], [31, 14, 5], [16, 11, 18], [6, 18, 26]], ![[0, 1], [1, 12, 28], [17, 34, 4], [10, 11, 10], [0, 26, 18], [12, 18, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 28], []]
 b := ![[], [5, 2, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [28, 6, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-105894, 12987, -3885]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2862, 351, -105]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, 4, 8]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-167, 4, 8]] 
 ![![41, 0, 0], ![0, 41, 0], ![15, 21, 1]] where
  M :=![![![-167, 4, 8], ![956, -195, 20], ![1128, 300, -179]]]
  hmulB := by decide  
  f := ![![![705, 76, 40]], ![![4724, 509, 268]], ![![2979, 321, 169]]]
  g := ![![![-7, -4, 8], ![16, -15, 20], ![93, 99, -179]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 39, 1] where
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
 g := ![![[25, 8], [20], [33], [28, 4], [1]], ![[0, 33], [20], [33], [36, 37], [1]]]
 h' := ![![[2, 40], [27, 7], [3, 15], [17, 19], [5, 2], [0, 1]], ![[0, 1], [0, 34], [33, 26], [14, 22], [9, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [24, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4513, 2546, 131]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-158, -5, 131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-705, -76, -40]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-705, -76, -40]] 
 ![![41, 0, 0], ![18, 1, 0], ![7, 0, 1]] where
  M :=![![![-705, -76, -40], ![-4724, -509, -268], ![-12360, -1332, -701]]]
  hmulB := by decide  
  f := ![![![167, -4, -8]], ![![50, 3, -4]], ![![1, -8, 3]]]
  g := ![![![23, -76, -40], ![154, -509, -268], ![403, -1332, -701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-167, 4, 8]] ![![-705, -76, -40]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, -27, -4]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![251, -27, -4]] 
 ![![43, 0, 0], ![2, 1, 0], ![42, 0, 1]] where
  M :=![![![251, -27, -4], ![-453, 290, -85], ![-3564, -75, 232]]]
  hmulB := by decide  
  f := ![![![60905, 6564, 3455]], ![![12322, 1328, 699]], ![![84315, 9087, 4783]]]
  g := ![![![11, -27, -4], ![59, 290, -85], ![-306, -75, 232]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8129654, -1289173, 28939]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![8129654, -1289173, 28939]] 
 ![![43, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![8129654, -1289173, 28939], ![4761853, 9332010, -3838580], ![-152356701, 4996140, 6782603]]]
  hmulB := by decide  
  f := ![![![-82473402103230, -8888531952779, -4678534656950]], ![![-43537443268207, -4692227381955, -2469783372709]], ![![-71977981014210, -7757392902751, -4083152508863]]]
  g := ![![![655294, -1289173, 28939], ![-1576249, 9332010, -3838580], ![-8556907, 4996140, 6782603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317311234278801708, 34198068382490218, 18000368224834191]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![317311234278801708, 34198068382490218, 18000368224834191]] 
 ![![43, 0, 0], ![25, 1, 0], ![29, 0, 1]] where
  M :=![![![317311234278801708, 34198068382490218, 18000368224834191], ![2125846118597612702, 229112061221808917, 120594573372304845], ![5561798032110395631, 599420155621062795, 315508566211623544]]]
  hmulB := by decide  
  f := ![![![-2521399927, 595531253, -83774937]], ![![-1713570276, 279597092, -9105921]], ![![-196339940, 284106745, -97390511]]]
  g := ![![![-24643050088456867, 34198068382490218, 18000368224834191], ![-165097628831266296, 229112061221808917, 120594573372304845], ![-431940797175657140, 599420155621062795, 315508566211623544]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![251, -27, -4]] ![![8129654, -1289173, 28939]]
  ![![2521399927, -595531253, 83774937]] where
 M := ![![![2521399927, -595531253, 83774937]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![2521399927, -595531253, 83774937]] ![![317311234278801708, 34198068382490218, 18000368224834191]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52538202655660849, 5662279973147013, 2980376650774119]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![52538202655660849, 5662279973147013, 2980376650774119]] 
 ![![47, 0, 0], ![0, 47, 0], ![15, 36, 1]] where
  M :=![![![52538202655660849, 5662279973147013, 2980376650774119], ![351982918119747267, 37934792730191479, 19967216570215158], ![920884105490345199, 99247849460749602, 52239729327259624]]]
  hmulB := by decide  
  f := ![![![143886740, 15958458, -14308701]], ![![-1733002578, 170854385, 33566673]], ![![-1265399607, 123068511, 25153879]]]
  g := ![![![166650061575512, -2162367647972793, 2980376650774119], ![1116482331202551, -14486914974416047, 19967216570215158], ![2921024799605337, -37901753325970146, 52239729327259624]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 46], [0, 1]]
 g := ![![[26, 9], [31, 27], [4, 42], [0, 42], [1]], ![[0, 38], [0, 20], [8, 5], [4, 5], [1]]]
 h' := ![![[18, 46], [7, 44], [10, 36], [0, 29], [26, 18], [0, 1]], ![[0, 1], [0, 3], [0, 11], [5, 18], [21, 29], [18, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [13, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331496, 175933, -11311]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10663, 12407, -11311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143886740, 15958458, -14308701]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![143886740, 15958458, -14308701]] 
 ![![47, 0, 0], ![32, 1, 0], ![45, 0, 1]] where
  M :=![![![143886740, 15958458, -14308701], ![-1733002578, 170854385, 33566673], ![756010179, -605914713, 188462600]]]
  hmulB := by decide  
  f := ![![![52538202655660849, 5662279973147013, 2980376650774119]], ![![43259689427678605, 4662292592997785, 2454027008403978]], ![![69895813297767732, 7532988260688621, 3965035715150957]]]
  g := ![![![5895907, 15958458, -14308701], ![-185337089, 170854385, 33566673], ![248180085, -605914713, 188462600]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![52538202655660849, 5662279973147013, 2980376650774119]] ![![143886740, 15958458, -14308701]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7484, 5379, -1629]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-7484, 5379, -1629]] 
 ![![53, 0, 0], ![0, 53, 0], ![3, 17, 1]] where
  M :=![![![-7484, 5379, -1629], ![-200859, -7976, 14508], ![513531, -79668, 1153]]]
  hmulB := by decide  
  f := ![![![21634472, 2331645, 1227276]], ![![144941475, 15620999, 8222211]], ![![54870099, 5913599, 3112660]]]
  g := ![![![-49, 624, -1629], ![-4611, -4804, 14508], ![9624, -1873, 1153]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [10, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 52], [0, 1]]
 g := ![![[23, 16], [24], [48, 17], [16], [35, 1]], ![[0, 37], [24], [7, 36], [16], [17, 52]]]
 h' := ![![[35, 52], [34, 49], [50, 17], [16, 21], [21, 49], [0, 1]], ![[0, 1], [0, 4], [9, 36], [9, 32], [40, 4], [35, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [13, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [10, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2439, 2768, -336]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, 160, -336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21634472, 2331645, 1227276]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![21634472, 2331645, 1227276]] 
 ![![53, 0, 0], ![1, 1, 0], ![35, 0, 1]] where
  M :=![![![21634472, 2331645, 1227276], ![144941475, 15620999, 8222211], ![379206756, 40868829, 21511565]]]
  hmulB := by decide  
  f := ![![![-7484, 5379, -1629]], ![![-3931, -49, 243]], ![![4747, 2049, -1054]]]
  g := ![![![-446261, 2331645, 1227276], ![-2989753, 15620999, 8222211], ![-7822016, 40868829, 21511565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-7484, 5379, -1629]] ![![21634472, 2331645, 1227276]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![202, -38, 3]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![202, -38, 3]] 
 ![![59, 0, 0], ![5, 1, 0], ![52, 0, 1]] where
  M :=![![![202, -38, 3], ![398, 231, -111], ![-4317, 231, 158]]]
  hmulB := by decide  
  f := ![![![62139, 6697, 3525]], ![![12322, 1328, 699]], ![![73227, 7892, 4154]]]
  g := ![![![4, -38, 3], ![85, 231, -111], ![-232, 231, 158]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1861, 474, -75]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1861, 474, -75]] 
 ![![59, 0, 0], ![7, 1, 0], ![25, 0, 1]] where
  M :=![![![-1861, 474, -75], ![-9474, -2110, 1347], ![50805, -4347, -1237]]]
  hmulB := by decide  
  f := ![![![8465479, 912363, 480228]], ![![1965650, 211847, 111507]], ![![6102017, 657642, 346154]]]
  g := ![![![-56, 474, -75], ![-481, -2110, 1347], ![1901, -4347, -1237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24218701410, -2610159104, -1373873649]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-24218701410, -2610159104, -1373873649]] 
 ![![59, 0, 0], ![47, 1, 0], ![46, 0, 1]] where
  M :=![![![-24218701410, -2610159104, -1373873649], ![-162254678776, -17486921359, -9204350961], ![-424502858049, -45750594999, -24081113216]]]
  hmulB := by decide  
  f := ![![![-136505, -162887, 70047]], ![![36488, -132872, 48705]], ![![-341557, -72412, 47164]]]
  g := ![![![2739948548, -2610159104, -1373873649], ![18356453717, -17486921359, -9204350961], ![48025530760, -45750594999, -24081113216]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![202, -38, 3]] ![![-1861, 474, -75]]
  ![![136505, 162887, -70047]] where
 M := ![![![136505, 162887, -70047]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![136505, 162887, -70047]] ![![-24218701410, -2610159104, -1373873649]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![202067910, -56416871, 10035454]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![202067910, -56416871, 10035454]] 
 ![![61, 0, 0], ![0, 61, 0], ![48, 27, 1]] where
  M :=![![![202067910, -56416871, 10035454], ![1260671351, 228378419, -159215159], ![-5957152746, 560633319, 125580131]]]
  hmulB := by decide  
  f := ![![![-1933460898375010, -208377834991507, -109680983083283]], ![![-12953340135002453, -1396040114133654, -734814488057804]], ![![-7810423058947434, -841764655679910, -443068116930463]]]
  g := ![![![-4584162, -5366789, 10035454], ![145950803, 74216192, -159215159], ![-196475394, -46393938, 125580131]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [8, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 60], [0, 1]]
 g := ![![[1, 46], [16], [8, 4], [14, 25], [53, 1]], ![[60, 15], [16], [37, 57], [58, 36], [45, 60]]]
 h' := ![![[53, 60], [3, 31], [58, 4], [10, 2], [3, 56], [0, 1]], ![[0, 1], [60, 30], [26, 57], [55, 59], [43, 5], [53, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [15, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![746, 351, -48]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 27, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-725425148355, -33459072730, 54175715723]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-725425148355, -33459072730, 54175715723]] 
 ![![61, 0, 0], ![40, 1, 0], ![49, 0, 1]] where
  M :=![![![-725425148355, -33459072730, 54175715723], ![6534544959490, -854493222794, -46201502467], ![373144245963, 2213230131387, -867235652531]]]
  hmulB := by decide  
  f := ![![![843301545028386967623343, 90886425655516314118171, 47838641356596475214972]], ![![645603480955271137977249, 69579610188913668730936, 36623665124377121740465]], ![![919722569425200550821919, 99122665460016606275734, 52173837941703895358118]]]
  g := ![![![-33470037862, -33459072730, 54175715723], ![704559794953, -854493222794, -46201502467], ![-748549410418, 2213230131387, -867235652531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![202067910, -56416871, 10035454]] ![![-725425148355, -33459072730, 54175715723]]
  ![![61, 0, 0]] where
 M := ![![![-511499051697055971638, 63657598198602457972, 4850614355452835613]]]
 hmul := by decide  
 g := ![![![![-8385230355689442158, 1043567183583646852, 79518268122177633]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368650021120604952, 39731081882880383, 20912704655244866]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![368650021120604952, 39731081882880383, 20912704655244866]] 
 ![![67, 0, 0], ![17, 1, 0], ![43, 0, 1]] where
  M :=![![![368650021120604952, 39731081882880383, 20912704655244866], ![2469793476746503537, 266180825271989971, 140105950303886015], ![6461658903020480106, 696402235905908625, 366555693692995603]]]
  hmulB := by decide  
  f := ![![![-5042281862, 202413301, 210304859]], ![![-905740625, -36337069, 65563095]], ![![-2619310901, 243260023, 56457174]]]
  g := ![![![-18000368224834191, 39731081882880383, 20912704655244866], ![-120594573372304845, 266180825271989971, 140105950303886015], ![-315508566211623544, 696402235905908625, 366555693692995603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9278513227982244, 999987380149228, 526349642370141]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![9278513227982244, 999987380149228, 526349642370141]] 
 ![![67, 0, 0], ![52, 1, 0], ![9, 0, 1]] where
  M :=![![![9278513227982244, 999987380149228, 526349642370141], ![62161969704267692, 6699476920722593, 3526311782817825], ![162632806649888781, 17527673911987815, 9225801323391190]]]
  hmulB := by decide  
  f := ![![![245353295, 91330595, -48906513]], ![![101466555, 75372137, -34597812]], ![![137409306, -20289111, -84503]]]
  g := ![![![-708328019718043, 999987380149228, 526349642370141], ![-4745487107741307, 6699476920722593, 3526311782817825], ![-12415499234089527, 17527673911987815, 9225801323391190]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![192745, 20773, 10934]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![192745, 20773, 10934]] 
 ![![67, 0, 0], ![65, 1, 0], ![20, 0, 1]] where
  M :=![![![192745, 20773, 10934], ![1291307, 139170, 73253], ![3378414, 364107, 191650]]]
  hmulB := by decide  
  f := ![![![429, 488, -211]], ![![31, 482, -186]], ![![747, 1, -43]]]
  g := ![![![-20540, 20773, 10934], ![-137609, 139170, 73253], ![-360023, 364107, 191650]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![368650021120604952, 39731081882880383, 20912704655244866]] ![![9278513227982244, 999987380149228, 526349642370141]]
  ![![9291378258507523328276703463206670, 1001373902736889556451459573677965, 527079447248323438052511133895747]] where
 M := ![![![9291378258507523328276703463206670, 1001373902736889556451459573677965, 527079447248323438052511133895747]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![9291378258507523328276703463206670, 1001373902736889556451459573677965, 527079447248323438052511133895747]] ![![192745, 20773, 10934]]
  ![![67, 0, 0]] where
 M := ![![![4864640416353494606026094466632407764663, 524284322907115003728627261339333297889, 275960348440847817652880002628453612475]]]
 hmul := by decide  
 g := ![![![![72606573378410367254120812934812056189, 7825139147867388115352645691631840267, 4118811170758922651535522427290352425]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1101044581, 1729528734, -723882050]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1101044581, 1729528734, -723882050]] 
 ![![71, 0, 0], ![0, 71, 0], ![66, 57, 1]] where
  M :=![![![1101044581, 1729528734, -723882050], ![-88595374734, 1543161997, 4464704152], ![148909002030, -33419986152, 4278337415]]]
  hmulB := by decide  
  f := ![![![-2194542516081522829, -236515783009740690, -124491568867092358]], ![![-14702472481041342270, -1584552026470505065, -834038917896314428]], ![![-14385161246762540562, -1550353958088014847, -816038549671480237]]]
  g := ![![![688412111, 605504304, -723882050], ![-5398110546, -3562605277, 4464704152], ![-1879736160, -3905425617, 4278337415]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [16, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 70], [0, 1]]
 g := ![![[21, 40], [23, 10], [24, 25], [9], [6], [1]], ![[0, 31], [0, 61], [2, 46], [9], [6], [1]]]
 h' := ![![[19, 70], [58, 53], [42, 9], [38, 66], [18, 3], [55, 19], [0, 1]], ![[0, 1], [0, 18], [0, 62], [14, 5], [4, 68], [61, 52], [19, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [67, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [16, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18217, 768, 1284]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-937, -1020, 1284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2194542516081522829, 236515783009740690, 124491568867092358]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2194542516081522829, 236515783009740690, 124491568867092358]] 
 ![![71, 0, 0], ![41, 1, 0], ![21, 0, 1]] where
  M :=![![![2194542516081522829, 236515783009740690, 124491568867092358], ![14702472481041342270, 1584552026470505065, 834038917896314428], ![38465711039403363798, 4145623836787379892, 2182075161357078803]]]
  hmulB := by decide  
  f := ![![![-1101044581, -1729528734, 723882050]], ![![612007703, -1020476621, 355133238]], ![![-2422970961, -40846722, 153847685]]]
  g := ![![![-142491937091926549, 236515783009740690, 124491568867092358], ![-954633491268619273, 1584552026470505065, 834038917896314428], ![-2497583727568702347, 4145623836787379892, 2182075161357078803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1101044581, 1729528734, -723882050]] ![![2194542516081522829, 236515783009740690, 124491568867092358]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179884532527, -19386970519, -10204453778]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-179884532527, -19386970519, -10204453778]] 
 ![![73, 0, 0], ![0, 73, 0], ![63, 66, 1]] where
  M :=![![![-179884532527, -19386970519, -10204453778], ![-1205147482841, -129884200674, -68365365335], ![-3152997218298, -339812785785, -178862595490]]]
  hmulB := by decide  
  f := ![![![-378045, 60460, -1541]], ![![-245380, -433882, 179839]], ![![-450432, -343407, 156956]]]
  g := ![![![6342411719, 8960369573, -10204453778], ![42491377168, 60030546732, -68365365335], ![111169127364, 157056418035, -178862595490]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [33, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 72], [0, 1]]
 g := ![![[70, 9], [36], [57], [5, 69], [19], [1]], ![[12, 64], [36], [57], [47, 4], [19], [1]]]
 h' := ![![[26, 72], [3, 70], [13, 6], [54, 35], [24, 19], [40, 26], [0, 1]], ![[0, 1], [71, 3], [23, 67], [15, 38], [7, 54], [59, 47], [26, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [3, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [33, 47, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2479, 900, -212]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![149, 204, -212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![378045, -60460, 1541]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![378045, -60460, 1541]] 
 ![![73, 0, 0], ![20, 1, 0], ![19, 0, 1]] where
  M :=![![![378045, -60460, 1541], ![245380, 433882, -179839], ![-7130379, 241479, 314503]]]
  hmulB := by decide  
  f := ![![![179884532527, 19386970519, 10204453778]], ![![65792303197, 7090734398, 3732252615]], ![![90011004607, 9700893502, 5106126264]]]
  g := ![![![21342, -60460, 1541], ![-68703, 433882, -179839], ![-245692, 241479, 314503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-179884532527, -19386970519, -10204453778]] ![![378045, -60460, 1541]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![465370729340200, 50155110522189, 26399457643605]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![465370729340200, 50155110522189, 26399457643605]] 
 ![![79, 0, 0], ![15, 1, 0], ![35, 0, 1]] where
  M :=![![![465370729340200, 50155110522189, 26399457643605], ![3117779806710411, 336017245887196, 176864789210172], ![8156969331794685, 879113516534028, 462726924575179]]]
  hmulB := by decide  
  f := ![![![173775268, 944109, -10275072]], ![![17375649, 2757190, -2045175]], ![![67887932, -4690080, -2080481]]]
  g := ![![![-15328315772390, 50155110522189, 26399457643605], ![-102692993720931, 336017245887196, 176864789210172], ![-268673111093000, 879113516534028, 462726924575179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1292452222652, 139293427766, 73317971151]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1292452222652, 139293427766, 73317971151]] 
 ![![79, 0, 0], ![32, 1, 0], ![64, 0, 1]] where
  M :=![![![1292452222652, 139293427766, 73317971151], ![8658863110354, 933204881433, 491198254449], ![22653966995151, 2441520591591, 1285109708116]]]
  hmulB := by decide  
  f := ![![![-9928131, 1242385, 91551]], ![![-3898183, 358369, 85422]], ![![-6062007, 1004506, -38096]]]
  g := ![![![-99459336956, 139293427766, 73317971151], ![-666333941522, 933204881433, 491198254449], ![-1743312826015, 2441520591591, 1285109708116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![465370729340200, 50155110522189, 26399457643605]] ![![1292452222652, 139293427766, 73317971151]]
  ![![1633808111937348338048014661, 176082897483574308438535592, 92682339755274449251037241]] where
 M := ![![![1633808111937348338048014661, 176082897483574308438535592, 92682339755274449251037241]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![1633808111937348338048014661, 176082897483574308438535592, 92682339755274449251037241]] ![![1292452222652, 139293427766, 73317971151]]
  ![![79, 0, 0]] where
 M := ![![![5735919296894419013075544221850152438931, 618185992681523661112859009638915381093, 325386082489954889471306271755937841575]]]
 hmul := by decide  
 g := ![![![![72606573378410367254120812934812056189, 7825139147867388115352645691631840267, 4118811170758922651535522427290352425]]]]
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


lemma PB177I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB177I1 : PrimesBelowBoundCertificateInterval O 31 79 177 where
  m := 11
  g := ![1, 2, 3, 2, 2, 3, 2, 3, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB177I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
      exact NI41N1
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
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N1
      exact NI79N1
  β := ![I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N0, I59N1, I59N2, I61N1, I67N0, I67N1, I67N2, I71N1, I73N1, I79N0, I79N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [I73N1], [I79N0, I79N1, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
