
import IdealArithmetic.Examples.NF3_1_592328_1.RI3_1_592328_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-22, -8, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-22, -8, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 29, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-22, -8, 1], ![-217, -15, -49], ![1652, -220, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -29, 37]], ![![-1, -1, 1], ![14, 38, -49], ![41, -13, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [7, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36], [0, 1]]
 g := ![![[12, 16], [21], [30, 7], [26], [1]], ![[0, 21], [21], [34, 30], [26], [1]]]
 h' := ![![[27, 36], [34, 33], [12, 24], [15, 28], [30, 27], [0, 1]], ![[0, 1], [0, 4], [31, 13], [31, 9], [19, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [7, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2342, -1188, 1462]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-656, -1178, 1462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![3, 14, 6], ![-193, 23, 11]]]
  hmulB := by decide  
  f := ![![![2563, 13771, 5916], ![1221, -36482, 0]], ![![825, 4455, 1914], ![408, -11803, 0]], ![![1936, 10421, 4477], ![935, -27608, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-9, 14, 6], ![-21, 23, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-22, -8, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-814, -296, 37], ![-481, -111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-22, -8, 1]], ![![-13, -3, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [9, 15, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 29], [27, 37, 12], [0, 1]]
 g := ![![[4, 32, 33], [0, 18], [15, 2], [25, 32, 1], []], ![[40, 40, 4, 30], [17, 36], [19, 21], [12, 24, 35, 13], [26, 21]], ![[17, 6, 17, 6], [16, 16], [9, 21], [9, 39, 21, 26], [2, 21]]]
 h' := ![![[5, 3, 29], [33, 14, 22], [19, 37, 31], [21, 34, 24], [0, 0, 1], [0, 1]], ![[27, 37, 12], [15, 18, 31], [39, 25, 6], [13, 5, 29], [37, 25, 37], [5, 3, 29]], ![[0, 1], [22, 9, 29], [17, 20, 4], [4, 2, 29], [14, 16, 3], [27, 37, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 39], []]
 b := ![[], [17, 33, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [9, 15, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7658021, -1702566, 745421]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![186781, -41526, 18181]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![3, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![3, 1, 0]] 
 ![![43, 0, 0], ![3, 1, 0], ![41, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![3, 1, 0], ![3, 5, 6], ![-193, 23, 2]]]
  hmulB := by decide  
  f := ![![![949, 1592, 1914], ![129, -13717, 0]], ![![63, 109, 132], ![44, -946, 0]], ![![905, 1518, 1825], ![121, -13079, 0]]]
  g := ![![![1, 0, 0], ![-3, 43, 0], ![-41, 0, 43]], ![![0, 1, 0], ![-6, 5, 6], ![-8, 23, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, 1, 0]] 
 ![![43, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, 1, 0], ![3, 7, 6], ![-193, 23, 4]]]
  hmulB := by decide  
  f := ![![![1755, 4178, 3588], ![344, -25714, 0]], ![![202, 482, 414], ![44, -2967, 0]], ![![365, 874, 751], ![92, -5382, 0]]]
  g := ![![![1, 0, 0], ![-5, 43, 0], ![-9, 0, 43]], ![![0, 1, 0], ![-2, 7, 6], ![-8, 23, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-500465197718766, 118518555588371, 56615392520912]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-500465197718766, 118518555588371, 56615392520912]] 
 ![![43, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![-500465197718766, 118518555588371, 56615392520912], ![-10571215089770903, 1038725941438952, 654495941009314], ![-16759618836297107, 687772647779701, 683170274673839]]]
  hmulB := by decide  
  f := ![![![-259482280414647960631068841614, 42029835756059345004754718957, -18762036670655448972829723270]], ![![-118028719753333743597347438765, 19117789846009607748023660596, -8534144083611017350577966376]], ![![-434906360814735459902524247561, 70444281918207429843910099984, -31446189993660754607309024737]]]
  g := ![![![-148800093974732, 118518555588371, 56615392520912], ![-1569447980279131, 1038725941438952, 654495941009314], ![-1457872277326596, 687772647779701, 683170274673839]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![3, 1, 0]] ![![43, 0, 0], ![5, 1, 0]]
  ![![-259482280414647960631068841614, 42029835756059345004754718957, -18762036670655448972829723270]] where
 M := ![![![1849, 0, 0], ![215, 43, 0]], ![![129, 43, 0], ![18, 10, 6]]]
 hmul := by decide  
 g := ![![![![-21520003501906938, 5096297890299953, 2434461878399216]], ![![-13073541078364733, 1631318719380807, 937572903613874]]], ![![![-12072610682927201, 1394281608204065, 824342118572050]], ![![-5006470638940220, 387144867480428, 271233909849130]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-259482280414647960631068841614, 42029835756059345004754718957, -18762036670655448972829723270]] ![![-500465197718766, 118518555588371, 56615392520912]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-35, 11, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-35, 11, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![12, 11, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-35, 11, 1], ![-160, 10, 65], ![-2015, 217, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -11, 47]], ![![-1, 0, 1], ![-20, -15, 65], ![-37, 10, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [3, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46], [0, 1]]
 g := ![![[12, 16], [46, 7], [2, 14], [43, 27], [1]], ![[0, 31], [29, 40], [15, 33], [11, 20], [1]]]
 h' := ![![[11, 46], [3, 4], [41, 30], [12, 25], [44, 11], [0, 1]], ![[0, 1], [0, 43], [42, 17], [5, 22], [24, 36], [11, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [7, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [3, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-743814, -773926, 927342]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-252594, -233504, 927342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-18, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-18, 1, 0]] 
 ![![47, 0, 0], ![29, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-18, 1, 0], ![3, -16, 6], ![-193, 23, -19]]]
  hmulB := by decide  
  f := ![![![1348, -8514, 3198], ![-658, -25051, 0]], ![![823, -5239, 1968], ![-422, -15416, 0]], ![![670, -4167, 1565], ![-295, -12259, 0]]]
  g := ![![![1, 0, 0], ![-29, 47, 0], ![-23, 0, 47]], ![![-1, 1, 0], ![7, -16, 6], ![-9, 23, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-35, 11, 1]] ![![47, 0, 0], ![-18, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-846, 47, 0]], ![![-1645, 517, 47], ![470, -188, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-18, 1, 0]]], ![![![-35, 11, 1]], ![![10, -4, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-24, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-24, 1, 0]] 
 ![![53, 0, 0], ![29, 1, 0], ![45, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-24, 1, 0], ![3, -22, 6], ![-193, 23, -25]]]
  hmulB := by decide  
  f := ![![![691, -6285, 1716], ![-371, -15158, 0]], ![![373, -3428, 936], ![-211, -8268, 0]], ![![579, -5336, 1457], ![-332, -12870, 0]]]
  g := ![![![1, 0, 0], ![-29, 53, 0], ![-45, 0, 53]], ![![-1, 1, 0], ![7, -22, 6], ![5, 23, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, 1, 0]] 
 ![![53, 0, 0], ![47, 1, 0], ![23, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, 1, 0], ![3, -4, 6], ![-193, 23, -7]]]
  hmulB := by decide  
  f := ![![![3901, -5270, 7920], ![-530, -69960, 0]], ![![3457, -4671, 7020], ![-476, -62010, 0]], ![![1693, -2287, 3437], ![-229, -30360, 0]]]
  g := ![![![1, 0, 0], ![-47, 53, 0], ![-23, 0, 53]], ![![-1, 1, 0], ![1, -4, 6], ![-21, 23, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-24, 1, 0]] ![![53, 0, 0], ![-24, 1, 0]]
  ![![53, 0, 0], ![-36, 10, 1]] where
 M := ![![![2809, 0, 0], ![-1272, 53, 0]], ![![-1272, 53, 0], ![579, -46, 6]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![12, -9, -1], ![53, 0, 0]]], ![![![12, -9, -1], ![53, 0, 0]], ![![15, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-36, 10, 1]] ![![53, 0, 0], ![-6, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-318, 53, 0]], ![![-1908, 530, 53], ![53, -53, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-6, 1, 0]]], ![![![-36, 10, 1]], ![![1, -1, 1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, 9, 2]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![52, 9, 2]] 
 ![![59, 0, 0], ![0, 59, 0], ![26, 34, 1]] where
  M :=![![![52, 9, 2], ![-359, 116, 52], ![-1521, 135, 89]]]
  hmulB := by decide  
  f := ![![![56, -9, 4]], ![![-799, 130, -58]], ![![-399, 65, -29]]]
  g := ![![![0, -1, 2], ![-29, -28, 52], ![-65, -49, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [1, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 58], [0, 1]]
 g := ![![[20, 1], [20, 1], [36], [4, 19], [39, 1]], ![[0, 58], [0, 58], [36], [37, 40], [19, 58]]]
 h' := ![![[39, 58], [39, 58], [39, 58], [55, 6], [20, 45], [0, 1]], ![[0, 1], [0, 1], [0, 1], [53, 53], [5, 14], [39, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [22, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [1, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1855, -3692, 3775]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1695, -2238, 3775]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, -9, 4]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![56, -9, 4]] 
 ![![59, 0, 0], ![33, 1, 0], ![44, 0, 1]] where
  M :=![![![56, -9, 4], ![-799, 130, -58], ![2169, -351, 157]]]
  hmulB := by decide  
  f := ![![![52, 9, 2]], ![![23, 7, 2]], ![![13, 9, 3]]]
  g := ![![![3, -9, 4], ![-43, 130, -58], ![116, -351, 157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![52, 9, 2]] ![![56, -9, 4]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-20, 30, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-20, 30, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![41, 30, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-20, 30, 1], ![-103, 63, 179], ![-5682, 654, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -30, 61]], ![![-1, 0, 1], ![-122, -87, 179], ![-75, 24, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [13, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 60], [0, 1]]
 g := ![![[42, 47], [19], [27, 13], [55, 16], [3, 1]], ![[0, 14], [19], [5, 48], [42, 45], [6, 60]]]
 h' := ![![[3, 60], [39, 48], [15, 18], [17, 14], [22, 57], [0, 1]], ![[0, 1], [0, 13], [8, 43], [59, 47], [10, 4], [3, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [51, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [13, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2528, -1332, 1078]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-766, -552, 1078]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![4, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![4, 1, 0]] 
 ![![61, 0, 0], ![4, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![4, 1, 0], ![3, 6, 6], ![-193, 23, 3]]]
  hmulB := by decide  
  f := ![![![821, 1654, 1656], ![122, -16836, 0]], ![![50, 107, 108], ![62, -1098, 0]], ![![363, 732, 733], ![60, -7452, 0]]]
  g := ![![![1, 0, 0], ![-4, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-3, 6, 6], ![-6, 23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-20, 30, 1]] ![![61, 0, 0], ![4, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![244, 61, 0]], ![![-1220, 1830, 61], ![-183, 183, 183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![4, 1, 0]]], ![![![-20, 30, 1]], ![![-3, 3, 3]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [37, 28, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30, 22], [23, 36, 45], [0, 1]]
 g := ![![[32, 52, 19], [40, 34, 1], [52, 4], [55, 35], [45, 1], []], ![[36, 24, 58, 29], [36, 65, 15, 26], [17, 37], [21, 14], [59, 23], [52, 15]], ![[14, 46, 18, 61], [59, 38, 3, 7], [0, 59], [66, 16], [19, 29], [29, 15]]]
 h' := ![![[22, 30, 22], [61, 22, 32], [16, 28, 1], [8, 35, 2], [10, 43, 54], [0, 0, 1], [0, 1]], ![[23, 36, 45], [25, 55, 28], [63, 15, 49], [42, 3, 38], [45, 22, 9], [34, 46, 36], [22, 30, 22]], ![[0, 1], [43, 57, 7], [49, 24, 17], [60, 29, 27], [31, 2, 4], [59, 21, 30], [23, 36, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 19], []]
 b := ![[], [54, 27, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [37, 28, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![307018455, -102466182, 49564523]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4582365, -1529346, 739769]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [5, 53, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 41, 24], [31, 29, 47], [0, 1]]
 g := ![![[35, 0, 36], [12, 9, 48], [65, 50, 8], [68, 58], [69, 1], []], ![[45, 43, 27, 54], [40, 16, 8, 64], [19, 9, 35, 2], [45, 10], [53, 60], [35, 8]], ![[67, 16, 1, 11], [9, 33, 33, 69], [45, 67, 55, 70], [12, 38], [34, 48], [12, 8]]]
 h' := ![![[38, 41, 24], [11, 6, 6], [30, 16, 41], [44, 43, 47], [10, 30, 22], [0, 0, 1], [0, 1]], ![[31, 29, 47], [43, 46, 34], [56, 23, 11], [48, 7, 52], [29, 47, 9], [62, 14, 29], [38, 41, 24]], ![[0, 1], [65, 19, 31], [50, 32, 19], [59, 21, 43], [30, 65, 40], [49, 57, 41], [31, 29, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 38], []]
 b := ![[], [52, 11, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [5, 53, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258653, 46008, -19170]
  a := ![-2, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3643, 648, -270]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [9, 42, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 14, 66], [17, 58, 7], [0, 1]]
 g := ![![[41, 43, 27], [53, 3], [62, 65], [16, 14, 69], [13, 1], []], ![[61, 60, 9, 58], [3, 1], [54, 16], [68, 37, 23, 17], [8, 6], [3, 49]], ![[63, 44, 62, 63], [60, 35], [25, 35], [40, 45, 16, 43], [25, 50], [62, 49]]]
 h' := ![![[69, 14, 66], [58, 30, 63], [30, 49, 21], [2, 43, 24], [29, 29, 54], [0, 0, 1], [0, 1]], ![[17, 58, 7], [48, 56, 13], [41, 5, 72], [4, 1, 69], [49, 21, 9], [62, 51, 58], [69, 14, 66]], ![[0, 1], [46, 60, 70], [32, 19, 53], [44, 29, 53], [12, 23, 10], [23, 22, 14], [17, 58, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 34], []]
 b := ![[], [31, 25, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [9, 42, 60, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12179977, -3344860, 1671116]
  a := ![7, 5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![166849, -45820, 22892]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 32, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 32, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![21, 32, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 32, 1], ![-97, 108, 191], ![-6068, 700, 12]]]
  hmulB := by decide  
  f := ![![![-20, -32, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -32, 79]], ![![0, 0, 1], ![-52, -76, 191], ![-80, 4, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [43, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 78], [0, 1]]
 g := ![![[38, 49], [21, 72], [21, 67], [15, 50], [72], [1]], ![[78, 30], [4, 7], [37, 12], [1, 29], [72], [1]]]
 h' := ![![[25, 78], [45, 7], [45, 25], [66, 15], [17, 45], [36, 25], [0, 1]], ![[0, 1], [62, 72], [38, 54], [46, 64], [36, 34], [29, 54], [25, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [59, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [43, 54, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4972, -4770, 4665]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1303, -1950, 4665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-33, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-33, 1, 0]] 
 ![![79, 0, 0], ![46, 1, 0], ![67, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-33, 1, 0], ![3, -31, 6], ![-193, 23, -34]]]
  hmulB := by decide  
  f := ![![![2590, -33213, 6432], ![-1501, -84688, 0]], ![![1510, -19333, 3744], ![-868, -49296, 0]], ![![2197, -28168, 5455], ![-1272, -71824, 0]]]
  g := ![![![1, 0, 0], ![-46, 79, 0], ![-67, 0, 79]], ![![-1, 1, 0], ![13, -31, 6], ![13, 23, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![21, 32, 1]] ![![79, 0, 0], ![-33, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2607, 79, 0]], ![![1659, 2528, 79], ![-790, -948, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-33, 1, 0]]], ![![![21, 32, 1]], ![![-10, -12, 2]]]]
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


lemma PB218I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB218I1 : PrimesBelowBoundCertificateInterval O 31 79 218 where
  m := 11
  g := ![2, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB218I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI37N1
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
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N0, I43N1, I43N2, I47N1, I53N0, I53N1, I59N1, I61N1, I79N1]
  Il := ![[I37N1], [], [I43N0, I43N1, I43N2], [I47N1], [I53N0, I53N0, I53N1], [I59N1], [I61N1], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
