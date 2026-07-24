
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![0, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![0, 1, 0]] 
 ![![83, 0, 0], ![0, 1, 0], ![15, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![-1, 4, 11], ![106, -23, -4]]]
  hmulB := by decide  
  f := ![![![0, 3, 11], ![83, -83, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![60, -15, 0]]]
  g := ![![![1, 0, 0], ![0, 83, 0], ![-15, 0, 83]], ![![0, 1, 0], ![-2, 4, 11], ![2, -23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![29, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![29, 1, 0]] 
 ![![83, 0, 0], ![29, 1, 0], ![11, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![29, 1, 0], ![-1, 33, 11], ![106, -23, 25]]]
  hmulB := by decide  
  f := ![![![3243, -106028, -35343], ![-83, 266679, 0]], ![![1122, -37026, -12342], ![1, 93126, 0]], ![![427, -14052, -4684], ![-3, 35343, 0]]]
  g := ![![![1, 0, 0], ![-29, 83, 0], ![-11, 0, 83]], ![![0, 1, 0], ![-13, 33, 11], ![6, -23, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-29, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-29, 1, 0]] 
 ![![83, 0, 0], ![54, 1, 0], ![17, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-29, 1, 0], ![-1, -25, 11], ![106, -23, -33]]]
  hmulB := by decide  
  f := ![![![1001, 25000, -11000], ![0, 83000, 0]], ![![651, 16250, -7150], ![1, 53950, 0]], ![![219, 5120, -2253], ![40, 17000, 0]]]
  g := ![![![1, 0, 0], ![-54, 83, 0], ![-17, 0, 83]], ![![-1, 1, 0], ![14, -25, 11], ![23, -23, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![0, 1, 0]] ![![83, 0, 0], ![29, 1, 0]]
  ![![83, 0, 0], ![15, 3, 1]] where
 M := ![![![6889, 0, 0], ![2407, 83, 0]], ![![0, 83, 0], ![-1, 33, 11]]]
 hmul := by decide  
 g := ![![![![68, -3, -1], ![83, 0, 0]], ![![14, -2, -1], ![83, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![15, 3, 1]] ![![83, 0, 0], ![-29, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2407, 83, 0]], ![![1245, 249, 83], ![-332, -83, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-29, 1, 0]]], ![![![15, 3, 1]], ![![-4, -1, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [63, 85, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 71, 15], [22, 17, 74], [0, 1]]
 g := ![![[38, 52, 69], [70, 8], [86, 64], [71, 13, 22], [75, 31, 1], []], ![[29, 25, 18, 28], [73, 87], [53, 64], [12, 50, 42, 3], [22, 65, 19, 63], [27, 47]], ![[70, 87, 78, 70], [18, 11], [], [23, 68, 25, 43], [82, 1, 23, 35], [57, 47]]]
 h' := ![![[9, 71, 15], [76, 43, 43], [6, 0, 50], [66, 63, 81], [81, 38, 72], [0, 0, 1], [0, 1]], ![[22, 17, 74], [45, 31, 41], [85, 15, 49], [65, 74, 8], [17, 14, 14], [71, 27, 17], [9, 71, 15]], ![[0, 1], [31, 15, 5], [50, 74, 79], [53, 41], [69, 37, 3], [8, 62, 71], [22, 17, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 80], []]
 b := ![[], [22, 55, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [63, 85, 58, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-313636, 126647, -805717]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3524, 1423, -9053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![49, 39, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![49, 39, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![49, 39, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![49, 39, 1], ![67, 182, 425], ![4059, -879, -127]]]
  hmulB := by decide  
  f := ![![![-48, -39, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -39, 97]], ![![0, 0, 1], ![-214, -169, 425], ![106, 42, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [58, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 96], [0, 1]]
 g := ![![[8, 47], [31], [48], [4], [25], [21, 1]], ![[25, 50], [31], [48], [4], [25], [42, 96]]]
 h' := ![![[21, 96], [36, 12], [31, 82], [83, 40], [11, 95], [43, 92], [0, 1]], ![[0, 1], [94, 85], [7, 15], [50, 57], [66, 2], [35, 5], [21, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [79, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [58, 76, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15986, 6138, -19653]
  a := ![-3, 9, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9763, 7965, -19653]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-37, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-37, 1, 0]] 
 ![![97, 0, 0], ![60, 1, 0], ![30, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-37, 1, 0], ![-1, -33, 11], ![106, -23, -41]]]
  hmulB := by decide  
  f := ![![![-6576, -220707, 73568], ![291, -648736, 0]], ![![-4061, -136490, 45496], ![195, -401192, 0]], ![![-2030, -68260, 22753], ![100, -200640, 0]]]
  g := ![![![1, 0, 0], ![-60, 97, 0], ![-30, 0, 97]], ![![-1, 1, 0], ![17, -33, 11], ![28, -23, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![49, 39, 1]] ![![97, 0, 0], ![-37, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3589, 97, 0]], ![![4753, 3783, 97], ![-1746, -1261, 388]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-37, 1, 0]]], ![![![49, 39, 1]], ![![-18, -13, 4]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-4, 12, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-4, 12, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![97, 12, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-4, 12, 1], ![94, 21, 128], ![1197, -258, -72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -12, 101]], ![![-1, 0, 1], ![-122, -15, 128], ![81, 6, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [34, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 100], [0, 1]]
 g := ![![[82, 96], [47], [76, 49], [56], [76], [40, 1]], ![[84, 5], [47], [16, 52], [56], [76], [80, 100]]]
 h' := ![![[40, 100], [65, 55], [42, 42], [48, 94], [29, 64], [54, 51], [0, 1]], ![[0, 1], [43, 46], [5, 59], [71, 7], [64, 37], [74, 50], [40, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [21, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [34, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![639032, -116165, -108046]
  a := ![1, -67, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110094, 11687, -108046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-27, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-27, 1, 0]] 
 ![![101, 0, 0], ![74, 1, 0], ![72, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-27, 1, 0], ![-1, -23, 11], ![106, -23, -31]]]
  hmulB := by decide  
  f := ![![![-7916, -183957, 87978], ![303, -807798, 0]], ![![-5777, -134760, 64449], ![304, -591759, 0]], ![![-5634, -131138, 62717], ![250, -575856, 0]]]
  g := ![![![1, 0, 0], ![-74, 101, 0], ![-72, 0, 101]], ![![-1, 1, 0], ![9, -23, 11], ![40, -23, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-4, 12, 1]] ![![101, 0, 0], ![-27, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2727, 101, 0]], ![![-404, 1212, 101], ![202, -303, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-27, 1, 0]]], ![![![-4, 12, 1]], ![![2, -3, 1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![26, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![26, 1, 0]] 
 ![![103, 0, 0], ![26, 1, 0], ![32, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![26, 1, 0], ![-1, 30, 11], ![106, -23, 22]]]
  hmulB := by decide  
  f := ![![![-425, 11999, 4400], ![103, -41200, 0]], ![![-126, 2999, 1100], ![104, -10300, 0]], ![![-128, 3728, 1367], ![16, -12800, 0]]]
  g := ![![![1, 0, 0], ![-26, 103, 0], ![-32, 0, 103]], ![![0, 1, 0], ![-11, 30, 11], ![0, -23, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![51, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![51, 1, 0]] 
 ![![103, 0, 0], ![51, 1, 0], ![82, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![51, 1, 0], ![-1, 55, 11], ![106, -23, 47]]]
  hmulB := by decide  
  f := ![![![6971, -377738, -75548], ![-206, 707404, 0]], ![![3451, -186999, -37400], ![-102, 350200, 0]], ![![5522, -300724, -60145], ![-108, 563176, 0]]]
  g := ![![![1, 0, 0], ![-51, 103, 0], ![-82, 0, 103]], ![![0, 1, 0], ![-36, 55, 11], ![-25, -23, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![26, 1, 0]] ![![103, 0, 0], ![26, 1, 0]]
  ![![103, 0, 0], ![52, -23, 1]] where
 M := ![![![10609, 0, 0], ![2678, 103, 0]], ![![2678, 103, 0], ![675, 56, 11]]]
 hmul := by decide  
 g := ![![![![51, 23, -1], ![103, 0, 0]], ![![-26, 24, -1], ![103, 0, 0]]], ![![![-26, 24, -1], ![103, 0, 0]], ![![1, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![52, -23, 1]] ![![103, 0, 0], ![51, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![5253, 103, 0]], ![![5356, -2369, 103], ![2781, -1236, -206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![51, 1, 0]]], ![![![52, -23, 1]], ![![27, -12, -2]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [53, 50, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 83, 30], [46, 23, 77], [0, 1]]
 g := ![![[3, 21, 25], [81, 81, 34], [29, 83], [31, 105, 25], [63, 36], [1]], ![[98, 75, 75, 102], [65, 93, 100, 12], [73, 16], [52, 93, 21, 53], [35, 19], [10, 29, 40, 36]], ![[103, 3, 70, 31], [52, 78, 78, 70], [95, 39], [50, 46, 86, 22], [18, 23], [57, 28, 42, 71]]]
 h' := ![![[55, 83, 30], [94, 92, 5], [14, 24, 26], [69, 79, 46], [5, 28, 102], [54, 57, 101], [0, 1]], ![[46, 23, 77], [76, 36, 93], [52, 29, 34], [47, 88, 4], [96, 80, 83], [102, 48, 74], [55, 83, 30]], ![[0, 1], [96, 86, 9], [94, 54, 47], [97, 47, 57], [66, 106, 29], [48, 2, 39], [46, 23, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 71], []]
 b := ![[], [3, 90, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [53, 50, 6, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43442000, 10604342, -14887980]
  a := ![3, -10, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-406000, 99106, -139140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![9, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![9, 1, 0]] 
 ![![109, 0, 0], ![9, 1, 0], ![19, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![9, 1, 0], ![-1, 13, 11], ![106, -23, 5]]]
  hmulB := by decide  
  f := ![![![10504, -136185, -115236], ![-327, 1141884, 0]], ![![864, -11232, -9504], ![1, 94176, 0]], ![![1828, -23739, -20087], ![-21, 199044, 0]]]
  g := ![![![1, 0, 0], ![-9, 109, 0], ![-19, 0, 109]], ![![0, 1, 0], ![-3, 13, 11], ![2, -23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![49, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![49, 1, 0]] 
 ![![109, 0, 0], ![49, 1, 0], ![71, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![49, 1, 0], ![-1, 53, 11], ![106, -23, 45]]]
  hmulB := by decide  
  f := ![![![2938, -155661, -32307], ![0, 320133, 0]], ![![1320, -69960, -14520], ![1, 143880, 0]], ![![1907, -101394, -21044], ![15, 208527, 0]]]
  g := ![![![1, 0, 0], ![-49, 109, 0], ![-71, 0, 109]], ![![0, 1, 0], ![-31, 53, 11], ![-18, -23, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![51, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![51, 1, 0]] 
 ![![109, 0, 0], ![51, 1, 0], ![62, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![51, 1, 0], ![-1, 55, 11], ![106, -23, 47]]]
  hmulB := by decide  
  f := ![![![4268, -231879, -46376], ![-109, 459544, 0]], ![![1972, -108460, -21692], ![1, 214948, 0]], ![![2401, -131895, -26379], ![-5, 261392, 0]]]
  g := ![![![1, 0, 0], ![-51, 109, 0], ![-62, 0, 109]], ![![0, 1, 0], ![-32, 55, 11], ![-15, -23, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![9, 1, 0]] ![![109, 0, 0], ![49, 1, 0]]
  ![![109, 0, 0], ![40, -34, 1]] where
 M := ![![![11881, 0, 0], ![5341, 109, 0]], ![![981, 109, 0], ![440, 62, 11]]]
 hmul := by decide  
 g := ![![![![69, 34, -1], ![109, 0, 0]], ![![9, 35, -1], ![109, 0, 0]]], ![![![-31, 35, -1], ![109, 0, 0]], ![![0, 4, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![40, -34, 1]] ![![109, 0, 0], ![51, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5559, 109, 0]], ![![4360, -3706, 109], ![2180, -1853, -327]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![51, 1, 0]]], ![![![40, -34, 1]], ![![20, -17, -3]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![104, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![-1, 23, 11], ![106, -23, 15]]]
  hmulB := by decide  
  f := ![![![-252, 5381, 2574], ![113, -26442, 0]], ![![-58, 896, 429], ![114, -4407, 0]], ![![-221, 4953, 2369], ![39, -24336, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-104, 0, 113]], ![![0, 1, 0], ![-14, 23, 11], ![-9, -23, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-17, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-17, 1, 0]] 
 ![![113, 0, 0], ![96, 1, 0], ![62, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-17, 1, 0], ![-1, -13, 11], ![106, -23, -21]]]
  hmulB := by decide  
  f := ![![![-8225, -107604, 91047], ![339, -935301, 0]], ![![-6979, -91406, 77341], ![340, -794503, 0]], ![![-4502, -59040, 49955], ![258, -513174, 0]]]
  g := ![![![1, 0, 0], ![-96, 113, 0], ![-62, 0, 113]], ![![-1, 1, 0], ![5, -13, 11], ![32, -23, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-2, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-2, 1, 0]] 
 ![![113, 0, 0], ![111, 1, 0], ![103, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-2, 1, 0], ![-1, 2, 11], ![106, -23, -6]]]
  hmulB := by decide  
  f := ![![![-4251, 8510, 46816], ![226, -480928, 0]], ![![-4175, 8358, 45980], ![227, -472340, 0]], ![![-3875, 7757, 42673], ![195, -438368, 0]]]
  g := ![![![1, 0, 0], ![-111, 113, 0], ![-103, 0, 113]], ![![-1, 1, 0], ![-12, 2, 11], ![29, -23, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![19, 1, 0]] ![![113, 0, 0], ![-17, 1, 0]]
  ![![113, 0, 0], ![63, -20, 1]] where
 M := ![![![12769, 0, 0], ![-1921, 113, 0]], ![![2147, 113, 0], ![-324, 6, 11]]]
 hmul := by decide  
 g := ![![![![50, 20, -1], ![113, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![-44, 21, -1], ![113, 0, 0]], ![![-9, 2, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![63, -20, 1]] ![![113, 0, 0], ![-2, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-226, 113, 0]], ![![7119, -2260, 113], ![0, 0, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-2, 1, 0]]], ![![![63, -20, 1]], ![![0, 0, -2]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![44, 54, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![44, 54, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![44, 54, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![44, 54, 1], ![52, 237, 590], ![5649, -1224, -192]]]
  hmulB := by decide  
  f := ![![![-43, -54, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -54, 127]], ![![0, 0, 1], ![-204, -249, 590], ![111, 72, -192]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [106, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 126], [0, 1]]
 g := ![![[123, 115], [49, 115], [32, 107], [74, 35], [6, 82], [43, 1]], ![[115, 12], [41, 12], [61, 20], [55, 92], [103, 45], [86, 126]]]
 h' := ![![[43, 126], [13, 49], [37, 78], [30, 108], [126, 17], [14, 92], [0, 1]], ![[0, 1], [88, 78], [89, 49], [102, 19], [95, 110], [33, 35], [43, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [124, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [106, 84, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2751, -682, -3531]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1245, 1496, -3531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![45, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![45, 1, 0]] 
 ![![127, 0, 0], ![45, 1, 0], ![65, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![45, 1, 0], ![-1, 49, 11], ![106, -23, 41]]]
  hmulB := by decide  
  f := ![![![-2684, 129359, 29040], ![127, -335280, 0]], ![![-980, 45814, 10285], ![128, -118745, 0]], ![![-1390, 66207, 14863], ![111, -171600, 0]]]
  g := ![![![1, 0, 0], ![-45, 127, 0], ![-65, 0, 127]], ![![0, 1, 0], ![-23, 49, 11], ![-12, -23, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![44, 54, 1]] ![![127, 0, 0], ![45, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![5715, 127, 0]], ![![5588, 6858, 127], ![2032, 2667, 635]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![45, 1, 0]]], ![![![44, 54, 1]], ![![16, 21, 5]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![62, 22, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![62, 22, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![62, 22, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![62, 22, 1], ![84, 127, 238], ![2257, -488, -46]]]
  hmulB := by decide  
  f := ![![![-61, -22, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -22, 131]], ![![0, 0, 1], ![-112, -39, 238], ![39, 4, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [70, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 130], [0, 1]]
 g := ![![[10, 123], [83, 12], [48], [94], [39], [60], [1]], ![[108, 8], [67, 119], [48], [94], [39], [60], [1]]]
 h' := ![![[86, 130], [85, 75], [14, 55], [112, 21], [81, 116], [45, 63], [61, 86], [0, 1]], ![[0, 1], [116, 56], [28, 76], [84, 110], [101, 15], [92, 68], [121, 45], [86, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [27, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [70, 45, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49706, -7320, 1668]
  a := ![-1, 24, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-410, -336, 1668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![24, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![24, 1, 0]] 
 ![![131, 0, 0], ![24, 1, 0], ![46, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![24, 1, 0], ![-1, 28, 11], ![106, -23, 20]]]
  hmulB := by decide  
  f := ![![![-3218, 89459, 35145], ![131, -418545, 0]], ![![-609, 16379, 6435], ![132, -76635, 0]], ![![-1132, 31413, 12341], ![57, -146970, 0]]]
  g := ![![![1, 0, 0], ![-24, 131, 0], ![-46, 0, 131]], ![![0, 1, 0], ![-9, 28, 11], ![-2, -23, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![62, 22, 1]] ![![131, 0, 0], ![24, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3144, 131, 0]], ![![8122, 2882, 131], ![1572, 655, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![24, 1, 0]]], ![![![62, 22, 1]], ![![12, 5, 2]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-65, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-65, 1, 0]] 
 ![![137, 0, 0], ![72, 1, 0], ![38, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-65, 1, 0], ![-1, -61, 11], ![106, -23, -69]]]
  hmulB := by decide  
  f := ![![![4072, 248331, -44781], ![0, 557727, 0]], ![![2140, 130479, -23529], ![1, 293043, 0]], ![![1138, 68880, -12421], ![18, 154698, 0]]]
  g := ![![![1, 0, 0], ![-72, 137, 0], ![-38, 0, 137]], ![![-1, 1, 0], ![29, -61, 11], ![32, -23, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-47, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-47, 1, 0]] 
 ![![137, 0, 0], ![90, 1, 0], ![3, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-47, 1, 0], ![-1, -43, 11], ![106, -23, -51]]]
  hmulB := by decide  
  f := ![![![-7249, -315794, 80784], ![274, -1006128, 0]], ![![-4776, -207433, 53064], ![138, -660888, 0]], ![![-121, -6916, 1769], ![116, -22032, 0]]]
  g := ![![![1, 0, 0], ![-90, 137, 0], ![-3, 0, 137]], ![![-1, 1, 0], ![28, -43, 11], ![17, -23, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-25, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-25, 1, 0]] 
 ![![137, 0, 0], ![112, 1, 0], ![2, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-25, 1, 0], ![-1, -21, 11], ![106, -23, -29]]]
  hmulB := by decide  
  f := ![![![-13406, -283125, 148302], ![411, -1847034, 0]], ![![-10945, -231444, 121231], ![412, -1509877, 0]], ![![-176, -4134, 2165], ![114, -26964, 0]]]
  g := ![![![1, 0, 0], ![-112, 137, 0], ![-2, 0, 137]], ![![-1, 1, 0], ![17, -21, 11], ![20, -23, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-65, 1, 0]] ![![137, 0, 0], ![-47, 1, 0]]
  ![![137, 0, 0], ![41, 40, 1]] where
 M := ![![![18769, 0, 0], ![-6439, 137, 0]], ![![-8905, 137, 0], ![3054, -108, 11]]]
 hmul := by decide  
 g := ![![![![96, -40, -1], ![137, 0, 0]], ![![-47, 1, 0], ![0, 0, 0]]], ![![![-65, 1, 0], ![0, 0, 0]], ![![19, -4, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![41, 40, 1]] ![![137, 0, 0], ![-25, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3425, 137, 0]], ![![5617, 5480, 137], ![-959, -822, 411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-25, 1, 0]]], ![![![41, 40, 1]], ![![-7, -6, 3]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB245I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB245I2 : PrimesBelowBoundCertificateInterval O 79 137 245 where
  m := 11
  g := ![3, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB245I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N0, I83N1, I83N2, I97N1, I101N1, I103N0, I103N1, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N1], [I103N0, I103N0, I103N1], [], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
