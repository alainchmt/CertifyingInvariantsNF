
import IdealArithmetic.Examples.NF3_1_205556_1.RI3_1_205556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17051, 1198, 44]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-17051, 1198, 44]] 
 ![![83, 0, 0], ![0, 83, 0], ![52, 31, 1]] where
  M :=![![![-17051, 1198, 44], ![12496, -13575, 1198], ![340232, 107138, -13575]]]
  hmulB := by decide  
  f := ![![![673847, 252734, 24488]], ![![6954592, 2608399, 252734]], ![![3884444, 1456905, 141163]]]
  g := ![![![-233, -2, 44], ![-600, -611, 1198], ![12604, 6361, -13575]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [65, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 82], [0, 1]]
 g := ![![[74, 23], [28, 44], [70], [10], [42, 16], [1]], ![[0, 60], [38, 39], [70], [10], [23, 67], [1]]]
 h' := ![![[4, 82], [6, 40], [76, 58], [12, 53], [9, 33], [18, 4], [0, 1]], ![[0, 1], [0, 43], [59, 25], [58, 30], [58, 50], [34, 79], [4, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [34, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [65, 79, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![633, 363, 1]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 4, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-673847, -252734, -24488]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-673847, -252734, -24488]] 
 ![![83, 0, 0], ![52, 1, 0], ![35, 0, 1]] where
  M :=![![![-673847, -252734, -24488], ![-6954592, -2608399, -252734], ![-71776456, -26920578, -2608399]]]
  hmulB := by decide  
  f := ![![![17051, -1198, -44]], ![![10532, -587, -42]], ![![3091, -1796, 145]]]
  g := ![![![160547, -252734, -24488], ![1656962, -2608399, -252734], ![17101055, -26920578, -2608399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-17051, 1198, 44]] ![![-673847, -252734, -24488]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -11, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![7, -11, 1]] 
 ![![89, 0, 0], ![38, 1, 0], ![69, 0, 1]] where
  M :=![![![7, -11, 1], ![284, 86, -11], ![-3124, -585, 86]]]
  hmulB := by decide  
  f := ![![![-961, -361, -35]], ![![-522, -196, -19]], ![![-1897, -712, -69]]]
  g := ![![![4, -11, 1], ![-25, 86, -11], ![148, -585, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-27, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-27, 1, 0]] 
 ![![89, 0, 0], ![62, 1, 0], ![72, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-27, 1, 0], ![0, -27, 1], ![284, 79, -27]]]
  hmulB := by decide  
  f := ![![![1216, -45, 0], ![4005, 0, 0]], ![![892, -33, 0], ![2938, 0, 0]], ![![1008, -37, 0], ![3320, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 89, 0], ![-72, 0, 89]], ![![-1, 1, 0], ![18, -27, 1], ![-30, 79, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 1, 0]] 
 ![![89, 0, 0], ![78, 1, 0], ![57, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 1, 0], ![0, -11, 1], ![284, 79, -11]]]
  hmulB := by decide  
  f := ![![![914, -83, 0], ![7387, 0, 0]], ![![804, -73, 0], ![6498, 0, 0]], ![![596, -54, 0], ![4817, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 89, 0], ![-57, 0, 89]], ![![-1, 1, 0], ![9, -11, 1], ![-59, 79, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![7, -11, 1]] ![![89, 0, 0], ![-27, 1, 0]]
  ![![89, 0, 0], ![-47, 11, 1]] where
 M := ![![![623, -979, 89], ![95, 383, -38]]]
 hmul := by decide  
 g := ![![![![7, -11, 1], ![0, 0, 0]], ![![28, -2, -1], ![51, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-47, 11, 1]] ![![89, 0, 0], ![-11, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-979, 89, 0]], ![![-4183, 979, 89], ![801, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-11, 1, 0]]], ![![![-47, 11, 1]], ![![9, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6569, -1149, 173]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-6569, -1149, 173]] 
 ![![97, 0, 0], ![0, 97, 0], ![68, 27, 1]] where
  M :=![![![-6569, -1149, 173], ![49132, 7098, -1149], ![-326316, -41639, 7098]]]
  hmulB := by decide  
  f := ![![![-26169, -9815, -951]], ![![-270084, -101298, -9815]], ![![-122260, -45855, -4443]]]
  g := ![![![-189, -60, 173], ![1312, 393, -1149], ![-8340, -2405, 7098]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [50, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 96], [0, 1]]
 g := ![![[8, 33], [62], [50], [96], [9], [85, 1]], ![[0, 64], [62], [50], [96], [9], [73, 96]]]
 h' := ![![[85, 96], [22, 18], [55, 81], [18, 27], [68, 75], [18, 94], [0, 1]], ![[0, 1], [0, 79], [53, 16], [82, 70], [41, 22], [54, 3], [85, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [21, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [50, 12, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3369, 1588, 745]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-557, -191, 745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26169, 9815, 951]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![26169, 9815, 951]] 
 ![![97, 0, 0], ![70, 1, 0], ![47, 0, 1]] where
  M :=![![![26169, 9815, 951], ![270084, 101298, 9815], ![2787460, 1045469, 101298]]]
  hmulB := by decide  
  f := ![![![6569, 1149, -173]], ![![4234, 756, -113]], ![![6547, 986, -157]]]
  g := ![![![-7274, 9815, 951], ![-75073, 101298, 9815], ![-774808, 1045469, 101298]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-6569, -1149, 173]] ![![26169, 9815, 951]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![47, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![47, 1, 0]] 
 ![![101, 0, 0], ![47, 1, 0], ![13, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![47, 1, 0], ![0, 47, 1], ![284, 79, 47]]]
  hmulB := by decide  
  f := ![![![1270, 27, 0], ![-2727, 0, 0]], ![![564, 12, 0], ![-1211, 0, 0]], ![![116, 2, 0], ![-249, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 101, 0], ![-13, 0, 101]], ![![0, 1, 0], ![-22, 47, 1], ![-40, 79, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-39, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-39, 1, 0]] 
 ![![101, 0, 0], ![62, 1, 0], ![95, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-39, 1, 0], ![0, -39, 1], ![284, 79, -39]]]
  hmulB := by decide  
  f := ![![![2926, -75, 0], ![7575, 0, 0]], ![![1834, -47, 0], ![4748, 0, 0]], ![![2746, -70, 0], ![7109, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 101, 0], ![-95, 0, 101]], ![![-1, 1, 0], ![23, -39, 1], ![-9, 79, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1293, -485, -47]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-1293, -485, -47]] 
 ![![101, 0, 0], ![93, 1, 0], ![37, 0, 1]] where
  M :=![![![-1293, -485, -47], ![-13348, -5006, -485], ![-137740, -51663, -5006]]]
  hmulB := by decide  
  f := ![![![-3481, -251, 57]], ![![-3045, -221, 50]], ![![-1981, -128, 31]]]
  g := ![![![451, -485, -47], ![4655, -5006, -485], ![48041, -51663, -5006]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![47, 1, 0]] ![![101, 0, 0], ![-39, 1, 0]]
  ![![-3481, -251, 57]] where
 M := ![![![10201, 0, 0], ![-3939, 101, 0]], ![![4747, 101, 0], ![-1833, 8, 1]]]
 hmul := by decide  
 g := ![![![![-130593, -48985, -4747]], ![![37079, 13909, 1348]]], ![![![-74119, -27801, -2694]], ![![21045, 7894, 765]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-3481, -251, 57]] ![![-1293, -485, -47]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![1, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![1, 1, 0]] 
 ![![103, 0, 0], ![1, 1, 0], ![102, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![1, 1, 0], ![0, 1, 1], ![284, 79, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![103, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![102, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 103, 0], ![-102, 0, 103]], ![![0, 1, 0], ![-1, 1, 1], ![1, 79, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![50, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![50, 1, 0]] 
 ![![103, 0, 0], ![50, 1, 0], ![75, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![50, 1, 0], ![0, 50, 1], ![284, 79, 50]]]
  hmulB := by decide  
  f := ![![![1601, 32, 0], ![-3296, 0, 0]], ![![750, 15, 0], ![-1544, 0, 0]], ![![1125, 22, 0], ![-2316, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 103, 0], ![-75, 0, 103]], ![![0, 1, 0], ![-25, 50, 1], ![-72, 79, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -11, -1]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-31, -11, -1]] 
 ![![103, 0, 0], ![52, 1, 0], ![77, 0, 1]] where
  M :=![![![-31, -11, -1], ![-284, -110, -11], ![-3124, -1153, -110]]]
  hmulB := by decide  
  f := ![![![583, 57, -11]], ![![264, 26, -5]], ![![593, 56, -11]]]
  g := ![![![6, -11, -1], ![61, -110, -11], ![634, -1153, -110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![1, 1, 0]] ![![103, 0, 0], ![50, 1, 0]]
  ![![-583, -57, 11]] where
 M := ![![![10609, 0, 0], ![5150, 103, 0]], ![![103, 103, 0], ![50, 51, 1]]]
 hmul := by decide  
 g := ![![![![3193, 1133, 103]], ![![1834, 660, 61]]], ![![![315, 121, 12]], ![![186, 71, 7]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-583, -57, 11]] ![![-31, -11, -1]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-32, -49, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-32, -49, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![75, 58, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-32, -49, 1], ![284, 47, -49], ![-13916, -3587, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -58, 107]], ![![-1, -1, 1], ![37, 27, -49], ![-163, -59, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [31, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 106], [0, 1]]
 g := ![![[51, 56], [36, 92], [85], [61, 23], [100], [24, 1]], ![[4, 51], [104, 15], [85], [78, 84], [100], [48, 106]]]
 h' := ![![[24, 106], [61, 85], [88, 29], [35, 37], [28, 39], [5, 10], [0, 1]], ![[0, 1], [68, 22], [35, 78], [67, 70], [1, 68], [31, 97], [24, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [1, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [31, 83, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1753, 81, 125]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104, -67, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![49, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![49, 1, 0]] 
 ![![107, 0, 0], ![49, 1, 0], ![60, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![49, 1, 0], ![0, 49, 1], ![284, 79, 49]]]
  hmulB := by decide  
  f := ![![![1618, 33, 0], ![-3531, 0, 0]], ![![686, 14, 0], ![-1497, 0, 0]], ![![856, 17, 0], ![-1868, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 107, 0], ![-60, 0, 107]], ![![0, 1, 0], ![-23, 49, 1], ![-61, 79, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-32, -49, 1]] ![![107, 0, 0], ![49, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5243, 107, 0]], ![![-3424, -5243, 107], ![-1284, -2354, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![49, 1, 0]]], ![![![-32, -49, 1]], ![![-12, -22, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58269, -4871, 1019]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-58269, -4871, 1019]] 
 ![![109, 0, 0], ![0, 109, 0], ![93, 64, 1]] where
  M :=![![![-58269, -4871, 1019], ![289396, 22232, -4871], ![-1383364, -95413, 22232]]]
  hmulB := by decide  
  f := ![![![-270689, -101525, -9837]], ![![-2793708, -1047812, -101525]], ![![-2135821, -801064, -77617]]]
  g := ![![![-1404, -643, 1019], ![6811, 3064, -4871], ![-31660, -13929, 22232]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [67, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 108], [0, 1]]
 g := ![![[67, 63], [80], [108, 25], [38, 81], [36], [89, 1]], ![[6, 46], [80], [44, 84], [53, 28], [36], [69, 108]]]
 h' := ![![[89, 108], [1, 64], [67, 84], [70, 104], [29, 100], [32, 6], [0, 1]], ![[0, 1], [29, 45], [22, 25], [61, 5], [100, 9], [21, 103], [89, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [56, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [67, 20, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1616, 2104, 646]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-566, -360, 646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270689, -101525, -9837]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-270689, -101525, -9837]] 
 ![![109, 0, 0], ![45, 1, 0], ![46, 0, 1]] where
  M :=![![![-270689, -101525, -9837], ![-2793708, -1047812, -101525], ![-28833100, -10814183, -1047812]]]
  hmulB := by decide  
  f := ![![![-58269, -4871, 1019]], ![![-21401, -1807, 376]], ![![-37282, -2931, 634]]]
  g := ![![![43582, -101525, -9837], ![449798, -1047812, -101525], ![4642243, -10814183, -1047812]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-58269, -4871, 1019]] ![![-270689, -101525, -9837]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [83, 112, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 49, 38], [88, 63, 75], [0, 1]]
 g := ![![[37, 95, 32], [61, 41], [96, 102], [22, 106], [67, 89, 104], [1]], ![[93, 82, 89, 37], [108, 49], [4, 87], [74, 13], [106, 99, 14, 73], [4, 31, 90, 67]], ![[13, 8, 37, 70], [46, 53], [66, 26], [19, 81], [57, 43, 31, 92], [60, 96, 98, 46]]]
 h' := ![![[93, 49, 38], [103, 58, 22], [104, 12, 70], [106, 47, 21], [89, 21, 28], [30, 1, 68], [0, 1]], ![[88, 63, 75], [13, 67, 87], [84, 28, 7], [23, 101, 58], [96, 14, 76], [30, 70, 28], [93, 49, 38]], ![[0, 1], [28, 101, 4], [111, 73, 36], [74, 78, 34], [71, 78, 9], [74, 42, 17], [88, 63, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 92], []]
 b := ![[], [58, 15, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [83, 112, 45, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122605, -44748, -3842]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1085, -396, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, -22, 4]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-195, -22, 4]] 
 ![![127, 0, 0], ![0, 127, 0], ![110, 58, 1]] where
  M :=![![![-195, -22, 4], ![1136, 121, -22], ![-6248, -602, 121]]]
  hmulB := by decide  
  f := ![![![11, 2, 0]], ![![0, 11, 2]], ![![14, 8, 1]]]
  g := ![![![-5, -2, 4], ![28, 11, -22], ![-154, -60, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [70, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 126], [0, 1]]
 g := ![![[47, 49], [75, 100], [121, 88], [36, 2], [66, 15], [12, 1]], ![[0, 78], [5, 27], [34, 39], [60, 125], [119, 112], [24, 126]]]
 h' := ![![[12, 126], [84, 120], [39, 10], [20, 56], [79, 111], [49, 74], [0, 1]], ![[0, 1], [0, 7], [32, 117], [57, 71], [14, 16], [48, 53], [12, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [41, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [70, 115, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10978, 5509, 557]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-396, -211, 557]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 2, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![11, 2, 0]] 
 ![![127, 0, 0], ![69, 1, 0], ![65, 0, 1]] where
  M :=![![![11, 2, 0], ![0, 11, 2], ![568, 158, 11]]]
  hmulB := by decide  
  f := ![![![-195, -22, 4]], ![![-97, -11, 2]], ![![-149, -16, 3]]]
  g := ![![![-1, 2, 0], ![-7, 11, 2], ![-87, 158, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-195, -22, 4]] ![![11, 2, 0]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB129I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 128 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 128 (by omega)

def PB129I2 : PrimesBelowBoundCertificateInterval O 79 128 129 where
  m := 9
  g := ![2, 3, 2, 3, 3, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127]
  hP := PB129I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I101N0, I101N1, I101N2, I103N0, I103N1, I103N2, I107N1, I109N1, I127N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [I101N0, I101N1, I101N2], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [], [I127N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
