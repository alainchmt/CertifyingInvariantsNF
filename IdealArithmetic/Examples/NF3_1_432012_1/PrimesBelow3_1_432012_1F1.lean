
import IdealArithmetic.Examples.NF3_1_432012_1.RI3_1_432012_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175227712447, 11966286244, -4119952994]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-175227712447, 11966286244, -4119952994]] 
 ![![37, 0, 0], ![24, 1, 0], ![16, 0, 1]] where
  M :=![![![-175227712447, 11966286244, -4119952994], ![333716192514, -22789451669, 7846333250], ![-635552993250, 43401862264, -14943118419]]]
  hmulB := by decide  
  f := ![![![-713311, -309820, 33986]], ![![-537090, -254229, 14590]], ![![295394, 67456, -46023]]]
  g := ![![![-10716198227, 11966286244, -4119952994], ![20408694610, -22789451669, 7846333250], ![-38867778186, 43401862264, -14943118419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57325393705, -29321256416, 409123324]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-57325393705, -29321256416, 409123324]] 
 ![![37, 0, 0], ![25, 1, 0], ![4, 0, 1]] where
  M :=![![![-57325393705, -29321256416, 409123324], ![-33138989244, -72462956693, -28912133092], ![2341882780452, 1036609935160, -101375089785]]]
  hmulB := by decide  
  f := ![![![-37316543150674851995725, 2548343699416923638720, -877386353633159125804]], ![![-23293115787096902991973, 1590684984302030449379, -547667607974194963032]], ![![-7692262638140117122408, 525303990485251263976, -180860436080995576521]]]
  g := ![![![18218095227, -29321256416, 409123324], ![51191444877, -72462956693, -28912133092], ![-626158519984, 1036609935160, -101375089785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-175227712447, 11966286244, -4119952994]] ![![-175227712447, 11966286244, -4119952994]]
  ![![37316543150674851995725, -2548343699416923638720, 877386353633159125804]] where
 M := ![![![37316543150674851995725, -2548343699416923638720, 877386353633159125804]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37316543150674851995725, -2548343699416923638720, 877386353633159125804]] ![![-57325393705, -29321256416, 409123324]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [40, 3, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 5, 26], [26, 35, 15], [0, 1]]
 g := ![![[5, 40, 2], [17, 25], [15, 16], [15, 31, 1], []], ![[6, 2, 21, 15], [], [26, 33], [35, 21, 7, 34], [19, 20]], ![[7, 20, 25, 13], [34, 25], [22, 20], [0, 1, 13, 6], [30, 20]]]
 h' := ![![[5, 5, 26], [12, 32, 24], [35, 2, 36], [15, 27, 4], [0, 0, 1], [0, 1]], ![[26, 35, 15], [39, 21, 32], [30, 27], [39, 23, 22], [3, 13, 35], [5, 5, 26]], ![[0, 1], [35, 29, 26], [1, 12, 5], [15, 32, 15], [9, 28, 5], [26, 35, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [1, 22, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [40, 3, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23288, -13899, -861]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-568, -339, -21]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [11, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 24, 35], [30, 18, 8], [0, 1]]
 g := ![![[27, 31, 9], [7, 33, 38], [31, 15], [31, 34, 1], []], ![[26, 20, 1, 15], [12, 8, 38, 36], [3, 9], [38, 29, 8, 31], [29, 21]], ![[7, 40, 14, 39], [21, 20, 41, 26], [0, 10], [24, 6, 33, 7], [13, 21]]]
 h' := ![![[4, 24, 35], [9, 33, 3], [12, 28, 9], [3, 11, 31], [0, 0, 1], [0, 1]], ![[30, 18, 8], [6, 23, 5], [20, 42, 24], [28, 29, 40], [41, 16, 18], [4, 24, 35]], ![[0, 1], [2, 30, 35], [11, 16, 10], [21, 3, 15], [26, 27, 24], [30, 18, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 24], []]
 b := ![[], [26, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [11, 7, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![178536, 157380, 34615]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4152, 3660, 805]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [35, 15, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 29, 34], [18, 17, 13], [0, 1]]
 g := ![![[20, 20, 21], [22, 12, 2], [29, 31, 18], [44, 23, 1], []], ![[31, 26, 14, 18], [6, 0, 1, 32], [15, 27, 32, 28], [19, 18, 33, 3], [31, 28]], ![[13, 28, 31, 35], [17, 22, 3, 44], [30, 4, 3, 39], [44, 22, 25, 29], [5, 28]]]
 h' := ![![[5, 29, 34], [29, 34, 16], [19, 11, 7], [11, 39, 21], [0, 0, 1], [0, 1]], ![[18, 17, 13], [18, 37, 18], [33, 36, 23], [36, 0, 38], [21, 20, 17], [5, 29, 34]], ![[0, 1], [17, 23, 13], [38, 0, 17], [35, 8, 35], [8, 27, 29], [18, 17, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 12], []]
 b := ![[], [16, 44, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [35, 15, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-181937, 12079, -4465]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3871, 257, -95]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9205, 5020, 98]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![9205, 5020, 98]] 
 ![![53, 0, 0], ![26, 1, 0], ![13, 0, 1]] where
  M :=![![![9205, 5020, 98], ![-7938, 5579, 5118], ![-414558, -197304, 10697]]]
  hmulB := by decide  
  f := ![![![-1069480435, 73034732, -25145618]], ![![-486220684, 33203971, -11432018]], ![![-335514413, 22912252, -7888613]]]
  g := ![![![-2313, 5020, 98], ![-4142, 5579, 5118], ![86345, -197304, 10697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-338158470018397460, 23092814438795776, -7950780053812249]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-338158470018397460, 23092814438795776, -7950780053812249]] 
 ![![53, 0, 0], ![28, 1, 0], ![11, 0, 1]] where
  M :=![![![-338158470018397460, 23092814438795776, -7950780053812249], ![644013184358792169, -43979608027344247, 15142034384983527], ![-1226504785183665687, 83757912114401670, -28837573642360720]]]
  hmulB := by decide  
  f := ![![![1220512250, 547737110, -48900449]], ![![719533573, 346537131, -16422187]], ![![-509059147, -159828526, 56429445]]]
  g := ![![![-16930164032315933, 23092814438795776, -7950780053812249], ![32243015677162496, -43979608027344247, 15142034384983527], ![-61405905930583859, 83757912114401670, -28837573642360720]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3032, -3750, -2805]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![3032, -3750, -2805]] 
 ![![53, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![3032, -3750, -2805], ![227205, 106817, -6555], ![530955, 469740, 100262]]]
  hmulB := by decide  
  f := ![![![13788831754, -941638200, 324202935]], ![![12773018523, -872268397, 300319140]], ![![13691792687, -935011410, 321921353]]]
  g := ![![![6259, -3750, -2805], ![-92439, 106817, -6555], ![-534691, 469740, 100262]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![9205, 5020, 98]] ![![-338158470018397460, 23092814438795776, -7950780053812249]]
  ![![13788831754, -941638200, 324202935]] where
 M := ![![![13788831754, -941638200, 324202935]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![13788831754, -941638200, 324202935]] ![![3032, -3750, -2805]]
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
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2380233204419, 162545932112, -55964029776]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2380233204419, 162545932112, -55964029776]] 
 ![![59, 0, 0], ![9, 1, 0], ![37, 0, 1]] where
  M :=![![![-2380233204419, 162545932112, -55964029776], ![4533086411856, -309564102707, 106581902336], ![-8633134089216, 589556025424, -202982200371]]]
  hmulB := by decide  
  f := ![![![3486167, 1811472, -10000]], ![![545517, 341685, 29008]], ![![-286967, 20000, 89621]]]
  g := ![![![-30041991385, 162545932112, -55964029776], ![57214117793, -309564102707, 106581902336], ![-108962659395, 589556025424, -202982200371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3657963662852, -249802041290, 86006021161]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![3657963662852, -249802041290, 86006021161]] 
 ![![59, 0, 0], ![50, 1, 0], ![37, 0, 1]] where
  M :=![![![3657963662852, -249802041290, 86006021161], ![-6966487714041, 475740879895, -163796020129], ![13267477630449, -906034969268, 311944859766]]]
  hmulB := by decide  
  f := ![![![-591002, -942008, -331685]], ![![-45485, -600323, -302677]], ![![1378001, 663370, -31605]]]
  g := ![![![219760049905, -249802041290, 86006021161], ![-418526762102, 475740879895, -163796020129], ![797072309873, -906034969268, 311944859766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-772472242654, -290449106840, 60468559449]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-772472242654, -290449106840, 60468559449]] 
 ![![59, 0, 0], ![58, 1, 0], ![58, 0, 1]] where
  M :=![![![-772472242654, -290449106840, 60468559449], ![-4897953315369, -3009808942267, -229980547391], ![18628424338671, 3611326938098, -3239789489658]]]
  hmulB := by decide  
  f := ![![![10581682323066930727977004, -722622225974631461072718, 248796455535894140585323]], ![![10060763759991094183648391, -687048739632030122303349, 236548621197341064973921]], ![![11052838341413893308171953, -754797432181402869010088, 259874273201389328131888]]]
  g := ![![![212989822136, -290449106840, 60468559449], ![3101861645505, -3009808942267, -229980547391], ![-49504197811, 3611326938098, -3239789489658]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2380233204419, 162545932112, -55964029776]] ![![3657963662852, -249802041290, 86006021161]]
  ![![-10581682323066930727977004, 722622225974631461072718, -248796455535894140585323]] where
 M := ![![![-10581682323066930727977004, 722622225974631461072718, -248796455535894140585323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-10581682323066930727977004, 722622225974631461072718, -248796455535894140585323]] ![![-772472242654, -290449106840, 60468559449]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70636414031391656249, -33538829077272641762, 1864528871266824928]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-70636414031391656249, -33538829077272641762, 1864528871266824928]] 
 ![![61, 0, 0], ![0, 61, 0], ![57, 4, 1]] where
  M :=![![![-70636414031391656249, -33538829077272641762, 1864528871266824928], ![-151026838572612819168, -139623982268264178585, -31674300206005816834], ![2565618316686471163554, 1020922269049602403690, -171298282474269995419]]]
  hmulB := by decide  
  f := ![![![922202406420415241299772249371770715075, -62977127396273576534180556814664867278, 21682817816588139405314966635619553908]], ![![-1756308243143639291830512297485183866548, 119938147206654083303118483853847220479, -41294309579685437128865590179045313370]], ![![801395791300715278593493144733653535673, -54727253466495994218004971539033046308, 18842413358258210553471207068671069285]]]
  g := ![![![-2900238683501650445, -672081058399015434, 1864528871266824928], ![27121447101142930170, -211914449905588709, -31674300206005816834], ![202124924880653457417, 27969104900765285006, -171298282474269995419]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [17, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 60], [0, 1]]
 g := ![![[51, 12], [48], [3, 27], [35, 46], [48, 1]], ![[17, 49], [48], [18, 34], [47, 15], [35, 60]]]
 h' := ![![[48, 60], [16, 16], [10, 32], [15, 24], [38, 30], [0, 1]], ![[0, 1], [52, 45], [21, 29], [8, 37], [14, 31], [48, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [50, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [17, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212, -825, -374]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![346, 11, -374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15966530642978951, 10225050967176211, 966853186547413]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![15966530642978951, 10225050967176211, 966853186547413]] 
 ![![61, 0, 0], ![56, 1, 0], ![36, 0, 1]] where
  M :=![![![15966530642978951, 10225050967176211, 966853186547413], ![-78315108110340453, -19807037259275330, 11191904153723624], ![-906544236451613544, -492415561798114541, -8615133105551706]]]
  hmulB := by decide  
  f := ![![![-5681708033861749022569153014829564, 388003379936768346965906827566467, -133588287481768885403689267729954]], ![![-5038606534594010910593012100726710, 344086030810208642089477577621326, -118467688631541936410563630049851]], ![![-3690969044391441331131625096403637, 252055976113310821814252897779805, -86782043506966896321364691594477]]]
  g := ![![![-9695787512042553, 10225050967176211, 966853186547413], ![10294597194672583, -19807037259275330, 11191904153723624], ![442276590426928888, -492415561798114541, -8615133105551706]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-70636414031391656249, -33538829077272641762, 1864528871266824928]] ![![15966530642978951, 10225050967176211, 966853186547413]]
  ![![61, 0, 0]] where
 M := ![![![-191499346006098986985704165970441445, -976079128077192466828590385046039127, -459721566858595535564853212098346493]]]
 hmul := by decide  
 g := ![![![![-3139333541083589950585314196236745, -16001297181593319128337547295836707, -7536419128829435009259888722923713]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [52, 39, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 50, 34], [22, 16, 33], [0, 1]]
 g := ![![[48, 63, 17], [55, 38, 10], [6, 59], [57, 62], [5, 1], []], ![[32, 35, 2, 38], [6, 60, 65, 3], [3, 35], [59, 39], [22, 55], [1, 17]], ![[61, 34, 39, 22], [20, 24, 6, 36], [56, 62], [47, 49], [33, 21], [2, 17]]]
 h' := ![![[50, 50, 34], [21, 22, 33], [49, 33, 12], [48, 48, 27], [8, 21, 53], [0, 0, 1], [0, 1]], ![[22, 16, 33], [31, 33, 3], [54, 56, 41], [3, 53, 54], [18, 51, 21], [36, 57, 16], [50, 50, 34]], ![[0, 1], [47, 12, 31], [42, 45, 14], [41, 33, 53], [41, 62, 60], [45, 10, 50], [22, 16, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 42], []]
 b := ![[], [50, 51, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [52, 39, 62, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35912, -23919, -2613]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-536, -357, -39]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-176, -1, 48]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-176, -1, 48]] 
 ![![71, 0, 0], ![0, 71, 0], ![20, 34, 1]] where
  M :=![![![-176, -1, 48], ![-3888, -1952, 47], ![-3807, -5627, -1905]]]
  hmulB := by decide  
  f := ![![![56099, -3831, 1319]], ![![-106839, 7296, -2512]], ![![-32494, 2219, -764]]]
  g := ![![![-16, -23, 48], ![-68, -50, 47], ![483, 833, -1905]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [70, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 70], [0, 1]]
 g := ![![[46, 27], [46, 1], [], [43], [57], [1]], ![[10, 44], [21, 70], [], [43], [57], [1]]]
 h' := ![![[46, 70], [46, 58], [0, 1], [70], [58, 16], [1, 46], [0, 1]], ![[0, 1], [16, 13], [46, 70], [70], [13, 55], [58, 25], [46, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [38, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [70, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3063, -1011, 390]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-153, -201, 390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56099, -3831, 1319]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![56099, -3831, 1319]] 
 ![![71, 0, 0], ![36, 1, 0], ![53, 0, 1]] where
  M :=![![![56099, -3831, 1319], ![-106839, 7296, -2512], ![203472, -13895, 4784]]]
  hmulB := by decide  
  f := ![![![-176, -1, 48]], ![![-144, -28, 25]], ![![-185, -80, 9]]]
  g := ![![![1748, -3831, 1319], ![-3329, 7296, -2512], ![6340, -13895, 4784]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-176, -1, 48]] ![![56099, -3831, 1319]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [1, 72, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 7, 5], [52, 65, 68], [0, 1]]
 g := ![![[52, 69, 4], [24, 55], [49, 9], [2, 71, 1], [0, 1], []], ![[11, 51, 1, 15], [44, 24], [57, 38], [62, 56, 71, 42], [51, 64], [70, 25]], ![[7, 5, 20, 20], [24, 49], [41, 2], [64, 12, 24, 10], [72, 49], [7, 25]]]
 h' := ![![[21, 7, 5], [30, 72, 2], [28, 24, 37], [71, 4, 70], [0, 72, 1], [0, 0, 1], [0, 1]], ![[52, 65, 68], [21, 14, 52], [24, 9, 43], [64, 33, 44], [58, 40, 60], [6, 47, 65], [21, 7, 5]], ![[0, 1], [43, 60, 19], [33, 40, 66], [72, 36, 32], [17, 34, 12], [69, 26, 7], [52, 65, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 29], []]
 b := ![[], [46, 16, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [1, 72, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12483, 4745, -1460]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, 65, -20]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17558862405949486, 9069823502462487, -78753978160706]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![17558862405949486, 9069823502462487, -78753978160706]] 
 ![![79, 0, 0], ![0, 79, 0], ![3, 51, 1]] where
  M :=![![![17558862405949486, 9069823502462487, -78753978160706], ![6379072231017186, 20472759597895608, 8991069524301781], ![-728276631468444261, -326290500168148711, 29463829122197389]]]
  hmulB := by decide  
  f := ![![![44770967880800629707010035978757, -3057405758490586399590241988563, 1052654746152513431493808295805]], ![![-85265034438353587950998471960205, 5822742273157632741739129033972, -2004751012338072968096433692758]], ![![-51288848363471483366633934593934, 3502511287009147120234106701756, -1205903115569172421579670862051]]]
  g := ![![![225254738486476, 165649068210867, -78753978160706], ![-260685270150483, -5545212482803737, 8991069524301781], ![-10337571124494132, -23151212473420450, 29463829122197389]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [49, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 78], [0, 1]]
 g := ![![[37, 50], [73, 42], [22, 52], [4, 65], [16], [1]], ![[0, 29], [4, 37], [72, 27], [27, 14], [16], [1]]]
 h' := ![![[4, 78], [57, 45], [28, 11], [41, 17], [37, 67], [30, 4], [0, 1]], ![[0, 1], [0, 34], [72, 68], [30, 62], [68, 12], [46, 75], [4, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [7, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [49, 75, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-599, -545, 11]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -14, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44770967880800629707010035978757, -3057405758490586399590241988563, 1052654746152513431493808295805]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![44770967880800629707010035978757, -3057405758490586399590241988563, 1052654746152513431493808295805]] 
 ![![79, 0, 0], ![27, 1, 0], ![61, 0, 1]] where
  M :=![![![44770967880800629707010035978757, -3057405758490586399590241988563, 1052654746152513431493808295805], ![-85265034438353587950998471960205, 5822742273157632741739129033972, -2004751012338072968096433692758], ![162384831999383910415811129113398, -11089246981844888131430425328159, 3817991260819559773642695341214]]]
  hmulB := by decide  
  f := ![![![17558862405949486, 9069823502462487, -78753978160706]], ![![6081877939134852, 3358961951447883, 86895090050161]], ![![4339417408790815, 2873021942810924, 312149828536637]]]
  g := ![![![798847896768900546516762830707, -3057405758490586399590241988563, 1052654746152513431493808295805], ![-1521383089379585074988259501509, 5822742273157632741739129033972, -2004751012338072968096433692758], ![2897430805053199288256053128603, -11089246981844888131430425328159, 3817991260819559773642695341214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![17558862405949486, 9069823502462487, -78753978160706]] ![![44770967880800629707010035978757, -3057405758490586399590241988563, 1052654746152513431493808295805]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB186I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB186I1 : PrimesBelowBoundCertificateInterval O 31 79 186 where
  m := 11
  g := ![3, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB186I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
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
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
  β := ![I37N0, I37N1, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I71N1, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [], [], [], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
