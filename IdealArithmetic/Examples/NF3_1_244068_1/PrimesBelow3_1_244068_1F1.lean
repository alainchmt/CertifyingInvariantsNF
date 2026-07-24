
import IdealArithmetic.Examples.NF3_1_244068_1.RI3_1_244068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![34, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 1, 0], ![2, 5, 6], ![14, -22, 3]]]
  hmulB := by decide  
  f := ![![![1593, 4052, 4872], ![296, -30044, 0]], ![![170, 434, 522], ![38, -3219, 0]], ![![1462, 3723, 4477], ![289, -27608, 0]]]
  g := ![![![1, 0, 0], ![-4, 37, 0], ![-34, 0, 37]], ![![0, 1, 0], ![-6, 5, 6], ![0, -22, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![2, 8, 6], ![14, -22, 6]]]
  hmulB := by decide  
  f := ![![![-515, -2172, -1632], ![-148, 10064, 0]], ![![-102, -408, -306], ![1, 1887, 0]], ![![-392, -1644, -1235], ![-100, 7616, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-6, 8, 6], ![0, -22, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![19, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![2, -10, 6], ![14, -22, -12]]]
  hmulB := by decide  
  f := ![![![-364, 2095, -1260], ![185, 7770, 0]], ![![-249, 1466, -882], ![149, 5439, 0]], ![![-189, 1076, -647], ![88, 3990, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-19, 0, 37]], ![![-1, 1, 0], ![4, -10, 6], ![22, -22, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![4, 1, 0]] ![![37, 0, 0], ![7, 1, 0]]
  ![![37, 0, 0], ![5, 2, 1]] where
 M := ![![![1369, 0, 0], ![259, 37, 0]], ![![148, 37, 0], ![30, 12, 6]]]
 hmul := by decide  
 g := ![![![![32, -2, -1], ![37, 0, 0]], ![![2, -1, -1], ![37, 0, 0]]], ![![![-1, -1, -1], ![37, 0, 0]], ![![0, 0, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 2, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![185, 74, 37], ![-37, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![5, 2, 1]], ![![-1, -1, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-761, -55740, -102010]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-761, -55740, -102010]] 
 ![![41, 0, 0], ![12, 1, 0], ![29, 0, 1]] where
  M :=![![![-761, -55740, -102010], ![-1539620, 2187719, -232430], ![443760, 614220, 2299199]]]
  hmulB := by decide  
  f := ![![![-5172764491681, -65500770060, -236124863390]], ![![-1597803012872, -20232378241, -72936051650]], ![![-3612041040949, -45737916360, -164881408911]]]
  g := ![![![88449, -55740, -102010], ![-513458, 2187719, -232430], ![-1795211, 614220, 2299199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -50, 21]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, -50, 21]] 
 ![![41, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![41, -50, 21], ![194, -471, -321], ![-952, 1226, -371]]]
  hmulB := by decide  
  f := ![![![-568287, -7196, -25941]], ![![-452750, -5733, -20667]], ![![-22586, -286, -1031]]]
  g := ![![![39, -50, 21], ![388, -471, -321], ![-962, 1226, -371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149534939, 411873514, 1142201594]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![149534939, 411873514, 1142201594]] 
 ![![41, 0, 0], ![38, 1, 0], ![13, 0, 1]] where
  M :=![![![149534939, 411873514, 1142201594], ![16814569344, -24567026615, 1329039490], ![-7940189932, -2208007744, -25390773643]]]
  hmulB := by decide  
  f := ![![![-626710341349023319005, -7935797198759847566, -28607893124484492170]], ![![-591009148034224114822, -7483726423463379179, -26978215336548421846]], ![![-193049777581125051389, -2444516681904105486, -8812280634875683949]]]
  g := ![![![-740250715, 411873514, 1142201594], ![22758147984, -24567026615, 1329039490], ![9903516139, -2208007744, -25390773643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-761, -55740, -102010]] ![![41, -50, 21]]
  ![![86268759, -98772670, 55722269]] where
 M := ![![![86268759, -98772670, 55722269]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![86268759, -98772670, 55722269]] ![![149534939, 411873514, 1142201594]]
  ![![41, 0, 0]] where
 M := ![![![-2090365114694353487, 2339047428177110040, -1447567983973892421]]]
 hmul := by decide  
 g := ![![![![-50984514992545207, 57049937272612440, -35306536194485181]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3612041040949, 45737916360, 164881408911]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![3612041040949, 45737916360, 164881408911]] 
 ![![43, 0, 0], ![0, 1, 0], ![29, 0, 1]] where
  M :=![![![3612041040949, 45737916360, 164881408911], ![2399815557474, 30387961267, 109546089249], ![-1338246077892, -16945706454, -61087871453]]]
  hmulB := by decide  
  f := ![![![302095, -140514, 563403]], ![![176898, -284495, -32709]], ![![761, 55740, 102010]]]
  g := ![![![-27198135290, 45737916360, 164881408911], ![-18070256529, 30387961267, 109546089249], ![10076795215, -16945706454, -61087871453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![3612041040949, 45737916360, 164881408911]] ![![3612041040949, 45737916360, 164881408911]]
  ![![12935951145954655270799629, 163803081095465916842166, 590496571431117324992496]] where
 M := ![![![12935951145954655270799629, 163803081095465916842166, 590496571431117324992496]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![12935951145954655270799629, 163803081095465916842166, 590496571431117324992496]] ![![3612041040949, 45737916360, 164881408911]]
  ![![43, 0, 0]] where
 M := ![![![46328053904548170846917392061391158173, 586634711672899296468228409912645578, 2114769658840792325791081776140950665]]]
 hmul := by decide  
 g := ![![![![1077396602431352810393427722357933911, 13642667713323239452749497904945246, 49180689740483542460257715724208155]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 10, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 41, 23], [39, 5, 24], [0, 1]]
 g := ![![[11, 21, 9], [40, 46, 9], [30, 0, 27], [17, 11, 1], []], ![[44, 33, 12, 45], [14, 22, 1, 15], [4, 23, 28, 19], [44, 42, 37, 11], [44, 12]], ![[1, 32, 3, 24], [23, 32, 36, 36], [36, 7, 2, 4], [38, 24, 45, 18], [43, 12]]]
 h' := ![![[19, 41, 23], [5, 34, 3], [39, 46, 3], [8, 37, 36], [0, 0, 1], [0, 1]], ![[39, 5, 24], [35, 29, 45], [15, 4, 39], [40, 36, 44], [14, 15, 5], [19, 41, 23]], ![[0, 1], [41, 31, 46], [26, 44, 5], [24, 21, 14], [40, 32, 41], [39, 5, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 22], []]
 b := ![[], [43, 18, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 10, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-116372, -48128, -400581]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2476, -1024, -8523]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![9, -23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![9, -23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![9, 30, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![9, -23, 1], ![-32, -36, -139], ![-334, 512, 10]]]
  hmulB := by decide  
  f := ![![![-8, 23, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -30, 53]], ![![0, -1, 1], ![23, 78, -139], ![-8, 4, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 52], [0, 1]]
 g := ![![[18, 6], [47], [], [], [50, 1]], ![[0, 47], [47], [], [], [47, 52]]]
 h' := ![![[50, 52], [1, 18], [0, 10], [40], [27], [0, 1]], ![[0, 1], [0, 35], [23, 43], [40], [27], [50, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-569, 294, -1029]
  a := ![2, 0, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![164, 588, -1029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, 1, 0]] 
 ![![53, 0, 0], ![33, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, 1, 0], ![2, -19, 6], ![14, -22, -21]]]
  hmulB := by decide  
  f := ![![![2591, -29897, 9450], ![-1484, -83475, 0]], ![![1601, -18602, 5880], ![-953, -51940, 0]], ![![2101, -24256, 7667], ![-1207, -67725, 0]]]
  g := ![![![1, 0, 0], ![-33, 53, 0], ![-43, 0, 53]], ![![-1, 1, 0], ![7, -19, 6], ![31, -22, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![9, -23, 1]] ![![53, 0, 0], ![-20, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1060, 53, 0]], ![![477, -1219, 53], ![-212, 424, -159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-20, 1, 0]]], ![![![9, -23, 1]], ![![-4, 8, -3]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [46, 0, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 45, 35], [45, 13, 24], [0, 1]]
 g := ![![[57, 33, 5], [44, 51, 17], [37, 45], [12, 15, 7], [1]], ![[58, 41, 18, 17], [33, 12, 30, 26], [22, 51], [6, 18, 35, 46], [25, 32, 10, 41]], ![[7, 27, 13, 54], [0, 58, 7, 43], [20, 12], [14, 6, 10, 6], [39, 30, 32, 18]]]
 h' := ![![[33, 45, 35], [41, 26, 51], [37, 47, 31], [38, 10, 24], [13, 0, 19], [0, 1]], ![[45, 13, 24], [54, 47, 39], [17, 43, 42], [12, 43, 13], [36, 49, 11], [33, 45, 35]], ![[0, 1], [53, 45, 28], [46, 28, 45], [9, 6, 22], [5, 10, 29], [45, 13, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 20], []]
 b := ![[], [51, 40, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [46, 0, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5360859003, -605854362, -15555783709]
  a := ![-129, -64, -323]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-90862017, -10268718, -263657351]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![24, 8, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 8, 1], ![30, 10, 47], ![100, -170, -6]]]
  hmulB := by decide  
  f := ![![![-23, -8, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -8, 61]], ![![0, 0, 1], ![-18, -6, 47], ![4, -2, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 60], [0, 1]]
 g := ![![[27, 5], [27], [51, 3], [13, 48], [55, 1]], ![[58, 56], [27], [33, 58], [30, 13], [49, 60]]]
 h' := ![![[55, 60], [14, 26], [9, 24], [31, 8], [42, 29], [0, 1]], ![[0, 1], [41, 35], [48, 37], [44, 53], [51, 32], [55, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [45, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-920, 161, -2214]
  a := ![-3, -1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![856, 293, -2214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![14, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![14, 1, 0]] 
 ![![61, 0, 0], ![14, 1, 0], ![6, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![14, 1, 0], ![2, 15, 6], ![14, -22, 13]]]
  hmulB := by decide  
  f := ![![![261, 2158, 864], ![122, -8784, 0]], ![![52, 494, 198], ![62, -2013, 0]], ![![22, 212, 85], ![28, -864, 0]]]
  g := ![![![1, 0, 0], ![-14, 61, 0], ![-6, 0, 61]], ![![0, 1, 0], ![-4, 15, 6], ![4, -22, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![24, 8, 1]] ![![61, 0, 0], ![14, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![854, 61, 0]], ![![1464, 488, 61], ![366, 122, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![14, 1, 0]]], ![![![24, 8, 1]], ![![6, 2, 1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![2, 15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![2, 15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![2, 15, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![2, 15, 1], ![44, -5, 89], ![198, -324, -35]]]
  hmulB := by decide  
  f := ![![![-1, -15, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -15, 67]], ![![0, 0, 1], ![-2, -20, 89], ![4, 3, -35]]]
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
  c := ![-467, -320, -1875]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 415, -1875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-22, 1, 0]] 
 ![![67, 0, 0], ![45, 1, 0], ![35, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-22, 1, 0], ![2, -21, 6], ![14, -22, -23]]]
  hmulB := by decide  
  f := ![![![-7, 314, -90], ![67, 1005, 0]], ![![3, 209, -60], ![68, 670, 0]], ![![-3, 164, -47], ![37, 525, 0]]]
  g := ![![![1, 0, 0], ![-45, 67, 0], ![-35, 0, 67]], ![![-1, 1, 0], ![11, -21, 6], ![27, -22, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![2, 15, 1]] ![![67, 0, 0], ![-22, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1474, 67, 0]], ![![134, 1005, 67], ![0, -335, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-22, 1, 0]]], ![![![2, 15, 1]], ![![0, -5, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![15, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![15, 1, 0]] 
 ![![71, 0, 0], ![15, 1, 0], ![55, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![15, 1, 0], ![2, 16, 6], ![14, -22, 14]]]
  hmulB := by decide  
  f := ![![![-1505, -12762, -4788], ![-426, 56658, 0]], ![![-321, -2687, -1008], ![-70, 11928, 0]], ![![-1165, -9886, -3709], ![-334, 43890, 0]]]
  g := ![![![1, 0, 0], ![-15, 71, 0], ![-55, 0, 71]], ![![0, 1, 0], ![-8, 16, 6], ![-6, -22, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 1, 0]] 
 ![![71, 0, 0], ![26, 1, 0], ![49, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 1, 0], ![2, 27, 6], ![14, -22, 25]]]
  hmulB := by decide  
  f := ![![![-2099, -34300, -7626], ![-1207, 90241, 0]], ![![-774, -12549, -2790], ![-425, 33015, 0]], ![![-1453, -23672, -5263], ![-821, 62279, 0]]]
  g := ![![![1, 0, 0], ![-26, 71, 0], ![-49, 0, 71]], ![![0, 1, 0], ![-14, 27, 6], ![-9, -22, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![30, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![30, 1, 0]] 
 ![![71, 0, 0], ![30, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![30, 1, 0], ![2, 31, 6], ![14, -22, 29]]]
  hmulB := by decide  
  f := ![![![-4529, -90631, -17550], ![-3124, 207675, 0]], ![![-1930, -38267, -7410], ![-1277, 87685, 0]], ![![-719, -14042, -2719], ![-443, 32175, 0]]]
  g := ![![![1, 0, 0], ![-30, 71, 0], ![-11, 0, 71]], ![![0, 1, 0], ![-14, 31, 6], ![5, -22, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![15, 1, 0]] ![![71, 0, 0], ![26, 1, 0]]
  ![![71, 0, 0], ![18, 7, 1]] where
 M := ![![![5041, 0, 0], ![1846, 71, 0]], ![![1065, 71, 0], ![392, 42, 6]]]
 hmul := by decide  
 g := ![![![![53, -7, -1], ![71, 0, 0]], ![![8, -6, -1], ![71, 0, 0]]], ![![![-3, -6, -1], ![71, 0, 0]], ![![4, 0, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![18, 7, 1]] ![![71, 0, 0], ![30, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2130, 71, 0]], ![![1278, 497, 71], ![568, 213, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![30, 1, 0]]], ![![![18, 7, 1]], ![![8, 3, 1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![7, 6, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![7, 6, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![7, 6, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![7, 6, 1], ![26, -9, 35], ![72, -126, -21]]]
  hmulB := by decide  
  f := ![![![-6, -6, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -6, 73]], ![![0, 0, 1], ![-3, -3, 35], ![3, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [5, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 72], [0, 1]]
 g := ![![[71, 55], [23], [16], [42, 65], [27], [1]], ![[37, 18], [23], [16], [35, 8], [27], [1]]]
 h' := ![![[10, 72], [32, 37], [1, 13], [9, 4], [36, 24], [68, 10], [0, 1]], ![[0, 1], [37, 36], [58, 60], [49, 69], [57, 49], [22, 63], [10, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [64, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [5, 63, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12639, -32358, -94526]
  a := ![23, 21, 68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8891, 7326, -94526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-35, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-35, 1, 0]] 
 ![![73, 0, 0], ![38, 1, 0], ![21, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-35, 1, 0], ![2, -34, 6], ![14, -22, -36]]]
  hmulB := by decide  
  f := ![![![1916, -45029, 7950], ![-1533, -96725, 0]], ![![1029, -23416, 4134], ![-729, -50297, 0]], ![![567, -12954, 2287], ![-408, -27825, 0]]]
  g := ![![![1, 0, 0], ![-38, 73, 0], ![-21, 0, 73]], ![![-1, 1, 0], ![16, -34, 6], ![22, -22, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![7, 6, 1]] ![![73, 0, 0], ![-35, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2555, 73, 0]], ![![511, 438, 73], ![-219, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-35, 1, 0]]], ![![![7, 6, 1]], ![![-3, -3, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [17, 3, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 30, 45], [40, 48, 34], [0, 1]]
 g := ![![[2, 9, 9], [25, 44, 13], [69, 3, 2], [59, 37, 62], [6, 1], []], ![[54, 3, 48, 9], [27, 24, 63, 22], [17, 39, 63, 1], [55, 40, 47, 11], [30, 13], [77, 50]], ![[56, 53, 30, 7], [43, 14, 33, 75], [2, 18, 4, 14], [67, 3, 49, 15], [58, 31], [9, 50]]]
 h' := ![![[45, 30, 45], [49, 32, 3], [12, 2, 31], [24, 39, 9], [56, 44, 33], [0, 0, 1], [0, 1]], ![[40, 48, 34], [3, 50, 4], [20, 5, 77], [7, 20, 54], [68, 0, 9], [5, 39, 48], [45, 30, 45]], ![[0, 1], [61, 76, 72], [77, 72, 50], [71, 20, 16], [34, 35, 37], [25, 40, 30], [40, 48, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 8], []]
 b := ![[], [38, 49, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [17, 3, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12956, 15405, -7426]
  a := ![-1, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-164, 195, -94]
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



lemma PB140I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB140I1 : PrimesBelowBoundCertificateInterval O 31 79 140 where
  m := 11
  g := ![3, 3, 3, 1, 2, 1, 2, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB140I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N0, I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N0, I53N1, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N0, I43N0, I43N0], [], [I53N1], [], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
