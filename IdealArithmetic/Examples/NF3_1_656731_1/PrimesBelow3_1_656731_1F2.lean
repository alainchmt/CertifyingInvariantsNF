
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44101, 10866, 4910]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-44101, 10866, 4910]] 
 ![![83, 0, 0], ![6, 1, 0], ![33, 0, 1]] where
  M :=![![![-44101, 10866, 4910], ![438036, -161941, 102704], ![979712, -226414, -151075]]]
  hmulB := by decide  
  f := ![![![-47718860031, -529888210, -1911111974]], ![![-5459154098, -60620505, -218635876]], ![![-19689161917, -218635876, -788539229]]]
  g := ![![![-3269, 10866, 4910], ![-23850, -161941, 102704], ![88237, -226414, -151075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![33, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![33, 1, 0]] 
 ![![83, 0, 0], ![33, 1, 0], ![82, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![33, 1, 0], ![1, 33, 9], ![87, -24, 34]]]
  hmulB := by decide  
  f := ![![![-1376, -61761, -16848], ![-1245, 155376, 0]], ![![-546, -24546, -6696], ![-497, 61752, 0]], ![![-1363, -61017, -16645], ![-1221, 153504, 0]]]
  g := ![![![1, 0, 0], ![-33, 83, 0], ![-82, 0, 83]], ![![0, 1, 0], ![-22, 33, 9], ![-23, -24, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-40, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-40, 1, 0]] 
 ![![83, 0, 0], ![43, 1, 0], ![16, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-40, 1, 0], ![1, -40, 9], ![87, -24, -39]]]
  hmulB := by decide  
  f := ![![![1817, -114214, 25704], ![-2158, -237048, 0]], ![![960, -59147, 13311], ![-1078, -122757, 0]], ![![344, -22017, 4955], ![-429, -45696, 0]]]
  g := ![![![1, 0, 0], ![-43, 83, 0], ![-16, 0, 83]], ![![-1, 1, 0], ![19, -40, 9], ![21, -24, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-44101, 10866, 4910]] ![![83, 0, 0], ![33, 1, 0]]
  ![![83, 0, 0], ![-24, 32, 1]] where
 M := ![![![-3660383, 901878, 407530], ![-1017297, 196637, 264734]]]
 hmul := by decide  
 g := ![![![![-40093, 5522, 4743], ![13861, 0, 0]], ![![-11187, 943, 3145], ![3699, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-24, 32, 1]] ![![83, 0, 0], ![-40, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3320, 83, 0]], ![![-1992, 2656, 83], ![1079, -1328, 249]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-40, 1, 0]]], ![![![-24, 32, 1]], ![![13, -16, 3]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673549511452, 7479347678, 26975257489]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![673549511452, 7479347678, 26975257489]] 
 ![![89, 0, 0], ![23, 1, 0], ![60, 0, 1]] where
  M :=![![![673549511452, 7479347678, 26975257489], ![2354326749221, 26143331716, 94289386591], ![839530050409, 9322458151, 33622679394]]]
  hmulB := by decide  
  f := ![![![1806863, -504293, -35426]], ![![426646, -100468, -60549]], ![![722363, -206770, 306]]]
  g := ![![![-12550459938, 7479347678, 26975257489], ![-43868910963, 26143331716, 94289386591], ![-15643227536, 9322458151, 33622679394]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-12, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-12, 1, 0]] 
 ![![89, 0, 0], ![77, 1, 0], ![83, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-12, 1, 0], ![1, -12, 9], ![87, -24, -11]]]
  hmulB := by decide  
  f := ![![![-703, 8877, -6660], ![267, 65860, 0]], ![![-615, 7678, -5760], ![179, 56960, 0]], ![![-661, 8279, -6211], ![209, 61420, 0]]]
  g := ![![![1, 0, 0], ![-77, 89, 0], ![-83, 0, 89]], ![![-1, 1, 0], ![2, -12, 9], ![32, -24, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![673549511452, 7479347678, 26975257489]] ![![89, 0, 0], ![-12, 1, 0]]
  ![![89, 0, 0], ![9, 21, 1]] where
 M := ![![![59945906519228, 665661943342, 2400797916521], ![-5728267388203, -63608840420, -229413703277]]]
 hmul := by decide  
 g := ![![![![666892253698, -8054253748, 26235562183], ![65832882234, 0, 0]], ![![-63726405527, 769642520, -2506998793], ![-6290810700, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![9, 21, 1]] ![![89, 0, 0], ![-12, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1068, 89, 0]], ![![801, 1869, 89], ![0, -267, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-12, 1, 0]]], ![![![9, 21, 1]], ![![0, -3, 2]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9808391445, 108916076, 392820246]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![9808391445, 108916076, 392820246]] 
 ![![97, 0, 0], ![0, 97, 0], ![10, 51, 1]] where
  M :=![![![9808391445, 108916076, 392820246], ![34284277478, 380705541, 1373064930], ![12225440334, 135755898, 489621617]]]
  hmulB := by decide  
  f := ![![![8481, -1072, -3798]], ![![-331498, 99633, -13446]], ![![-174654, 52265, -6445]]]
  g := ![![![60620505, -205411510, 392820246], ![211893074, -717995937, 1373064930], ![75559012, -256030377, 489621617]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [42, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 96], [0, 1]]
 g := ![![[91, 8], [73], [27], [9], [91], [58, 1]], ![[70, 89], [73], [27], [9], [91], [19, 96]]]
 h' := ![![[58, 96], [2, 28], [62, 49], [41, 30], [82, 94], [86, 24], [0, 1]], ![[0, 1], [74, 69], [91, 48], [35, 67], [5, 3], [23, 73], [58, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [66, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [42, 39, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2138, 98, -2250]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![254, 1184, -2250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8481, -1072, -3798]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![8481, -1072, -3798]] 
 ![![97, 0, 0], ![25, 1, 0], ![60, 0, 1]] where
  M :=![![![8481, -1072, -3798], ![-331498, 99633, -13446], ![-119850, -858, 98561]]]
  hmulB := by decide  
  f := ![![![9808391445, 108916076, 392820246]], ![![2881382099, 31995953, 115397640]], ![![6193081722, 68770314, 248029241]]]
  g := ![![![2713, -1072, -3798], ![-20779, 99633, -13446], ![-61980, -858, 98561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![9808391445, 108916076, 392820246]] ![![8481, -1072, -3798]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24753427771, -6248406417, -2336865504]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![24753427771, -6248406417, -2336865504]] 
 ![![101, 0, 0], ![0, 101, 0], ![63, 60, 1]] where
  M :=![![![24753427771, -6248406417, -2336865504], ![-209555705265, 80838199867, -58572523257], ![-559969416807, 133603695480, 74589793450]]]
  hmulB := by decide  
  f := ![![![137180298927453398510, 1523301751104473730, 5493989414391784437]], ![![479500380803189719749, 5324552982050572022, 19203705174332048007]], ![![372112543157106722739, 4132077951651992949, 14902886121779805403]]]
  g := ![![![1702732223, 1326371523, -2336865504], ![34460527326, 35595936587, -58572523257], ![-52070558457, -42987959520, 74589793450]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [90, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 100], [0, 1]]
 g := ![![[65, 70], [97], [97, 43], [71], [70], [8, 1]], ![[19, 31], [97], [37, 58], [71], [70], [16, 100]]]
 h' := ![![[8, 100], [74, 26], [57, 20], [65, 89], [30, 24], [88, 75], [0, 1]], ![[0, 1], [80, 75], [15, 81], [70, 12], [20, 77], [82, 26], [8, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [30, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [90, 93, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3801, 4157, -6861]
  a := ![2, -2, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4242, 4117, -6861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137180298927453398510, -1523301751104473730, -5493989414391784437]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-137180298927453398510, -1523301751104473730, -5493989414391784437]] 
 ![![101, 0, 0], ![65, 1, 0], ![2, 0, 1]] where
  M :=![![![-137180298927453398510, -1523301751104473730, -5493989414391784437], ![-479500380803189719749, -5324552982050572022, -19203705174332048007], ![-170985178246831705569, -1898683874235121539, -6847854733155045752]]]
  hmulB := by decide  
  f := ![![![-24753427771, 6248406417, 2336865504]], ![![-13855614850, 3220873438, 2083849317]], ![![5054084765, -1199078046, -692238242]]]
  g := ![![![-269086200761178586, -1523301751104473730, -5493989414391784437], ![-940564620012261805, -5324552982050572022, -19203705174332048007], ![-335396207477611030, -1898683874235121539, -6847854733155045752]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![24753427771, -6248406417, -2336865504]] ![![-137180298927453398510, -1523301751104473730, -5493989414391784437]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [32, 64, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 25, 41], [32, 77, 62], [0, 1]]
 g := ![![[56, 16, 28], [29, 23, 46], [20, 93, 79], [47, 49], [11, 81], [1]], ![[68, 68, 55, 15], [39, 29, 74, 9], [27, 88, 47, 28], [22, 59], [44, 29], [74, 0, 83, 14]], ![[50, 92, 53, 43], [102, 48, 35, 77], [86, 49, 57, 94], [88, 58], [75, 76], [3, 10, 24, 89]]]
 h' := ![![[62, 25, 41], [102, 55, 53], [81, 43, 47], [73, 42, 39], [54, 79, 7], [71, 39, 94], [0, 1]], ![[32, 77, 62], [15, 26, 53], [54, 75, 26], [26, 69, 90], [100, 40, 70], [90, 5, 82], [62, 25, 41]], ![[0, 1], [87, 22, 100], [87, 88, 30], [72, 95, 77], [101, 87, 26], [21, 59, 30], [32, 77, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 44], []]
 b := ![[], [47, 73, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [32, 64, 9, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64398054902, 47633971220, -82200277026]
  a := ![-65, 1, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-625223834, 462465740, -798060942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16159945951756796390541, -179446131540236592514, -647196227812909900596]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-16159945951756796390541, -179446131540236592514, -647196227812909900596]] 
 ![![107, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![-16159945951756796390541, -179446131540236592514, -647196227812909900596], ![-56485517951263397944366, -627236484246958776237, -2262211411675039233222], ![-20142187038690952852890, -223666437724691083836, -806682615787195368751]]]
  hmulB := by decide  
  f := ![![![292647229605, -88306236242, 12851637144]], ![![64324586798, -16653427913, -4905343422]], ![![2885926227, -1635114474, 2270055185]]]
  g := ![![![45824998411182268933, -179446131540236592514, -647196227812909900596], ![160176821017774176424, -627236484246958776237, -2262211411675039233222], ![57117498523898540001, -223666437724691083836, -806682615787195368751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![31, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![31, 1, 0]] 
 ![![107, 0, 0], ![31, 1, 0], ![36, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![31, 1, 0], ![1, 31, 9], ![87, -24, 32]]]
  hmulB := by decide  
  f := ![![![-1499, -54180, -15732], ![-856, 187036, 0]], ![![-444, -15684, -4554], ![-213, 54142, 0]], ![![-511, -18229, -5293], ![-265, 62928, 0]]]
  g := ![![![1, 0, 0], ![-31, 107, 0], ![-36, 0, 107]], ![![0, 1, 0], ![-12, 31, 9], ![-3, -24, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-52, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-52, 1, 0]] 
 ![![107, 0, 0], ![55, 1, 0], ![92, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-52, 1, 0], ![1, -52, 9], ![87, -24, -51]]]
  hmulB := by decide  
  f := ![![![1973, -164713, 28512], ![-2461, -338976, 0]], ![![1057, -84645, 14652], ![-1176, -174196, 0]], ![![1728, -141623, 24515], ![-2051, -291456, 0]]]
  g := ![![![1, 0, 0], ![-55, 107, 0], ![-92, 0, 107]], ![![-1, 1, 0], ![19, -52, 9], ![57, -24, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-16159945951756796390541, -179446131540236592514, -647196227812909900596]] ![![107, 0, 0], ![31, 1, 0]]
  ![![107, 0, 0], ![69, -30, 1]] where
 M := ![![![-1729114216837977213787887, -19200736074805315398998, -69249996375981359363772], ![-557443842455724086051137, -6190066561994293144171, -22325294473875246151698]]]
 hmul := by decide  
 g := ![![![![-11682667842719048237205, -2126088787643605354834, -582308139276130941852], ![-6943025473435348585608, 0, 0]], ![![-3766339544815311600761, -685423259866203246653, -187728539555317112244], ![-2238340741456315141590, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![69, -30, 1]] ![![107, 0, 0], ![-52, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5564, 107, 0]], ![![7383, -3210, 107], ![-3531, 1605, -321]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-52, 1, 0]]], ![![![69, -30, 1]], ![![-33, 15, -3]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-916, 1360, -3079]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-916, 1360, -3079]] 
 ![![109, 0, 0], ![0, 109, 0], ![42, 99, 1]] where
  M :=![![![-916, 1360, -3079], ![-266513, 72980, 9161], ![96767, -54193, 74340]]]
  hmulB := by decide  
  f := ![![![54328397, 603283, 2175820]], ![![189899623, 2108717, 7605367]], ![![194032768, 2154613, 7770897]]]
  g := ![![![1178, 2809, -3079], ![-5975, -7651, 9161], ![-27757, -68017, 74340]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [104, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 108], [0, 1]]
 g := ![![[12, 87], [84], [39, 71], [13, 78], [64], [60, 1]], ![[0, 22], [84], [48, 38], [6, 31], [64], [11, 108]]]
 h' := ![![[60, 108], [77, 95], [86, 53], [65, 17], [68, 29], [82, 8], [0, 1]], ![[0, 1], [0, 14], [105, 56], [104, 92], [64, 80], [17, 101], [60, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [50, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [104, 49, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-768, 3484, -9548]
  a := ![-2, 1, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3672, 8704, -9548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54328397, 603283, 2175820]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![54328397, 603283, 2175820]] 
 ![![109, 0, 0], ![89, 1, 0], ![101, 0, 1]] where
  M :=![![![54328397, 603283, 2175820], ![189899623, 2108717, 7605367], ![67716361, 751948, 2712000]]]
  hmulB := by decide  
  f := ![![![-916, 1360, -3079]], ![![-3193, 1780, -2430]], ![![39, 763, -2171]]]
  g := ![![![-2010290, 603283, 2175820], ![-7026773, 2108717, 7605367], ![-2505679, 751948, 2712000]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-916, 1360, -3079]] ![![54328397, 603283, 2175820]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-56, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-56, 1, 0]] 
 ![![113, 0, 0], ![57, 1, 0], ![66, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-56, 1, 0], ![1, -56, 9], ![87, -24, -55]]]
  hmulB := by decide  
  f := ![![![-39, 8510, -1368], ![226, 17176, 0]], ![![-19, 4255, -684], ![114, 8588, 0]], ![![2, 4970, -799], ![182, 10032, 0]]]
  g := ![![![1, 0, 0], ![-57, 113, 0], ![-66, 0, 113]], ![![-1, 1, 0], ![23, -56, 9], ![45, -24, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130929, 5834, -121404]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![130929, 5834, -121404]] 
 ![![113, 0, 0], ![62, 1, 0], ![25, 0, 1]] where
  M :=![![![130929, 5834, -121404], ![-10556314, 3044625, -68898], ![-342270, -989844, 3050459]]]
  hmulB := by decide  
  f := ![![![-9219305460963, -102374643170, -369227702568]], ![![-5343558613684, -59336889167, -214006345578]], ![![-2141361277857, -23778482842, -85760246077]]]
  g := ![![![24817, 5834, -121404], ![-1748678, 3044625, -68898], ![-134809, -989844, 3050459]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-7, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-7, 1, 0]] 
 ![![113, 0, 0], ![106, 1, 0], ![70, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-7, 1, 0], ![1, -7, 9], ![87, -24, -6]]]
  hmulB := by decide  
  f := ![![![-929, 6606, -8496], ![226, 106672, 0]], ![![-877, 6194, -7965], ![114, 100005, 0]], ![![-574, 4092, -5263], ![164, 66080, 0]]]
  g := ![![![1, 0, 0], ![-106, 113, 0], ![-70, 0, 113]], ![![-1, 1, 0], ![1, -7, 9], ![27, -24, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-56, 1, 0]] ![![130929, 5834, -121404]]
  ![![113, 0, 0], ![-9, -37, 1]] where
 M := ![![![14794977, 659242, -13718652]], ![![-17888338, 2717921, 6729726]]]
 hmul := by decide  
 g := ![![![![129975, 1912, -121298], ![-11978, 0, 0]]], ![![![-157925, 25610, 59513], ![4757, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-9, -37, 1]] ![![113, 0, 0], ![-7, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-791, 113, 0]], ![![-1017, -4181, 113], ![113, 226, -339]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-7, 1, 0]]], ![![![-9, -37, 1]], ![![1, 2, -3]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [41, 73, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 29, 62], [68, 97, 65], [0, 1]]
 g := ![![[16, 80, 19], [48, 89, 79], [31, 49, 94], [17, 40, 41], [10, 60, 50], [1]], ![[97, 43, 73, 15], [23, 107, 29, 38], [111, 8, 87, 88], [39, 30, 103, 32], [45, 9, 71, 81], [12, 97, 53, 76]], ![[18, 38, 11, 101], [8, 11, 15, 45], [115, 33, 30, 58], [76, 102, 115, 109], [111, 51, 68, 75], [41, 105, 99, 51]]]
 h' := ![![[106, 29, 62], [64, 87, 107], [126, 80, 98], [65, 119, 27], [98, 15, 26], [86, 54, 47], [0, 1]], ![[68, 97, 65], [93, 96, 25], [45, 1, 115], [115, 79, 91], [88, 123, 23], [26, 113, 33], [106, 29, 62]], ![[0, 1], [75, 71, 122], [20, 46, 41], [95, 56, 9], [95, 116, 78], [77, 87, 47], [68, 97, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 80], []]
 b := ![[], [109, 25, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [41, 73, 80, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346075, 112268, -580644]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2725, 884, -4572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-32, 15, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-32, 15, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![99, 15, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-32, 15, 1], ![102, -56, 136], ![1312, -353, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -15, 131]], ![![-1, 0, 1], ![-102, -16, 136], ![41, 2, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [118, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 130], [0, 1]]
 g := ![![[76, 108], [107, 38], [77], [75], [44], [63], [1]], ![[15, 23], [54, 93], [77], [75], [44], [63], [1]]]
 h' := ![![[71, 130], [81, 34], [117, 13], [65, 83], [111, 59], [71, 31], [13, 71], [0, 1]], ![[0, 1], [6, 97], [123, 118], [63, 48], [108, 72], [45, 100], [76, 60], [71, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [102, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [118, 60, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![58828, -12265, -1953]
  a := ![2, 19, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1925, 130, -1953]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-5, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-5, 1, 0]] 
 ![![131, 0, 0], ![126, 1, 0], ![41, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-5, 1, 0], ![1, -5, 9], ![87, -24, -4]]]
  hmulB := by decide  
  f := ![![![-2407, 12088, -21762], ![262, 316758, 0]], ![![-2314, 11623, -20925], ![263, 304575, 0]], ![![-752, 3783, -6811], ![117, 99138, 0]]]
  g := ![![![1, 0, 0], ![-126, 131, 0], ![-41, 0, 131]], ![![-1, 1, 0], ![2, -5, 9], ![25, -24, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-32, 15, 1]] ![![131, 0, 0], ![-5, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-655, 131, 0]], ![![-4192, 1965, 131], ![262, -131, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-5, 1, 0]]], ![![![-32, 15, 1]], ![![2, -1, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-31, 26, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-31, 26, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![106, 26, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-31, 26, 1], ![113, -55, 235], ![2269, -617, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -26, 137]], ![![-1, 0, 1], ![-181, -45, 235], ![39, 1, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [85, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 136], [0, 1]]
 g := ![![[127, 50], [130], [1], [4, 109], [105], [99], [1]], ![[20, 87], [130], [1], [42, 28], [105], [99], [1]]]
 h' := ![![[28, 136], [75, 18], [24, 33], [71, 1], [48, 71], [43, 67], [52, 28], [0, 1]], ![[0, 1], [31, 119], [126, 104], [99, 136], [118, 66], [1, 70], [14, 109], [28, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [5, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [85, 109, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6971, 4786, -8742]
  a := ![-2, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6713, 1694, -8742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![39, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![39, 1, 0]] 
 ![![137, 0, 0], ![39, 1, 0], ![29, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![39, 1, 0], ![1, 39, 9], ![87, -24, 40]]]
  hmulB := by decide  
  f := ![![![-14845, -679314, -156780], ![-9042, 2386540, 0]], ![![-4217, -193343, -44622], ![-2602, 679246, 0]], ![![-3166, -143797, -33187], ![-1831, 505180, 0]]]
  g := ![![![1, 0, 0], ![-39, 137, 0], ![-29, 0, 137]], ![![0, 1, 0], ![-13, 39, 9], ![-1, -24, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-31, 26, 1]] ![![137, 0, 0], ![39, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![5343, 137, 0]], ![![-4247, 3562, 137], ![-1096, 959, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![39, 1, 0]]], ![![![-31, 26, 1]], ![![-8, 7, 2]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB230I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB230I2 : PrimesBelowBoundCertificateInterval O 79 137 230 where
  m := 11
  g := ![3, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB230I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![18769, 137]
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
      exact NI89N1
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I89N0, I89N1, I97N1, I101N1, I107N0, I107N1, I107N2, I109N1, I113N0, I113N1, I113N2, I131N1, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N0, I89N1, I89N1], [I97N1], [I101N1], [], [I107N0, I107N1, I107N2], [I109N1], [I113N0, I113N1, I113N2], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
