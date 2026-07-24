
import IdealArithmetic.Examples.NF5_1_145800000_1.RI5_1_145800000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121352480, 60088794, 38435409, 20436133, 28751669]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![121352480, 60088794, 38435409, 20436133, 28751669]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![451, 331, 1, 0, 0], ![260, 262, 0, 1, 0], ![118, 251, 0, 0, 1]] where
  M :=![![![121352480, 60088794, 38435409, 20436133, 28751669], ![345020028, 170839833, 109276596, 58102440, 81744532], ![980934384, 485718660, 310686805, 165192384, 232409760], ![292309506, 144739734, 92581836, 49225825, 69255990], ![-123720633, -61261406, -39185463, -20834937, -29312748]]]
  hmulB := by decide  
  f := ![![![2518, -1196, 339, -511, 615]], ![![7380, 1179, -1092, -1656, -2044]], ![![7610, -301, -452, -1655, -869]], ![![5506, -8, -420, -1203, -794]], ![![4643, 315, -495, -1031, -928]]]
  g := ![![![-55501303, -54032050, 38435409, 20436133, 28751669], ![-157797032, -153619765, 109276596, 58102440, 81744532], ![-448636373, -436759889, 310686805, 165192384, 232409760], ![-133689550, -130150466, 92581836, 49225825, 69255990], ![56584392, 55086467, -39185463, -20834937, -29312748]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [324, 424, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 466], [0, 1]]
 g := ![![[353, 209], [162, 170], [1], [363], [156, 23], [212], [93, 432], [43, 1]], ![[0, 258], [0, 297], [1], [363], [211, 444], [212], [456, 35], [86, 466]]]
 h' := ![![[43, 466], [283, 26], [128, 388], [61, 466], [359, 42], [188, 81], [223, 408], [78, 124], [0, 1]], ![[0, 1], [0, 441], [0, 79], [18, 1], [297, 425], [402, 386], [21, 59], [273, 343], [43, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152]]
 b := ![[], [234, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [324, 424, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3021, -6419, -1115, -3221, -4280]
  a := ![0, -8, -9, -4, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3958, 4884, -1115, -3221, -4280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-904, 197, -44, 279, -27]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![-904, 197, -44, 279, -27]] 
 ![![467, 0, 0, 0, 0], ![298, 1, 0, 0, 0], ![393, 0, 1, 0, 0], ![413, 0, 0, 1, 0], ![231, 0, 0, 0, 1]] where
  M :=![![![-904, 197, -44, 279, -27], ![-324, -676, 449, -102, 1116], ![13392, -2427, 338, -4002, -408], ![-654, 2276, -1364, 797, -3226], ![-12945, 2208, -235, 3819, 620]]]
  hmulB := by decide  
  f := ![![![417773950, 206864621, 132319610, 70354431, 98981895]], ![![269131520, 133262952, 85240781, 45322584, 63764502]], ![![358805514, 177665856, 113642810, 60423963, 85010685]], ![![371620900, 184011513, 117701768, 62582114, 88046995]], ![![205738449, 101873289, 65162587, 34646994, 48744977]]]
  g := ![![![-324, 197, -44, 279, -27], ![-409, -676, 449, -102, 1116], ![5034, -2427, 338, -4002, -408], ![585, 2276, -1364, 797, -3226], ![-4923, 2208, -235, 3819, 620]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74477, -2430, 8132, 17610, 26254]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![-74477, -2430, 8132, 17610, 26254]] 
 ![![467, 0, 0, 0, 0], ![385, 1, 0, 0, 0], ![281, 0, 1, 0, 0], ![301, 0, 0, 1, 0], ![400, 0, 0, 0, 1]] where
  M :=![![![-74477, -2430, 8132, 17610, 26254], ![315048, -111233, 41434, -108732, 70440], ![845280, 119298, -149525, -174036, -434928], ![-1027380, 310192, -102328, 339769, -151244], ![-743814, -137232, 151702, 144066, 430891]]]
  hmulB := by decide  
  f := ![![![-1903863394507, -942715429182, -603001836884, -320616484518, -451076485946]], ![![-1581157012241, -782924402927, -500792538758, -266271731574, -374618657446]], ![![-1178533629793, -583561740732, -373271499229, -198468708606, -279226340414]], ![![-1236935416865, -612479921482, -391768826812, -208303750193, -293063295818]], ![![-1626561758378, -805406979600, -515173373750, -273918031266, -385376264001]]]
  g := ![![![-36887, -2430, 8132, 17610, 26254], ![77193, -111233, 41434, -108732, 70440], ![478133, 119298, -149525, -174036, -434928], ![-285803, 310192, -102328, 339769, -151244], ![-441666, -137232, 151702, 144066, 430891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2

def I467N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14034974167, -6949546247, -4445232379, -2363533064, -3325263172]] i)))

def SI467N3: IdealEqSpanCertificate' Table ![![-14034974167, -6949546247, -4445232379, -2363533064, -3325263172]] 
 ![![467, 0, 0, 0, 0], ![387, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![459, 0, 0, 0, 1]] where
  M :=![![![-14034974167, -6949546247, -4445232379, -2363533064, -3325263172], ![-39903158064, -19758414852, -12638342483, -6719815242, -9454132256], ![-113449587072, -56175603987, -35932362350, -19105261362, -26879260968], ![-33806942904, -16739818004, -10707516478, -5693193761, -8009774780], ![14308861944, 7085164270, 4531979572, 2409656604, 3390154545]]]
  hmulB := by decide  
  f := ![![![-8400437, 5422043, -2637563, 3591056, -5546988]], ![![-7103925, 4501605, -2178310, 3013266, -4565996]], ![![-2113254, 1427067, -702878, 921150, -1489632]], ![![154452, 136814, -99096, 595, -251260]], ![![-8639349, 5498563, -2664097, 3671304, -5588715]]]
  g := ![![![10371605320, -6949546247, -4445232379, -2363533064, -3325263172], ![29487749766, -19758414852, -12638342483, -6719815242, -9454132256], ![83837299959, -56175603987, -35932362350, -19105261362, -26879260968], ![24982751280, -16739818004, -10707516478, -5693193761, -8009774780], ![-10574003655, 7085164270, 4531979572, 2409656604, 3390154545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N3 : Nat.card (O ⧸ I467N3) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N3)

lemma isPrimeI467N3 : Ideal.IsPrime I467N3 := prime_ideal_of_norm_prime hp467.out _ NI467N3
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![121352480, 60088794, 38435409, 20436133, 28751669]] ![![-904, 197, -44, 279, -27]]
  ![![-35, 33, 1, 26, -6]] where
 M := ![![![-35, 33, 1, 26, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![-35, 33, 1, 26, -6]] ![![-74477, -2430, 8132, 17610, 26254]]
  ![![-8400437, 5422043, -2637563, 3591056, -5546988]] where
 M := ![![![-8400437, 5422043, -2637563, 3591056, -5546988]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N2 : IdealMulLeCertificate' Table 
  ![![-8400437, 5422043, -2637563, 3591056, -5546988]] ![![-14034974167, -6949546247, -4445232379, -2363533064, -3325263172]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![467, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1, I467N2, I467N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
    exact isPrimeI467N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0 ⊙ MulI467N1 ⊙ MulI467N2)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![614, 1736, -979, 501, -1135]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![614, 1736, -979, 501, -1135]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![320, 104, 53, 1, 0], ![426, 474, 4, 0, 1]] where
  M :=![![![614, 1736, -979, 501, -1135], ![-13620, 1583, 1102, 936, 2004], ![24048, -15390, 4523, -5412, 3744], ![14298, 2704, -3394, 311, -4610], ![-16437, 8016, -1805, 2943, -1126]]]
  hmulB := by decide  
  f := ![![![27556, 13646, 8727, 4641, 6527]], ![![78324, 38797, 24814, 13200, 18564]], ![![222768, 110274, 70561, 37500, 52800]], ![![60202, 29810, 19069, 10139, 14266]], ![![103815, 51420, 32887, 17493, 24602]]]
  g := ![![![676, 1018, -48, 501, -1135], ![-2436, -2183, -118, 936, 2004], ![336, -2562, 577, -5412, 3744], ![3922, 4500, -3, 311, -4610], ![-999, 492, -320, 2943, -1126]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [159, 95, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [391, 93, 405], [417, 385, 74], [0, 1]]
 g := ![![[347, 312, 44], [323, 163, 257], [385, 76, 66], [166, 461, 345], [85, 331, 108], [253, 192], [245, 273, 466], [1]], ![[191, 320, 144, 210], [245, 208, 345, 140], [419, 30, 459, 20], [474, 60, 371, 54], [444, 381, 67, 89], [424, 167], [228, 27, 269, 245], [125, 313, 210, 10]], ![[57, 191, 201, 195], [15, 256, 463, 148], [292, 409, 72, 62], [57, 136, 462, 29], [388, 320, 213, 425], [213, 18], [166, 335, 237, 367], [47, 7, 127, 469]]]
 h' := ![![[391, 93, 405], [375, 228, 116], [97, 205, 390], [430, 96, 32], [376, 0, 102], [395, 441, 293], [323, 272, 248], [320, 384, 329], [0, 1]], ![[417, 385, 74], [78, 240, 6], [359, 232, 381], [342, 436, 426], [439, 115, 471], [412, 201, 178], [462, 198, 149], [388, 435, 54], [391, 93, 405]], ![[0, 1], [404, 11, 357], [85, 42, 187], [219, 426, 21], [204, 364, 385], [247, 316, 8], [50, 9, 82], [405, 139, 96], [417, 385, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [475, 194], []]
 b := ![[], [401, 232, 391], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [159, 95, 150, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2903477043, 1815916786, -1074400976, 1135747326, -2143229812]
  a := ![3, -126, -124, -65, -310]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1141280331, 1878056630, -110012714, 1135747326, -2143229812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 63, 43, 20, 28]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![199, 63, 43, 20, 28]] 
 ![![479, 0, 0, 0, 0], ![187, 1, 0, 0, 0], ![477, 0, 1, 0, 0], ![368, 0, 0, 1, 0], ![353, 0, 0, 0, 1]] where
  M :=![![![199, 63, 43, 20, 28], ![336, 264, 111, 90, 80], ![960, 519, 434, 186, 360], ![552, 96, 122, 29, 84], ![-72, -22, -84, -12, -81]]]
  hmulB := by decide  
  f := ![![![-11911, 953, 463, 3196, 2196]], ![![-4595, 343, 194, 1226, 884]], ![![-11541, 942, 437, 3102, 2100]], ![![-9352, 818, 320, 2529, 1620]], ![![-9073, 703, 367, 2428, 1707]]]
  g := ![![![-103, 63, 43, 20, 28], ![-341, 264, 111, 90, 80], ![-1041, 519, 434, 186, 360], ![-242, 96, 122, 29, 84], ![161, -22, -84, -12, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N1 : Nat.card (O ⧸ I479N1) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N1)

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := prime_ideal_of_norm_prime hp479.out _ NI479N1

def I479N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1250, -603, -340, -201, -239]] i)))

def SI479N2: IdealEqSpanCertificate' Table ![![-1250, -603, -340, -201, -239]] 
 ![![479, 0, 0, 0, 0], ![453, 1, 0, 0, 0], ![282, 0, 1, 0, 0], ![277, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-1250, -603, -340, -201, -239], ![-2868, -1754, -1043, -606, -804], ![-9648, -4191, -3164, -1434, -2424], ![-3414, -1340, -820, -437, -554], ![1467, 324, 469, 111, 370]]]
  hmulB := by decide  
  f := ![![![98012, -5715, -5138, -25689, -21233]], ![![92160, -5153, -4969, -24093, -20295]], ![![55128, -3381, -2786, -14496, -11694]], ![![58558, -4039, -2680, -15524, -11753]], ![![14631, -648, -895, -3777, -3476]]]
  g := ![![![914, -603, -340, -201, -239], ![2718, -1754, -1043, -606, -804], ![6939, -4191, -3164, -1434, -2424], ![2065, -1340, -820, -437, -554], ![-690, 324, 469, 111, 370]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N2 : Nat.card (O ⧸ I479N2) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N2)

lemma isPrimeI479N2 : Ideal.IsPrime I479N2 := prime_ideal_of_norm_prime hp479.out _ NI479N2
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![614, 1736, -979, 501, -1135]] ![![199, 63, 43, 20, 28]]
  ![![123914, 61951, -49326, 14575, -62349]] where
 M := ![![![123914, 61951, -49326, 14575, -62349]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI479N1 : IdealMulLeCertificate' Table 
  ![![123914, 61951, -49326, 14575, -62349]] ![![-1250, -603, -340, -201, -239]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![2104247, -16388506, 8128630, -5005550, 8998494]]]
 hmul := by decide  
 g := ![![![![4393, -34214, 16970, -10450, 18786]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1, I479N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
    exact isPrimeI479N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0 ⊙ MulI479N1)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30464, 11782, -4647, 10803, -8345]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![-30464, 11782, -4647, 10803, -8345]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![266, 238, 363, 1, 0], ![289, 290, 250, 0, 1]] where
  M :=![![![-30464, 11782, -4647, 10803, -8345], ![-100140, -8567, 14240, 22188, 43212], ![518544, -164868, 56833, -173832, 88752], ![227574, 45776, -48778, -43013, -137494], ![-517083, 156036, -51451, 170985, -76004]]]
  hmulB := by decide  
  f := ![![![1834, 812, 127, 243, -31]], ![![-372, 2551, 1024, 948, 972]], ![![11664, 732, 4471, 312, 3792]], ![![9530, 2238, 3903, 829, 3284]], ![![6847, 2380, 2978, 870, 2505]]]
  g := ![![![-1011, -286, -3778, 10803, -8345], ![-37968, -36593, -38692, 22188, 43212], ![43344, 31764, 84127, -173832, 88752], ![105554, 102990, 102543, -43013, -137494], ![-49351, -37982, -88538, 170985, -76004]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [474, 72, 452, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [401, 16, 307], [121, 470, 180], [0, 1]]
 g := ![![[368, 204, 103], [189, 381, 50], [56, 251, 278], [417, 450], [39, 100], [214, 432, 164], [269, 336, 251], [1]], ![[350, 390, 475, 364], [382, 279, 350, 177], [457, 305, 434, 132], [121, 364], [163, 170], [232, 97, 48, 1], [185, 482, 364, 41], [168, 76, 415, 312]], ![[221, 392, 182, 346], [90, 448, 391, 20], [333, 31, 362, 320], [247, 235], [463, 386], [118, 39, 103, 346], [319, 271, 104, 243], [429, 212, 272, 175]]]
 h' := ![![[401, 16, 307], [22, 239, 432], [241, 458, 32], [184, 439, 256], [140, 194, 391], [347, 387, 10], [88, 266, 250], [13, 415, 35], [0, 1]], ![[121, 470, 180], [311, 291, 284], [419, 104, 293], [394, 367, 392], [144, 426, 315], [66, 282, 298], [148, 171, 466], [202, 78, 190], [401, 16, 307]], ![[0, 1], [265, 444, 258], [37, 412, 162], [362, 168, 326], [63, 354, 268], [146, 305, 179], [50, 50, 258], [75, 481, 262], [121, 470, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [313, 463], []]
 b := ![[], [451, 350, 357], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [474, 72, 452, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-344472, -451643, 749144, -66096, 1540262]
  a := ![1, -9, -9, -5, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-878642, -885825, -739884, -66096, 1540262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1834, -812, -127, -243, 31]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![-1834, -812, -127, -243, 31]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![355, 257, 1, 0, 0], ![297, 9, 0, 1, 0], ![330, 406, 0, 0, 1]] where
  M :=![![![-1834, -812, -127, -243, 31], ![372, -2551, -1024, -948, -972], ![-11664, -732, -4471, -312, -3792], ![-7770, -1060, -294, -205, 278], ![3657, -1602, 1127, -543, 986]]]
  hmulB := by decide  
  f := ![![![30464, -11782, 4647, -10803, 8345]], ![![100140, 8567, -14240, -22188, -43212]], ![![73988, -3729, -4244, -19227, -16903]], ![![19962, -7121, 2671, -6910, 4573]], ![![105189, -1162, -8617, -26169, -30214]]]
  g := ![![![216, 44, -127, -243, 31], ![1984, 1363, -1024, -948, -972], ![5995, 5525, -4471, -312, -3792], ![135, -75, -294, -205, 278], ![-1151, -1410, 1127, -543, 986]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P1 : CertificateIrreducibleZModOfList' 487 2 2 8 [274, 424, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 486], [0, 1]]
 g := ![![[453, 16], [351, 64], [272, 141], [460], [77], [448, 397], [262, 467], [63, 1]], ![[0, 471], [0, 423], [389, 346], [460], [77], [135, 90], [463, 20], [126, 486]]]
 h' := ![![[63, 486], [252, 483], [470, 8], [213, 221], [140, 66], [459, 442], [288, 408], [270, 286], [0, 1]], ![[0, 1], [0, 4], [0, 479], [13, 266], [402, 421], [59, 45], [181, 79], [269, 201], [63, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [338]]
 b := ![[], [277, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N1 : CertifiedPrimeIdeal' SI487N1 487 where
  n := 2
  hpos := by decide
  P := [274, 424, 1]
  hirr := P487P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107964, -69915, 95526, -44025, 198666]
  a := ![1, 44, 48, 18, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-177183, -215364, 95526, -44025, 198666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N1 B_one_repr
lemma NI487N1 : Nat.card (O ⧸ I487N1) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![-30464, 11782, -4647, 10803, -8345]] ![![-1834, -812, -127, -243, 31]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![-487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43995064, 21784560, 13934353, 7408905, 10423615]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![43995064, 21784560, 13934353, 7408905, 10423615]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![118, 437, 1, 0, 0], ![80, 107, 0, 1, 0], ![251, 128, 0, 0, 1]] where
  M :=![![![43995064, 21784560, 13934353, 7408905, 10423615], ![125083380, 61936183, 39617080, 21064428, 29635620], ![355627440, 176092188, 112636231, 59888760, 84257712], ![105973734, 52473868, 33564570, 17846305, 25108030], ![-44853615, -22209678, -14206277, -7553487, -10627028]]]
  hmulB := by decide  
  f := ![![![2546, -966, 339, -927, 301]], ![![3612, 1733, -1592, 228, -3708]], ![![3736, 1331, -1339, 6, -3226]], ![![1202, 205, -282, -107, -738]], ![![2327, -58, -240, -438, -817]]]
  g := ![![![-9794905, -16689416, 13934353, 7408905, 10423615], ![-27848120, -47450063, 39617080, 21064428, 29635620], ![-79175630, -134906365, 112636231, 59888760, 84257712], ![-23593616, -40200867, 33564570, 17846305, 25108030], ![9986049, 17015104, -14206277, -7553487, -10627028]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 2 2 8 [84, 425, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 490], [0, 1]]
 g := ![![[385, 12], [214, 38], [255], [440, 381], [83], [82, 290], [146, 5], [66, 1]], ![[195, 479], [267, 453], [255], [54, 110], [83], [73, 201], [476, 486], [132, 490]]]
 h' := ![![[66, 490], [191, 265], [242, 468], [356, 257], [98, 390], [477, 322], [11, 205], [348, 344], [0, 1]], ![[0, 1], [5, 226], [197, 23], [133, 234], [306, 101], [125, 169], [284, 286], [466, 147], [66, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [417, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 2
  hpos := by decide
  P := [84, 425, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32840, -17312, 1152, -10708, -4400]
  a := ![-1, -7, -14, 5, -38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3784, 2420, 1152, -10708, -4400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-964, -5, 122, 75, 185]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![-964, -5, 122, 75, 185]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![195, 101, 1, 0, 0], ![400, 215, 0, 1, 0], ![272, 170, 0, 0, 1]] where
  M :=![![![-964, -5, 122, 75, 185], ![2220, -1078, 255, -378, 300], ![3600, 1707, -1156, -270, -1512], ![-4134, 1272, -140, 545, -330], ![-2445, -912, 597, 447, 848]]]
  hmulB := by decide  
  f := ![![![-96841766, -47952089, -30672244, -16308453, -22944421]], ![![-275333052, -136333688, -87204963, -46366938, -65233812]], ![![-96691626, -47877746, -30624691, -16283169, -22908849]], ![![-199931938, -98998134, -63323517, -33669157, -47369258]], ![![-148775657, -73667632, -47121025, -25054281, -35248958]]]
  g := ![![![-214, -122, 122, 75, 185], ![45, 7, 255, -378, 300], ![1524, 883, -1156, -270, -1512], ![-214, -93, -140, 545, -330], ![-1076, -614, 597, 447, 848]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P1 : CertificateIrreducibleZModOfList' 491 2 2 8 [307, 410, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 490], [0, 1]]
 g := ![![[334, 239], [26, 36], [163], [95, 269], [241], [17, 97], [406, 438], [81, 1]], ![[53, 252], [487, 455], [163], [280, 222], [241], [18, 394], [41, 53], [162, 490]]]
 h' := ![![[81, 490], [365, 132], [159, 485], [295, 60], [381, 112], [182, 350], [72, 382], [174, 362], [0, 1]], ![[0, 1], [255, 359], [164, 6], [245, 431], [124, 379], [54, 141], [81, 109], [36, 129], [81, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [260]]
 b := ![[], [136, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N1 : CertifiedPrimeIdeal' SI491N1 491 where
  n := 2
  hpos := by decide
  P := [307, 410, 1]
  hirr := P491P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27043, -6284, 3356, -14640, 4816]
  a := ![0, -4, 8, -18, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7981, 4040, 3356, -14640, 4816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N1 B_one_repr
lemma NI491N1 : Nat.card (O ⧸ I491N1) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N1

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -1, 0, -2]] i)))

def SI491N2: IdealEqSpanCertificate' Table ![![1, 1, -1, 0, -2]] 
 ![![491, 0, 0, 0, 0], ![444, 1, 0, 0, 0], ![246, 0, 1, 0, 0], ![232, 0, 0, 1, 0], ![344, 0, 0, 0, 1]] where
  M :=![![![1, 1, -1, 0, -2], ![-24, 4, -1, 6, 0], ![0, -21, 10, -6, 24], ![60, -10, 0, -17, -4], ![-6, 18, -10, 6, -23]]]
  hmulB := by decide  
  f := ![![![359, -149, -5, -60, -26]], ![![324, -134, -5, -54, -24]], ![![174, -75, -2, -30, -12]], ![![172, -72, -2, -29, -12]], ![![254, -104, -4, -42, -19]]]
  g := ![![![1, 1, -1, 0, -2], ![-6, 4, -1, 6, 0], ![0, -21, 10, -6, 24], ![20, -10, 0, -17, -4], ![2, 18, -10, 6, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![43995064, 21784560, 13934353, 7408905, 10423615]] ![![-964, -5, 122, 75, 185]]
  ![![359, -149, -5, -60, -26]] where
 M := ![![![359, -149, -5, -60, -26]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI491N1 : IdealMulLeCertificate' Table 
  ![![359, -149, -5, -60, -26]] ![![1, 1, -1, 0, -2]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1, I491N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
    exact isPrimeI491N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0 ⊙ MulI491N1)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, -3, 0, -7, -1]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![22, -3, 0, -7, -1]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![72, 424, 1, 0, 0], ![401, 73, 0, 1, 0], ![165, 490, 0, 0, 1]] where
  M :=![![![22, -3, 0, -7, -1], ![-12, 18, -11, 6, -28], ![-336, 45, -4, 102, 24], ![54, -62, 34, -31, 82], ![333, -46, 1, -99, -30]]]
  hmulB := by decide  
  f := ![![![-8, -59, 2, -19, 5]], ![![60, -36, -73, -18, -76]], ![![48, -39, -62, -18, -64]], ![![2, -53, -9, -18, -7]], ![![57, -55, -71, -24, -73]]]
  g := ![![![6, 2, 0, -7, -1], ![6, 36, -11, 6, -28], ![-90, -35, -4, 102, 24], ![-7, -105, 34, -31, 82], ![90, 43, 1, -99, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 2 2 8 [142, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [350, 498], [0, 1]]
 g := ![![[363, 123], [354, 421], [39], [287], [127, 45], [133, 47], [373, 130], [350, 1]], ![[0, 376], [0, 78], [39], [287], [408, 454], [116, 452], [464, 369], [201, 498]]]
 h' := ![![[350, 498], [131, 98], [437, 445], [74, 312], [429, 423], [76, 150], [427, 394], [200, 103], [0, 1]], ![[0, 1], [0, 401], [0, 54], [492, 187], [276, 76], [181, 349], [104, 105], [322, 396], [350, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [19, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 2
  hpos := by decide
  P := [142, 149, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25057, -12563, 3898, -8891, 4747]
  a := ![13, -8, -13, 2, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5063, -6698, 3898, -8891, 4747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64984406, -32177625, -20582210, -10943575, -15396555]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-64984406, -32177625, -20582210, -10943575, -15396555]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![190, 33, 1, 0, 0], ![452, 17, 0, 1, 0], ![143, 339, 0, 0, 1]] where
  M :=![![![-64984406, -32177625, -20582210, -10943575, -15396555], ![-184758660, -91484946, -58517755, -31113930, -43774300], ![-525291600, -260102955, -166373176, -88460730, -124455720], ![-156532110, -77508310, -49577690, -26360491, -37086670], ![66252555, 32805560, 20983865, 11157135, 15697014]]]
  hmulB := by decide  
  f := ![![![1096, 1375, -860, 425, -905]], ![![-10860, 1656, 895, 270, 1700]], ![![-260, 607, -261, 170, -230]], ![![638, 1308, -755, 399, -770]], ![![-7093, 1531, 360, 310, 899]]]
  g := ![![![22031741, 12129275, -20582210, -10943575, -15396555], ![62638950, 34485021, -58517755, -31113930, -43774300], ![178090240, 98045157, -166373176, -88460730, -124455720], ![53069268, 29216563, -49577690, -26360491, -37086670], ![-22461683, -12365974, 20983865, 11157135, 15697014]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [208, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [469, 498], [0, 1]]
 g := ![![[360, 423], [393, 111], [404], [122], [397, 215], [490, 84], [257, 323], [469, 1]], ![[145, 76], [57, 388], [404], [122], [434, 284], [465, 415], [48, 176], [439, 498]]]
 h' := ![![[469, 498], [92, 315], [345, 333], [270, 109], [258, 163], [375, 240], [436, 87], [252, 193], [0, 1]], ![[0, 1], [123, 184], [335, 166], [493, 390], [358, 336], [161, 259], [321, 412], [450, 306], [469, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [161, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal' SI499N1 499 where
  n := 2
  hpos := by decide
  P := [208, 30, 1]
  hirr := P499P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-508, 45, 58, 151, 140]
  a := ![-1, -4, -2, -4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-200, -104, 58, 151, 140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N1 B_one_repr
lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-913, 326, -38, 126, 10]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![-913, 326, -38, 126, 10]] 
 ![![499, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![232, 0, 1, 0, 0], ![351, 0, 0, 1, 0], ![238, 0, 0, 0, 1]] where
  M :=![![![-913, 326, -38, 126, 10], ![120, -931, 462, -288, 504], ![6048, -294, -715, -252, -1152], ![-2364, 1650, -514, 581, -420], ![-2802, -210, 516, -6, 743]]]
  hmulB := by decide  
  f := ![![![-154091263, -76299698, -48804610, -25949442, -36508366]], ![![-13847562, -6856747, -4385874, -2331972, -3280860]], ![![-74137768, -36709994, -23481311, -12485028, -17565232]], ![![-109132671, -54038040, -34565084, -18378277, -25856466]], ![![-73179604, -36235550, -23177836, -12323670, -17338217]]]
  g := ![![![-105, 326, -38, 126, 10], ![-174, -931, 462, -288, 504], ![1096, -294, -715, -252, -1152], ![-113, 1650, -514, 581, -420], ![-578, -210, 516, -6, 743]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![22, -3, 0, -7, -1]] ![![-64984406, -32177625, -20582210, -10943575, -15396555]]
  ![![154091263, 76299698, 48804610, 25949442, 36508366]] where
 M := ![![![154091263, 76299698, 48804610, 25949442, 36508366]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![154091263, 76299698, 48804610, 25949442, 36508366]] ![![-913, 326, -38, 126, 10]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1, I499N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
    exact isPrimeI499N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0 ⊙ MulI499N1)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4519, -2644, -1394, -896, -1014]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![-4519, -2644, -1394, -896, -1014]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![0, 0, 503, 0, 0], ![466, 430, 197, 1, 0], ![119, 207, 368, 0, 1]] where
  M :=![![![-4519, -2644, -1394, -896, -1014], ![-12168, -6555, -4554, -2280, -3584], ![-43008, -17358, -12419, -5820, -9120], ![-12156, -6510, -3106, -2159, -2088], ![7530, 1636, 1554, 498, 1017]]]
  hmulB := by decide  
  f := ![![![331, 360, -254, 20, -638]], ![![-7656, 1503, -258, 2304, 80]], ![![960, -6366, 3887, -2028, 9216]], ![![-5818, -882, 1067, 1181, 3084]], ![![-2375, -3941, 2670, -526, 6607]]]
  g := ![![![1061, 1178, 1090, -896, -1014], ![2936, 3411, 3506, -2280, -3584], ![7464, 8694, 8927, -5820, -9120], ![2470, 2692, 2367, -2159, -2088], ![-687, -841, -936, 498, 1017]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 3 2 8 [98, 372, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [396, 278, 315], [65, 224, 188], [0, 1]]
 g := ![![[191, 436, 43], [33, 53, 131], [75, 250, 141], [18, 183], [222, 405, 435], [278, 230, 366], [499, 418, 255], [1]], ![[391, 114, 288, 395], [272, 39, 90, 110], [48, 21, 21, 157], [54, 308], [375, 88, 446, 111], [422, 187, 488, 314], [255, 464, 495, 35], [351, 164, 345, 461]], ![[148, 427, 243, 39], [452, 33, 199, 483], [273, 324, 217, 336], [261, 271], [21, 394, 138, 84], [230, 121, 147, 18], [231, 257, 282, 389], [75, 112, 259, 42]]]
 h' := ![![[396, 278, 315], [287, 435, 272], [195, 405, 159], [281, 170, 101], [376, 140, 85], [421, 43, 223], [392, 308, 236], [405, 131, 461], [0, 1]], ![[65, 224, 188], [76, 217, 274], [163, 279, 219], [313, 356, 221], [64, 34, 265], [21, 363, 119], [492, 305, 493], [71, 249, 168], [396, 278, 315]], ![[0, 1], [120, 354, 460], [30, 322, 125], [56, 480, 181], [22, 329, 153], [125, 97, 161], [217, 393, 277], [182, 123, 377], [65, 224, 188]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [253, 299], []]
 b := ![[], [180, 7, 427], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 3
  hpos := by decide
  P := [98, 372, 42, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![635099, -139417, 67107, -180985, 77342]
  a := ![3, 3, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![150637, 122613, 14432, -180985, 77342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 127263527 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 360, -254, 20, -638]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![331, 360, -254, 20, -638]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![246, 327, 1, 0, 0], ![174, 328, 0, 1, 0], ![138, 310, 0, 0, 1]] where
  M :=![![![331, 360, -254, 20, -638], ![-7656, 1503, -258, 2304, 80], ![960, -6366, 3887, -2028, 9216], ![22260, -3594, 266, -6481, -1392], ![-2502, 6404, -3774, 2418, -8805]]]
  hmulB := by decide  
  f := ![![![-4519, -2644, -1394, -896, -1014]], ![![-12168, -6555, -4554, -2280, -3584]], ![![-10206, -5589, -3667, -1932, -2844]], ![![-9522, -5202, -3458, -1801, -2692]], ![![-8724, -4762, -3186, -1650, -2485]]]
  g := ![![![293, 546, -254, 20, -638], ![-708, -1381, -258, 2304, 80], ![-3726, -6897, 3887, -2028, 9216], ![2538, 4904, 266, -6481, -1392], ![3420, 6316, -3774, 2418, -8805]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [258, 210, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [293, 502], [0, 1]]
 g := ![![[71, 271], [203, 286], [253, 91], [56], [411, 443], [15, 104], [220, 22], [293, 1]], ![[0, 232], [0, 217], [257, 412], [56], [436, 60], [307, 399], [127, 481], [83, 502]]]
 h' := ![![[293, 502], [441, 153], [116, 379], [110, 40], [95, 168], [154, 403], [79, 46], [359, 81], [0, 1]], ![[0, 1], [0, 350], [0, 124], [261, 463], [25, 335], [28, 100], [479, 457], [451, 422], [293, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [323]]
 b := ![[], [107, 413]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [258, 210, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14830, -5531, 5782, -6173, 12076]
  a := ![1, 6, 10, -2, 27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3976, -7187, 5782, -6173, 12076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![-4519, -2644, -1394, -896, -1014]] ![![331, 360, -254, 20, -638]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194839, -96480, -61712, -32814, -46164]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![-194839, -96480, -61712, -32814, -46164]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![369, 20, 1, 0, 0], ![297, 165, 0, 1, 0], ![211, 8, 0, 0, 1]] where
  M :=![![![-194839, -96480, -61712, -32814, -46164], ![-553968, -274297, -175458, -93288, -131256], ![-1575072, -779862, -498841, -265212, -373152], ![-469320, -232410, -148642, -79045, -111180], ![198720, 98352, 62916, 33432, 47057]]]
  hmulB := by decide  
  f := ![![![-7355, 5460, -1772, 1890, -1572]], ![![-18864, -6065, 5778, -1200, 7560]], ![![-5895, 3670, -1057, 1302, -852]], ![![-10407, 1257, 820, 725, 1512]], ![![-3445, 2188, -640, 774, -523]]]
  g := ![![![82639, 13598, -61712, -32814, -46164], ![234954, 38659, -175458, -93288, -131256], ![667977, 109906, -498841, -265212, -373152], ![199047, 32755, -148642, -79045, -111180], ![-84235, -13856, 62916, 33432, 47057]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 2 2 8 [198, 496, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 508], [0, 1]]
 g := ![![[275, 268], [123], [133, 372], [108, 400], [50, 26], [393, 102], [399, 332], [13, 1]], ![[196, 241], [123], [388, 137], [218, 109], [388, 483], [192, 407], [134, 177], [26, 508]]]
 h' := ![![[13, 508], [219, 461], [134, 387], [503, 95], [280, 489], [63, 434], [402, 354], [480, 480], [0, 1]], ![[0, 1], [104, 48], [75, 122], [211, 414], [20, 20], [106, 75], [423, 155], [103, 29], [13, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [259]]
 b := ![[], [49, 384]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 2
  hpos := by decide
  P := [198, 496, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2354, -33, -498, 461, -1014]
  a := ![4, 0, -1, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![517, -114, -498, 461, -1014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![350803, -71707, -12463, -33498, -33840]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![350803, -71707, -12463, -33498, -33840]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![282, 394, 1, 0, 0], ![315, 49, 0, 1, 0], ![38, 244, 0, 0, 1]] where
  M :=![![![350803, -71707, -12463, -33498, -33840], ![-406080, 381436, -139045, 128262, -133992], ![-1607904, -292977, 375706, -30318, 513048], ![1229136, -532426, 101148, -201473, 46784], ![643848, 275574, -230944, 57060, -296237]]]
  hmulB := by decide  
  f := ![![![663343058640623, 328460402157281, 210097575279451, 111709022875110, 157163826321168]], ![![1885965915854016, 933853328390582, 597333251353559, 317602493749698, 446836091500440]], ![![1837908342792030, 910057180124569, 582112198773572, 309509449798194, 435449958838392]], ![![595212633282345, 294724996893245, 188518941141234, 100235648509159, 141021894633304]], ![![952271968024058, 471526202778498, 301608690831024, 160365544907220, 225618862281835]]]
  g := ![![![30851, 28953, -12463, -33498, -33840], ![6864, 160264, -139045, 128262, -133992], ![-230850, -534419, 375706, -30318, 513048], ![67567, -82373, 101148, -201473, 46784], ![116018, 315822, -230944, 57060, -296237]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [283, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [487, 508], [0, 1]]
 g := ![![[99, 237], [439], [231, 278], [174, 353], [174, 465], [198, 371], [500, 190], [487, 1]], ![[484, 272], [439], [223, 231], [43, 156], [124, 44], [180, 138], [392, 319], [465, 508]]]
 h' := ![![[487, 508], [445, 42], [288, 84], [131, 473], [131, 380], [465, 90], [2, 54], [118, 201], [0, 1]], ![[0, 1], [30, 467], [476, 425], [414, 36], [424, 129], [12, 419], [341, 455], [277, 308], [487, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [121, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N1 : CertifiedPrimeIdeal' SI509N1 509 where
  n := 2
  hpos := by decide
  P := [283, 22, 1]
  hirr := P509P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15450, 6517, 3142, 7913, 5530]
  a := ![7, -19, -18, -23, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7081, -5832, 3142, 7913, 5530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N1 B_one_repr
lemma NI509N1 : Nat.card (O ⧸ I509N1) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N1

def I509N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![663369977, 328473731, 210106101, 111713556, 157170204]] i)))

def SI509N2: IdealEqSpanCertificate' Table ![![663369977, 328473731, 210106101, 111713556, 157170204]] 
 ![![509, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![498, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![663369977, 328473731, 210106101, 111713556, 157170204], ![1886042448, 933891224, 597357491, 317615382, 446854224], ![5362250688, 2655167631, 1698360830, 903019602, 1270461528], ![1597901832, 791215754, 506096048, 269091611, 378585956], ![-676315416, -334883784, -214206250, -113893608, -160237327]]]
  hmulB := by decide  
  f := ![![![3445, -145, 271, -660, 3564]], ![![727, -41, 56, -162, 660]], ![![865, 38, 15, -114, 804]], ![![3018, -86, 260, -529, 3532]], ![![644, -134, 108, -180, 689]]]
  g := ![![![-249321133, 328473731, 210106101, 111713556, 157170204], ![-708850651, 933891224, 597357491, 317615382, 446854224], ![-2015349599, 2655167631, 1698360830, 903019602, 1270461528], ![-600555812, 791215754, 506096048, 269091611, 378585956], ![254186550, -334883784, -214206250, -113893608, -160237327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N2 : Nat.card (O ⧸ I509N2) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N2)

lemma isPrimeI509N2 : Ideal.IsPrime I509N2 := prime_ideal_of_norm_prime hp509.out _ NI509N2
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![-194839, -96480, -61712, -32814, -46164]] ![![350803, -71707, -12463, -33498, -33840]]
  ![![-3445, 145, -271, 660, -3564]] where
 M := ![![![-3445, 145, -271, 660, -3564]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI509N1 : IdealMulLeCertificate' Table 
  ![![-3445, 145, -271, 660, -3564]] ![![663369977, 328473731, 210106101, 111713556, 157170204]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![-509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1, I509N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
    exact isPrimeI509N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0 ⊙ MulI509N1)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4881290, 5662919, -3967466, 396001, -9940879]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![4881290, 5662919, -3967466, 396001, -9940879]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![483, 5, 101, 1, 0], ![26, 351, 330, 0, 1]] where
  M :=![![![4881290, 5662919, -3967466, 396001, -9940879], ![-119290548, 23197530, -3881959, 35840478, 1584004], ![19008048, -99847959, 60622012, -32795778, 143361912], ![346369098, -55266670, 3727342, -100660139, -22655854], ![-42896937, 100377244, -58830679, 38813619, -136896618]]]
  hmulB := by decide  
  f := ![![![-1998635004896, -989642461635, -633018410196, -336576316837, -473530431495]], ![![-5682365177940, -2813675257836, -1799749209967, -956927872206, -1346305267348]], ![![-16155663208176, -7999624878003, -5116908397390, -2720663655714, -3827711488824]], ![![-5048538882282, -2499830351708, -1599000342373, -850189563518, -1196134756731]], ![![-14157017099033, -7009976917940, -4483886470160, -2384085468865, -3354178426398]]]
  g := ![![![138341, 6704283, 6212143, 396001, -9940879], ![-33534406, -1366584, -7958717, 35840478, 1584004], ![23285910, -96460461, -84330970, -32795778, 143361912], ![95113759, 16123299, 33871081, -100660139, -22655854], ![-29233326, 92048027, 79072702, 38813619, -136896618]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 3 2 9 [286, 360, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [465, 449, 383], [417, 71, 138], [0, 1]]
 g := ![![[135, 376, 360], [379, 8], [61, 260], [439, 186, 338], [373, 273], [513, 258], [62, 161], [361, 1], []], ![[64, 392, 520, 58], [238, 113], [253, 105], [507, 271, 473, 200], [268, 47], [14, 296], [89, 219], [490, 352], [363, 288]], ![[283, 465, 112, 267], [497, 513], [149, 311], [75, 5, 114, 400], [485, 246], [8, 235], [456, 1], [72, 495], [87, 288]]]
 h' := ![![[465, 449, 383], [431, 415, 336], [317, 383, 498], [7, 246, 342], [363, 469, 410], [310, 371, 362], [432, 223, 193], [433, 4, 232], [0, 0, 1], [0, 1]], ![[417, 71, 138], [14, 351, 451], [71, 140, 218], [465, 192, 233], [401, 209, 337], [45, 118, 33], [38, 318, 122], [499, 304, 290], [392, 290, 71], [465, 449, 383]], ![[0, 1], [329, 276, 255], [58, 519, 326], [294, 83, 467], [450, 364, 295], [121, 32, 126], [357, 501, 206], [249, 213, 520], [1, 231, 449], [417, 71, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [215, 150], []]
 b := ![[], [270, 103, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 3
  hpos := by decide
  P := [286, 360, 160, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84456, 33577, 9232, 41012, 15894]
  a := ![1, -3, -3, -5, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38976, -11037, -18000, 41012, 15894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 141420761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5775662845, 2859872454, 1829298948, 972639488, 1368409996]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![5775662845, 2859872454, 1829298948, 972639488, 1368409996]] 
 ![![521, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![511, 0, 1, 0, 0], ![239, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![5775662845, 2859872454, 1829298948, 972639488, 1368409996], ![16420919952, 8130969189, 5200921938, 2765333712, 3890557952], ![46686695424, 23117345622, 14786860853, 7862183916, 11061334848], ![13912209720, 6888758298, 4406349762, 2342859149, 3296176968], ![-5888372940, -2915681890, -1864997094, -991620216, -1395114051]]]
  hmulB := by decide  
  f := ![![![-440179, -58414, 75456, 91840, 220596]], ![![-42232, -7783, 8598, 8200, 24416]], ![![-423269, -54536, 71537, 88772, 209676]], ![![-217837, -22744, 33498, 47181, 99972]], ![![-31555, -6200, 6666, 6016, 18825]]]
  g := ![![![-2612847763, 2859872454, 1829298948, 972639488, 1368409996], ![-7428647606, 8130969189, 5200921938, 2765333712, 3890557952], ![-21120558967, 23117345622, 14786860853, 7862183916, 11061334848], ![-6293734073, 6888758298, 4406349762, 2342859149, 3296176968], ![2663836597, -2915681890, -1864997094, -991620216, -1395114051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N1)

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := prime_ideal_of_norm_prime hp521.out _ NI521N1

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -23, -30, -9, -27]] i)))

def SI521N2: IdealEqSpanCertificate' Table ![![-44, -23, -30, -9, -27]] 
 ![![521, 0, 0, 0, 0], ![380, 1, 0, 0, 0], ![438, 0, 1, 0, 0], ![204, 0, 0, 1, 0], ![474, 0, 0, 0, 1]] where
  M :=![![![-44, -23, -30, -9, -27], ![-324, -62, -59, -18, -36], ![-432, -411, -116, -138, -72], ![18, -86, -74, -35, -74], ![-33, 114, -5, 39, -8]]]
  hmulB := by decide  
  f := ![![![-1666, 2107, -1168, 1005, -2643]], ![![-1276, 1544, -851, 750, -1920]], ![![-1308, 1707, -950, 804, -2154]], ![![-486, 812, -464, 349, -1066]], ![![-1617, 1980, -1093, 957, -2468]]]
  g := ![![![70, -23, -30, -9, -27], ![134, -62, -59, -18, -36], ![516, -411, -116, -138, -72], ![206, -86, -74, -35, -74], ![-87, 114, -5, 39, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N2 : Nat.card (O ⧸ I521N2) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N2)

lemma isPrimeI521N2 : Ideal.IsPrime I521N2 := prime_ideal_of_norm_prime hp521.out _ NI521N2
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![4881290, 5662919, -3967466, 396001, -9940879]] ![![5775662845, 2859872454, 1829298948, 972639488, 1368409996]]
  ![![-1666, 2107, -1168, 1005, -2643]] where
 M := ![![![-1666, 2107, -1168, 1005, -2643]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N1 : IdealMulLeCertificate' Table 
  ![![-1666, 2107, -1168, 1005, -2643]] ![![-44, -23, -30, -9, -27]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1, I521N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
    exact isPrimeI521N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0 ⊙ MulI521N1)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7229726, -11440634, 6497443, -4998821, 14892097]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![7229726, -11440634, 6497443, -4998821, 14892097]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![196, 40, 1, 0, 0], ![88, 28, 0, 1, 0], ![148, 386, 0, 0, 1]] where
  M :=![![![7229726, -11440634, 6497443, -4998821, 14892097], ![178705164, -22953057, -1547358, -50367924, -19995284], ![-239943408, 183681018, -93316265, 110687556, -201471696], ![-492295974, 44011602, 16256492, 133339393, 83789346], ![266677599, -180570776, 89000991, -116379189, 188706138]]]
  hmulB := by decide  
  f := ![![![497552292447908, 246367583022016, 157587433615829, 83789345037439, 117883531089091]], ![![1414602373069092, 700453345065561, 448040459148546, 238223415160428, 335157380149756]], ![![302344613392640, 149708709560542, 95760209359503, 50915768083648, 71633577361556]], ![![161743698501146, 80088876432898, 51228332654088, 27238139120345, 38321435957846]], ![![1183875704456987, 586206918011624, 374963469804545, 199368330500767, 280492021703532]]]
  g := ![![![-5794270, -11242296, 6497443, -4998821, 14892097], ![15054812, 17528533, -1547358, -50367924, -19995284], ![72901244, 150258422, -93316265, 110687556, -201471696], ![-53180226, -70138506, 16256492, 133339393, 83789346], ![-66662823, -140196104, 89000991, -116379189, 188706138]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 2 2 9 [457, 495, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 522], [0, 1]]
 g := ![![[254, 105], [193, 1], [216], [303, 435], [130], [40], [441], [261], [1]], ![[56, 418], [221, 522], [216], [454, 88], [130], [40], [441], [261], [1]]]
 h' := ![![[28, 522], [186, 378], [344, 1], [124, 138], [293, 459], [514, 322], [311, 404], [139, 21], [66, 28], [0, 1]], ![[0, 1], [310, 145], [372, 522], [327, 385], [70, 64], [116, 201], [117, 119], [204, 502], [327, 495], [28, 522]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [521]]
 b := ![[], [14, 522]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 2
  hpos := by decide
  P := [457, 495, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2885, 5467, 2223, 7496, 5764]
  a := ![3, 8, 4, 11, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3731, -4815, 2223, 7496, 5764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 273529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, -78, 58, 2, 148]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![-101, -78, 58, 2, 148]] 
 ![![523, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![358, 0, 1, 0, 0], ![426, 0, 0, 1, 0], ![202, 0, 0, 0, 1]] where
  M :=![![![-101, -78, 58, 2, 148], ![1776, -369, 72, -540, 8], ![96, 1428, -901, 384, -2160], ![-5208, 894, -94, 1529, 252], ![288, -1444, 876, -480, 2067]]]
  hmulB := by decide  
  f := ![![![-4067999, -2014322, -1288402, -685066, -963780]], ![![-1048836, -519345, -332184, -176628, -248488]], ![![-2847470, -1409960, -901841, -479524, -674616]], ![![-3332250, -1650006, -1055378, -561163, -789468]], ![![-1563266, -774072, -495112, -263260, -370365]]]
  g := ![![![-79, -78, 58, 2, 148], ![484, -369, 72, -540, 8], ![778, 1428, -901, 384, -2160], ![-1514, 894, -94, 1529, 252], ![-642, -1444, 876, -480, 2067]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N1 : Nat.card (O ⧸ I523N1) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N1)

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := prime_ideal_of_norm_prime hp523.out _ NI523N1

def I523N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65434, -17945, -66, -7467, -4027]] i)))

def SI523N2: IdealEqSpanCertificate' Table ![![65434, -17945, -66, -7467, -4027]] 
 ![![523, 0, 0, 0, 0], ![434, 1, 0, 0, 0], ![447, 0, 1, 0, 0], ![399, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![65434, -17945, -66, -7467, -4027], ![-48324, 69850, -29439, 23766, -29868], ![-358416, -23271, 63748, 2574, 95064], ![214290, -109890, 27114, -43199, 16650], ![151635, 38976, -42687, 9111, -59498]]]
  hmulB := by decide  
  f := ![![![11063345093913160, 5478116837761631, 3504042061545468, 1863101534074749, 2621204253548863]], ![![9240814955642252, 4575674316712286, 2926800530279385, 1556181821484552, 2189397805308806]], ![![9626661817619064, 4766729930855208, 3049008020166502, 1621159626512295, 2280815313055947]], ![![8491249869472074, 4204520286471807, 2689394251481184, 1429952742478342, 2011805659759449]], ![![570735028918951, 282604686492284, 180766262857485, 96113544222183, 135222491276600]]]
  g := ![![![20985, -17945, -66, -7467, -4027], ![-49427, 69850, -29439, 23766, -29868], ![-42912, -23271, 63748, 2574, 95064], ![100491, -109890, 27114, -43199, 16650], ![665, 38976, -42687, 9111, -59498]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N2 : Nat.card (O ⧸ I523N2) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N2)

lemma isPrimeI523N2 : Ideal.IsPrime I523N2 := prime_ideal_of_norm_prime hp523.out _ NI523N2

def I523N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-188971, -93572, -59852, -31824, -44772]] i)))

def SI523N3: IdealEqSpanCertificate' Table ![![-188971, -93572, -59852, -31824, -44772]] 
 ![![523, 0, 0, 0, 0], ![440, 1, 0, 0, 0], ![433, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![240, 0, 0, 0, 1]] where
  M :=![![![-188971, -93572, -59852, -31824, -44772], ![-537264, -266035, -170168, -90480, -127296], ![-1527552, -756360, -483811, -257232, -361920], ![-455208, -225392, -144168, -76651, -107840], ![192684, 95388, 61024, 32436, 45653]]]
  hmulB := by decide  
  f := ![![![-31153, 52028, -22364, 16704, -23316]], ![![-26744, 43749, -18728, 14064, -19488]], ![![-24259, 42428, -18399, 13584, -19260]], ![![-5840, 10608, -4632, 3389, -4864]], ![![-15228, 24180, -10288, 7788, -10675]]]
  g := ![![![154787, -93572, -59852, -31824, -44772], ![440080, -266035, -170168, -90480, -127296], ![1251193, -756360, -483811, -257232, -361920], ![372840, -225392, -144168, -76651, -107840], ![-157804, 95388, 61024, 32436, 45653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N3 : Nat.card (O ⧸ I523N3) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N3)

lemma isPrimeI523N3 : Ideal.IsPrime I523N3 := prime_ideal_of_norm_prime hp523.out _ NI523N3
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![7229726, -11440634, 6497443, -4998821, 14892097]] ![![-101, -78, 58, 2, 148]]
  ![![9897769922, -13037110120, 7256768463, -6103983945, 16466259103]] where
 M := ![![![9897769922, -13037110120, 7256768463, -6103983945, 16466259103]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI523N1 : IdealMulLeCertificate' Table 
  ![![9897769922, -13037110120, 7256768463, -6103983945, 16466259103]] ![![65434, -17945, -66, -7467, -4027]]
  ![![-134447459410225, 55425828479815, -22647915027339, 48642404031756, -41949294039646]] where
 M := ![![![-134447459410225, 55425828479815, -22647915027339, 48642404031756, -41949294039646]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI523N2 : IdealMulLeCertificate' Table 
  ![![-134447459410225, 55425828479815, -22647915027339, 48642404031756, -41949294039646]] ![![-188971, -93572, -59852, -31824, -44772]]
  ![![523, 0, 0, 0, 0]] where
 M := ![![![-1132791550688669, 216413004815215, -34446766019803, 339252821718036, 20825666068462]]]
 hmul := by decide  
 g := ![![![![-2165949427703, 413791596205, -65863797361, 648666963132, 39819629194]]]]
 hle2 := by decide  


def PBC523 : ContainsPrimesAboveP 523 ![I523N0, I523N1, I523N2, I523N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
    exact isPrimeI523N1
    exact isPrimeI523N2
    exact isPrimeI523N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 523 (by decide) (𝕀 ⊙ MulI523N0 ⊙ MulI523N1 ⊙ MulI523N2)


lemma PB752I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB752I10 : PrimesBelowBoundCertificateInterval O 463 523 752 where
  m := 9
  g := ![4, 3, 2, 3, 3, 2, 3, 3, 4]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB752I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2, I467N3]
    · exact ![I479N0, I479N1, I479N2]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1]
    · exact ![I509N0, I509N1, I509N2]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1, I523N2, I523N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![218089, 467, 467, 467]
    · exact ![109902239, 479, 479]
    · exact ![115501303, 237169]
    · exact ![241081, 241081, 491]
    · exact ![249001, 249001, 499]
    · exact ![127263527, 253009]
    · exact ![259081, 259081, 509]
    · exact ![141420761, 521, 521]
    · exact ![273529, 523, 523, 523]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
      exact NI467N3
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
      exact NI479N2
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
      exact NI491N2
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
      exact NI499N2
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
      exact NI509N2
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
      exact NI521N2
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
      exact NI523N2
      exact NI523N3
  β := ![I467N1, I467N2, I467N3, I479N1, I479N2, I491N2, I499N2, I509N2, I521N1, I521N2, I523N1, I523N2, I523N3]
  Il := ![[I467N1, I467N2, I467N3], [I479N1, I479N2], [], [I491N2], [I499N2], [], [I509N2], [I521N1, I521N2], [I523N1, I523N2, I523N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
