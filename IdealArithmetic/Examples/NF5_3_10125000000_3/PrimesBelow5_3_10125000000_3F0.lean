
import IdealArithmetic.Examples.NF5_3_10125000000_3.RI5_3_10125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -1, -4, -1, 4]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![7, -1, -4, -1, 4]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![7, -1, -4, -1, 4], ![-20, 20, 39, 4, -76], ![80, 71, 160, 30, -416], ![310, 151, 156, -22, -598], ![60, 71, 137, 18, -355]]]
  hmulB := by decide  
  f := ![![![-284, 450, 349, 65, -618]], ![![650, -162, -180, -41, 322]], ![![-820, 851, 688, 132, -1220]], ![![853, -190, -220, -51, 394]], ![![-160, 313, 239, 44, -423]]]
  g := ![![![4, -1, -4, -1, 4], ![-12, 20, 39, 4, -76], ![25, 71, 160, 30, -416], ![166, 151, 156, -22, -598], ![21, 71, 137, 18, -355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1235082, -736232, -647469, -131107, 1151117]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1235082, -736232, -647469, -131107, 1151117]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1235082, -736232, -647469, -131107, 1151117], ![-2622140, 1563054, 1374603, 278346, -2443864], ![5566920, -3318459, -2918386, -590946, 5188536], ![-4598390, 2741029, 2410509, 488117, -4285504], ![1599530, -953500, -838557, -169798, 1490868]]]
  hmulB := by decide  
  f := ![![![-1364, 465, 942, 80, -1233]], ![![800, 22, 915, 462, -2438]], ![![9240, -4959, -15508, -3714, 28032]], ![![-37540, 15248, 38403, 6545, -60857]], ![![2165, -1288, -4269, -1091, 7938]]]
  g := ![![![617541, -736232, -647469, -131107, 1151117], ![-1311070, 1563054, 1374603, 278346, -2443864], ![2783460, -3318459, -2918386, -590946, 5188536], ![-2299195, 2741029, 2410509, 488117, -4285504], ![799765, -953500, -838557, -169798, 1490868]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 83, 140, 60, -352]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![227, 83, 140, 60, -352]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![227, 83, 140, 60, -352], ![1200, -429, -1757, -440, 3216], ![-8800, 4011, 9891, 1766, -15968], ![17060, -5347, -10176, -485, 12076], ![-2480, 1282, 3129, 592, -5169]]]
  hmulB := by decide  
  f := ![![![-21175554, -36667389, -67083779, -7153258, 169151192]], ![![-82120357, -142198828, -260155824, -27740860, 655980752]], ![![-493872397, -855184746, -1564578943, -166833726, 3945072824]], ![![-1607392457, -2783345480, -5092190608, -542988985, 12839916372]], ![![-498680837, -863510993, -1579811992, -168458052, 3983482831]]]
  g := ![![![148, 83, 140, 60, -352], ![305, -429, -1757, -440, 3216], ![-4250, 4011, 9891, 1766, -15968], ![10496, -5347, -10176, -485, 12076], ![-1157, 1282, 3129, 592, -5169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![7, -1, -4, -1, 4]] ![![1235082, -736232, -647469, -131107, 1151117]]
  ![![-3456, 2129, 1921, 380, -3485]] where
 M := ![![![-3456, 2129, 1921, 380, -3485]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-3456, 2129, 1921, 380, -3485]] ![![1235082, -736232, -647469, -131107, 1151117]]
  ![![-6478676382, 3861938539, 3396327710, 687727650, -6038235652]] where
 M := ![![![-6478676382, 3861938539, 3396327710, 687727650, -6038235652]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-6478676382, 3861938539, 3396327710, 687727650, -6038235652]] ![![227, 83, 140, 60, -352]]
  ![![-16559013954, 9870821459, 8680751599, 1757779546, -15433258804]] where
 M := ![![![-16559013954, 9870821459, 8680751599, 1757779546, -15433258804]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-16559013954, 9870821459, 8680751599, 1757779546, -15433258804]] ![![227, 83, 140, 60, -352]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-42323599278, 25229080306, 22187350874, 4492752856, -39446253508]]]
 hmul := by decide  
 g := ![![![![-21161799639, 12614540153, 11093675437, 2246376428, -19723126754]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 24, 13, 2, -21]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![27, 24, 13, 2, -21]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![27, 24, 13, 2, -21], ![40, 32, 9, 2, -4], ![40, 7, -68, -6, 200], ![-80, -155, -321, -33, 830], ![10, -19, -83, -8, 227]]]
  hmulB := by decide  
  f := ![![![-2261, 1348, 1185, 240, -2107]], ![![1600, -954, -839, -170, 1492]], ![![-3400, 2027, 1786, 362, -3176]], ![![2820, -1679, -1487, -301, 2642]], ![![-2484, 1481, 1303, 264, -2317]]]
  g := ![![![23, 24, 13, 2, -21], ![16, 32, 9, 2, -4], ![-120, 7, -68, -6, 200], ![-580, -155, -321, -33, 830], ![-148, -19, -83, -8, 227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1870276513, -1113385319, -979398084, -198349918, 1741256803]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![1870276513, -1113385319, -979398084, -198349918, 1741256803]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1870276513, -1113385319, -979398084, -198349918, 1741256803], ![-3966998360, 2367112773, 2081325746, 421402848, -3700308196], ![8428056960, -5020127422, -4415517127, -894182684, 7850254800], ![-6958327660, 4149742280, 3649116936, 738877553, -6487643510], ![2422423770, -1441702216, -1268267842, -256860142, 2254837253]]]
  hmulB := by decide  
  f := ![![![-8274599, 4839387, 15877192, 4016212, -29389627]], ![![24016547, -9728022, -24436002, -4141316, 38648379]], ![![-115117466, 40384096, 85822237, 8981316, -117780642]], ![![49651040, 7878304, 89796772, 40154421, -222509642]], ![![-35908310, 12813106, 27854122, 3177806, -39074861]]]
  g := ![![![1647486000, -1113385319, -979398084, -198349918, 1741256803], ![-3498920875, 2367112773, 2081325746, 421402848, -3700308196], ![7426406212, -5020127422, -4415517127, -894182684, 7850254800], ![-6135434604, 4149742280, 3649116936, 738877553, -6487643510], ![2133553890, -1441702216, -1268267842, -256860142, 2254837253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![188517, -71699, -168447, -24396, 253018]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![188517, -71699, -168447, -24396, 253018]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![188517, -71699, -168447, -24396, 253018], ![-487920, 123934, 126971, -44142, 11112], ![-882840, 720377, 2716894, 783646, -5340264], ![8080420, -3600251, -9862017, -1962911, 16538912], ![-90580, 151333, 666875, 215154, -1384399]]]
  hmulB := by decide  
  f := ![![![-654841, 340747, 264605, 60052, -420230]], ![![-36214, -123194, -210671, -23770, 521076]], ![![-1712654, 233095, -351822, 31542, 1422820]], ![![-285100, -2323795, -3806151, -445367, 9290680]], ![![-819247, -290440, -805858, -61574, 2220903]]]
  g := ![![![138597, -71699, -168447, -24396, 253018], ![-333614, 123934, 126971, -44142, 11112], ![-805706, 720377, 2716894, 783646, -5340264], ![6155348, -3600251, -9862017, -1962911, 16538912], ![-114199, 151333, 666875, 215154, -1384399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![27, 24, 13, 2, -21]] ![![27, 24, 13, 2, -21]]
  ![![1839, 1596, 784, 126, -1170]] where
 M := ![![![1839, 1596, 784, 126, -1170]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1839, 1596, 784, 126, -1170]] ![![27, 24, 13, 2, -21]]
  ![![123073, 103396, 41623, 7368, -49213]] where
 M := ![![![123073, 103396, 41623, 7368, -49213]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![123073, 103396, 41623, 7368, -49213]] ![![1870276513, -1113385319, -979398084, -198349918, 1741256803]]
  ![![326094508079, 295349500963, 178185956957, 26191536412, -312475291166]] where
 M := ![![![326094508079, 295349500963, 178185956957, 26191536412, -312475291166]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![326094508079, 295349500963, 178185956957, 26191536412, -312475291166]] ![![188517, -71699, -168447, -24396, 253018]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![366157813323, 331635541320, 200077532064, 29409376296, -350865400392]]]
 hmul := by decide  
 g := ![![![![122052604441, 110545180440, 66692510688, 9803125432, -116955133464]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4983785, -2970809, -2612639, -529038, 4644936]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![4983785, -2970809, -2612639, -529038, 4644936]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![4983785, -2970809, -2612639, -529038, 4644936], ![-10580760, 6307224, 5546791, 1123178, -9861480], ![22463560, -13390459, -11776056, -2384554, 20936312], ![-18555160, 11060753, 9727215, 1969679, -17293736], ![6454440, -3847453, -3383593, -685150, 6015593]]]
  hmulB := by decide  
  f := ![![![-2435, 995, 2519, 434, -4008]], ![![1736, -550, -1001, -34, 1144]], ![![-680, -703, -4230, -1594, 9512]], ![![-16808, 8233, 24189, 5351, -42328]], ![![-664, -23, -805, -402, 2121]]]
  g := ![![![996757, -2970809, -2612639, -529038, 4644936], ![-2116152, 6307224, 5546791, 1123178, -9861480], ![4492712, -13390459, -11776056, -2384554, 20936312], ![-3711032, 11060753, 9727215, 1969679, -17293736], ![1290888, -3847453, -3383593, -685150, 6015593]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![4983785, -2970809, -2612639, -529038, 4644936]] ![![4983785, -2970809, -2612639, -529038, 4644936]]
  ![![37379202478145, -22281727338602, -19595343814968, -3967893121028, 34837998645728]] where
 M := ![![![37379202478145, -22281727338602, -19595343814968, -3967893121028, 34837998645728]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![37379202478145, -22281727338602, -19595343814968, -3967893121028, 34837998645728]] ![![4983785, -2970809, -2612639, -529038, 4644936]]
  ![![280351000172072347065, -167117116766741484709, -146968738582148112353, -29759939520845836606, 261291496798186573976]] where
 M := ![![![280351000172072347065, -167117116766741484709, -146968738582148112353, -29759939520845836606, 261291496798186573976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![280351000172072347065, -167117116766741484709, -146968738582148112353, -29759939520845836606, 261291496798186573976]] ![![4983785, -2970809, -2612639, -529038, 4644936]]
  ![![2102684864522745347330423585, -1253409589451903419454830820, -1102292989805667859031461644, -223205104890610005515188984, 1959735029334028307748667808]] where
 M := ![![![2102684864522745347330423585, -1253409589451903419454830820, -1102292989805667859031461644, -223205104890610005515188984, 1959735029334028307748667808]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![2102684864522745347330423585, -1253409589451903419454830820, -1102292989805667859031461644, -223205104890610005515188984, 1959735029334028307748667808]] ![![4983785, -2970809, -2612639, -529038, 4644936]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![15770529217942380574451795800924745, -9400806029479355746511035674157325, -8267403306966307724748360129467075, -1674079976349770936099674285727750, 14698378754227791214711268749746600]]]
 hmul := by decide  
 g := ![![![![3154105843588476114890359160184949, -1880161205895871149302207134831465, -1653480661393261544949672025893415, -334815995269954187219934857145550, 2939675750845558242942253749949320]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104771419, 181421185, 331913974, 35392554, -836918333]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![104771419, 181421185, 331913974, 35392554, -836918333]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 5, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 1, 0, 0, 1]] where
  M :=![![![104771419, 181421185, 331913974, 35392554, -836918333], ![707851080, 1225708209, 2242459610, 239117300, -5654343300], ![4782346000, 8281064790, 15150386709, 1615511620, -38201574400], ![15801190660, 27361191400, 50057889990, 5337758339, -126220554310], ![4829927930, 8363457230, 15301125450, 1631585150, -38581660881]]]
  hmulB := by decide  
  f := ![![![19503, -8385, -22178, -4168, 36401]], ![![-83360, 28723, 59690, 5660, -80020]], ![![-35013, 16190, 45877, 9608, -78471]], ![![87827, -46165, -142392, -33553, 255619]], ![![-1581, 1554, 6246, 1886, -12548]]]
  g := ![![![-22889976, -91604336, 331913974, 35392554, -836918333], ![-154648050, -618892363, 2242459610, 239117300, -5654343300], ![-1044824941, -4181327765, 15150386709, 1615511620, -38201574400], ![-3452171431, -13815386320, 50057889990, 5337758339, -126220554310], ![-1055220427, -4222929877, 15301125450, 1631585150, -38581660881]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[5, 2], [1, 1]], ![[0, 5], [2, 6]]]
 h' := ![![[1, 6], [3, 4], [0, 1]], ![[0, 1], [0, 3], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-700301, -585288, -910121, -48069, 2612742]
  a := ![-145, 179, 431, 83, -899]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62639, 193225, -910121, -48069, 2612742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -71, -188, -20, 491]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![29, -71, -188, -20, 491]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 5, 1, 0, 0], ![5, 1, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![29, -71, -188, -20, 491], ![-400, -641, -1326, -136, 3412], ![-2720, -5150, -9541, -1020, 24080], ![-10000, -17140, -31512, -3353, 79534], ![-2910, -5210, -9626, -1026, 24301]]]
  hmulB := by decide  
  f := ![![![-1367, 447, 856, 50, -1047]], ![![1000, 333, 2682, 1112, -6364]], ![![2915, -1070, -2411, -310, 3495]], ![![-12305, 4924, 12218, 2017, -19151]], ![![-195, -115, -774, -304, 1782]]]
  g := ![![![-198, 127, -188, -20, 491], ![-1450, 875, -1326, -136, 3412], ![-10045, 6225, -9541, -1020, 24080], ![-33335, 20539, -31512, -3353, 79534], ![-10165, 6278, -9626, -1026, 24301]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142806302, -120320532, -188002294, -10276067, 538237688]
  a := ![-2062, 2532, 6127, 1177, -12785]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-263228991, 118566715, -188002294, -10276067, 538237688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70934557, 22731603, 42090923, 1787298, -49316154]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-70934557, 22731603, 42090923, 1787298, -49316154]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-70934557, 22731603, 42090923, 1787298, -49316154], ![35745960, 25106224, 162074493, 62734270, -370168896], ![1254685400, -630198505, -1888105496, -428662254, 3337022728], ![-4304495520, 1691992287, 4121174301, 652500893, -6369838932], ![314431740, -170089879, -534121459, -128586902, 967640651]]]
  hmulB := by decide  
  f := ![![![6145806309, -3316587239, -2974497913, -609316698, 5291332070]], ![![1770984468, -777826750, -730319623, -153494606, 1300863224]], ![![8283588935, -4562151170, -4074681757, -832675644, 7247570858]], ![![-1348097226, 965634053, 822229633, 163222529, -1460390312]], ![![6413312422, -3448765851, -3095283673, -634325726, 5506314055]]]
  g := ![![![-11427608, 22731603, 42090923, 1787298, -49316154], ![174356205, 25106224, 162074493, 62734270, -370168896], ![-849829280, -630198505, -1888105496, -428662254, 3337022728], ![747956519, 1691992287, 4121174301, 652500893, -6369838932], ![-269038793, -170089879, -534121459, -128586902, 967640651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![104771419, 181421185, 331913974, 35392554, -836918333]] ![![29, -71, -188, -20, 491]]
  ![![1109170696901, 1920629422936, 3513832967794, 374686013076, -8860100676528]] where
 M := ![![![1109170696901, 1920629422936, 3513832967794, 374686013076, -8860100676528]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![1109170696901, 1920629422936, 3513832967794, 374686013076, -8860100676528]] ![![-70934557, 22731603, 42090923, 1787298, -49316154]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-3753337979937, -6499244327079, -11890507720525, -1267905154334, 29981816570062]]]
 hmul := by decide  
 g := ![![![![-536191139991, -928463475297, -1698643960075, -181129307762, 4283116652866]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10289, 6133, 5393, 1092, -9588]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-10289, 6133, 5393, 1092, -9588]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![1, 8, 9, 1, 0], ![1, 1, 5, 0, 1]] where
  M :=![![![-10289, 6133, 5393, 1092, -9588], ![21840, -13020, -11447, -2318, 20352], ![-46360, 27639, 24300, 4922, -43208], ![38300, -22837, -20097, -4073, 35740], ![-13320, 7941, 6981, 1414, -12413]]]
  hmulB := by decide  
  f := ![![![-19, -25, -35, -4, 84]], ![![-80, -122, -205, -22, 512]], ![![-440, -759, -1362, -146, 3416]], ![![-549, -933, -1670, -179, 4192]], ![![-249, -427, -765, -82, 1919]]]
  g := ![![![-163, 635, 3955, 1092, -9588], ![346, -1348, -8395, -2318, 20352], ![-734, 2861, 17822, 4922, -43208], ![603, -2363, -14740, -4073, 35740], ![-211, 822, 5120, 1414, -12413]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 8, 4], [9, 2, 7], [0, 1]]
 g := ![![[7, 4, 5], [1, 10, 1], []], ![[8, 3, 0, 9], [0, 8, 10, 5], [4, 5]], ![[1, 7], [0, 6, 8, 8], [1, 5]]]
 h' := ![![[1, 8, 4], [8, 3, 7], [0, 0, 1], [0, 1]], ![[9, 2, 7], [0, 9, 4], [0, 1, 2], [1, 8, 4]], ![[0, 1], [9, 10], [1, 10, 8], [9, 2, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3], []]
 b := ![[], [4, 7, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 0, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1299676055, 2708125494, 5044621924, 563498526, -12501152676]
  a := ![-109, 134, 324, 62, -676]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1203393655, 972844542, 5679899870, 563498526, -12501152676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 25, 35, 4, -84]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![19, 25, 35, 4, -84]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 4, 1, 0, 0], ![4, 8, 0, 1, 0], ![10, 10, 0, 0, 1]] where
  M :=![![![19, 25, 35, 4, -84], ![80, 122, 205, 22, -512], ![440, 759, 1362, 146, -3416], ![1420, 2431, 4437, 475, -11188], ![440, 755, 1365, 146, -3433]]]
  hmulB := by decide  
  f := ![![![10289, -6133, -5393, -1092, 9588]], ![![-21840, 13020, 11447, 2318, -20352]], ![![4691, -2796, -2459, -498, 4372]], ![![-15624, 9315, 8191, 1659, -14564]], ![![-9290, 5539, 4869, 986, -8657]]]
  g := ![![![48, 63, 35, 4, -84], ![297, 386, 205, 22, -512], ![1978, 2573, 1362, 146, -3416], ![6497, 8433, 4437, 475, -11188], ![1991, 2587, 1365, 146, -3433]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[2, 5], [1, 4], [1]], ![[1, 6], [9, 7], [1]]]
 h' := ![![[2, 10], [1, 7], [1, 2], [0, 1]], ![[0, 1], [4, 4], [5, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [3, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [10, 9, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1143228, -837773, -1113948, 17082, 3445601]
  a := ![-206, 259, 613, 127, -1277]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2331094, -2815877, -1113948, 17082, 3445601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-10289, 6133, 5393, 1092, -9588]] ![![19, 25, 35, 4, -84]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-329479, 2698, -320274, -170772, 882554]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-329479, 2698, -320274, -170772, 882554]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![11, 2, 2, 10, 1]] where
  M :=![![![-329479, 2698, -320274, -170772, 882554], ![-3415440, 1854439, 5836248, 1408716, -10585080], ![28174320, -11626932, -29743121, -5232096, 47659824], ![-50613240, 16029756, 29081730, 945097, -33138468], ![8251660, -3530918, -9340956, -1751040, 15315969]]]
  hmulB := by decide  
  f := ![![![813, -1546, 1206, -36, -4946]], ![![-720, 12811, 25344, 2844, -63816]], ![![56880, 81156, 161251, 16560, -413136]], ![![165960, 308796, 563946, 60469, -1420188]], ![![141071, 257498, 476456, 50830, -1202813]]]
  g := ![![![-772121, -135570, -160414, -692024, 882554], ![8693880, 1771123, 2077416, 8250732, -10585080], ![-38160288, -8226660, -9620213, -37063872, 47659824], ![24146916, 6331284, 7335282, 25563829, -33138468], ![-12324923, -2627912, -3074838, -11916210, 15315969]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [10, 10, 9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 9, 3], [11, 12], [12, 7, 4, 10], [0, 1]]
 g := ![![[4, 7, 12, 4], [7, 9, 1], []], ![[11, 0, 10, 5, 4, 4], [4, 9, 1], [1, 0, 4, 4, 5, 1]], ![[6, 6, 1, 9], [6, 8, 1], []], ![[12, 9, 3, 10, 3, 9], [3, 8, 1], [7, 9, 7, 9, 8, 12]]]
 h' := ![![[12, 6, 9, 3], [8, 9, 6, 11], [0, 0, 0, 1], [0, 1]], ![[11, 12], [3, 6, 6, 6], [2, 8, 0, 12], [12, 6, 9, 3]], ![[12, 7, 4, 10], [4, 0, 5, 2], [5, 1, 7, 12], [11, 12]], ![[0, 1], [6, 11, 9, 7], [7, 4, 6, 1], [12, 7, 4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11], []]
 b := ![[], [], [9, 7, 10, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [10, 10, 9, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1203675075670, -4765851277640, -7773018257184, -411326938584, 18987435094928]
  a := ![140, -184, -416, -102, 868]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16158881624606, -3287747805192, -3519068342080, -14637359837528, 18987435094928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![813, -1546, 1206, -36, -4946]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![813, -1546, 1206, -36, -4946]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![813, -1546, 1206, -36, -4946], ![-720, 12811, 25344, 2844, -63816], ![56880, 81156, 161251, 16560, -413136], ![165960, 308796, 563946, 60469, -1420188], ![53060, 88586, 168012, 17688, -426379]]]
  hmulB := by decide  
  f := ![![![-329479, 2698, -320274, -170772, 882554]], ![![-490827, 144517, 227214, -9864, -203238]], ![![1913810, -892304, -2534297, -533832, 4345028]], ![![-4121427, 1234926, 2015328, -45527, -1938114]], ![![584054, -271194, -767808, -160968, 1313929]]]
  g := ![![![991, -1546, 1206, -36, -4946], ![-20571, 12811, 25344, 2844, -63816], ![-123754, 81156, 161251, 16560, -413136], ![-458193, 308796, 563946, 60469, -1420188], ![-133136, 88586, 168012, 17688, -426379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-329479, 2698, -320274, -170772, 882554]] ![![813, -1546, 1206, -36, -4946]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301369, 179734, 158050, 32002, -280992]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-301369, 179734, 158050, 32002, -280992]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![7, 10, 1, 8, 1]] where
  M :=![![![-301369, 179734, 158050, 32002, -280992], ![640040, -381385, -335426, -67924, 596344], ![-1358480, 810026, 712335, 144236, -1266448], ![1122340, -668882, -588234, -119119, 1045772], ![-390280, 232792, 204710, 41448, -363957]]]
  hmulB := by decide  
  f := ![![![-353, 146, 374, 66, -600]], ![![1320, -429, -814, -44, 984]], ![![-880, -362, -2709, -1100, 6352]], ![![-11660, 5818, 17346, 3913, -30580]], ![![-4943, 2526, 7651, 1762, -13605]]]
  g := ![![![97975, 175862, 25826, 134114, -280992], ![-207904, -373225, -54810, -284628, 596344], ![441568, 792618, 116399, 604460, -1266448], ![-364592, -654506, -96118, -499135, 1045772], ![126907, 227786, 33451, 173712, -363957]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [5, 4, 14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16, 1, 2], [11, 16], [6, 1, 16, 15], [0, 1]]
 g := ![![[16, 4], [3, 2, 8], [1], []], ![[0, 1, 6, 16, 3, 9], [7, 2, 13], [8, 4, 8], [10, 7, 4]], ![[9, 13], [7, 9, 8], [1], []], ![[1, 7, 0, 12, 5, 8], [4, 1, 13], [0, 7, 8], [10, 7, 4]]]
 h' := ![![[5, 16, 1, 2], [10, 1, 15], [12, 13, 3, 5], [0, 0, 1], [0, 1]], ![[11, 16], [14, 16, 15, 9], [7, 16, 12, 8], [9, 0, 10, 5], [5, 16, 1, 2]], ![[6, 1, 16, 15], [0, 9, 15], [16, 10, 15, 12], [2, 12, 1], [11, 16]], ![[0, 1], [10, 8, 6, 8], [9, 12, 4, 9], [3, 5, 5, 12], [6, 1, 16, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10], []]
 b := ![[], [], [11, 3, 11, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [5, 4, 14, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-869274894572402, -1486870644335004, -2719446968686365, -290030512424387, 6864570039233018]
  a := ![303, -365, -900, -159, 1876]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2877721480541384, -4125445355097952, -563765706348199, -3247446519193443, 6864570039233018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, -146, -374, -66, 600]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![353, -146, -374, -66, 600]] 
 ![![17, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![353, -146, -374, -66, 600], ![-1320, 429, 814, 44, -984], ![880, 362, 2709, 1100, -6352], ![11660, -5818, -17346, -3913, 30580], ![600, -28, 470, 272, -1363]]]
  hmulB := by decide  
  f := ![![![301369, -179734, -158050, -32002, 280992]], ![![245992, -146727, -129022, -26124, 229384]], ![![363552, -216810, -190655, -38604, 338960]], ![![-66020, 39346, 34602, 7007, -61516]], ![![93868, -55984, -49230, -9968, 87525]]]
  g := ![![![369, -146, -374, -66, 600], ![-1016, 429, 814, 44, -984], ![-1344, 362, 2709, 1100, -6352], ![15292, -5818, -17346, -3913, 30580], ![-60, -28, 470, 272, -1363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-301369, 179734, 158050, 32002, -280992]] ![![353, -146, -374, -66, 600]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![309, 451, 290, 46, -509]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![309, 451, 290, 46, -509]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![6, 13, 6, 2, 1]] where
  M :=![![![309, 451, 290, 46, -509], ![920, 467, 236, 28, -404], ![560, 1264, 807, 136, -1376], ![900, 126, -126, -23, 378], ![490, 650, 376, 62, -615]]]
  hmulB := by decide  
  f := ![![![21, -11, -34, -8, 61]], ![![-160, 65, 164, 28, -260]], ![![560, -176, -315, -8, 352]], ![![0, -162, -810, -281, 1746]], ![![84, -35, -90, -16, 145]]]
  g := ![![![177, 372, 176, 56, -509], ![176, 301, 140, 44, -404], ![464, 1008, 477, 152, -1376], ![-72, -252, -126, -41, 378], ![220, 455, 214, 68, -615]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [17, 2, 9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18, 10], [8, 1, 13, 8], [8, 18, 15, 11], [0, 1]]
 g := ![![[7, 17, 0, 17], [3, 11, 12, 7], [1], []], ![[4, 14, 3, 13, 18], [15, 15, 15, 6, 8], [12, 13, 9], [5]], ![[7, 17, 10, 13, 14, 13], [16, 0, 1, 4, 14, 18], [1], [8, 0, 7]], ![[2, 12, 9, 6, 11, 6], [13, 8, 4, 15, 3, 11], [12, 13, 9], [0, 8, 7]]]
 h' := ![![[14, 18, 10], [6, 1, 5, 6], [2, 17, 10, 11], [0, 0, 1], [0, 1]], ![[8, 1, 13, 8], [0, 18, 9, 13], [14, 2, 7, 15], [16, 0, 8, 16], [14, 18, 10]], ![[8, 18, 15, 11], [2, 1, 8, 2], [18, 17, 2, 11], [4, 0, 18], [8, 1, 13, 8]], ![[0, 1], [3, 18, 16, 17], [16, 2, 0, 1], [7, 0, 11, 3], [8, 18, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 10, 18], []]
 b := ![[], [], [5, 0, 4, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [17, 2, 9, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2744887771223, -4700425383506, -8597858181308, -917206575572, 21700634956696]
  a := ![-71, 85, 211, 37, -440]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6997299869021, -15095193674766, -7305350943236, -2332551394156, 21700634956696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -11, -34, -8, 61]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![21, -11, -34, -8, 61]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![21, -11, -34, -8, 61], ![-160, 65, 164, 28, -260], ![560, -176, -315, -8, 352], ![0, -162, -810, -281, 1746], ![190, -64, -128, -10, 165]]]
  hmulB := by decide  
  f := ![![![309, 451, 290, 46, -509]], ![![146, 167, 104, 16, -182]], ![![62, 114, 73, 12, -126]], ![![210, 244, 146, 23, -248]], ![![286, 414, 264, 42, -461]]]
  g := ![![![-39, -11, -34, -8, 61], ![158, 65, 164, 28, -260], ![-174, -176, -315, -8, 352], ![-1186, -162, -810, -281, 1746], ![-90, -64, -128, -10, 165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![309, 451, 290, 46, -509]] ![![21, -11, -34, -8, 61]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [6, 8, 7, 5, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 1, 3, 16, 22], [7, 3, 2, 2, 21], [21, 20, 18, 12, 13], [5, 21, 0, 16, 13], [0, 1]]
 g := ![![[4, 19, 10, 13, 8], [12, 14, 1, 18, 12], [1], []], ![[6, 8, 22, 0, 10, 22, 1, 20], [3, 17, 9, 8, 17, 5, 13, 20], [20, 16, 6, 18, 18, 13, 1, 14], [15, 15, 0, 1]], ![[13, 21, 12, 0, 21, 5, 3, 15], [13, 21, 3, 17, 17, 13, 8, 7], [9, 21, 13, 14, 17, 22, 7, 10], [17, 21, 5, 4]], ![[22, 16, 19, 6, 3, 13, 3, 9], [11, 0, 8, 10, 19, 4, 16, 3], [13, 2, 18, 11, 2, 18, 22, 8], [15, 3, 16, 8]], ![[20, 16, 7, 8, 17, 7, 20, 4], [7, 3, 22, 20, 13, 11, 1, 9], [15, 15, 13, 8, 0, 9, 21, 13], [8, 8, 5, 8]]]
 h' := ![![[22, 1, 3, 16, 22], [20, 17, 9, 12, 10], [17, 15, 16, 18, 9], [0, 0, 1], [0, 1]], ![[7, 3, 2, 2, 21], [16, 20, 1, 8, 7], [9, 13, 13, 17, 7], [3, 18, 0, 18, 3], [22, 1, 3, 16, 22]], ![[21, 20, 18, 12, 13], [1, 16, 0, 6, 2], [13, 4, 1, 8, 13], [16, 10, 19, 20, 15], [7, 3, 2, 2, 21]], ![[5, 21, 0, 16, 13], [14, 20, 10, 15, 12], [11, 17, 1, 13, 5], [6, 12, 11, 9, 6], [21, 20, 18, 12, 13]], ![[0, 1], [1, 19, 3, 5, 15], [2, 20, 15, 13, 12], [0, 6, 15, 22, 22], [5, 21, 0, 16, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 3, 22, 20], [], [], []]
 b := ![[], [12, 20, 4, 1, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [6, 8, 7, 5, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9399704909879613090, -16431045764531166928, -30088958674430788564, -3216146280459441143, 75796223642647500768]
  a := ![318, -395, -944, -187, 1971]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-408682822168678830, -714393294110050736, -1308215594540469068, -139832446976497441, 3295487984462934816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB4920I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB4920I0 : PrimesBelowBoundCertificateInterval O 1 23 4920 where
  m := 9
  g := ![5, 5, 5, 3, 2, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB4920I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![1331, 121]
    · exact ![28561, 13]
    · exact ![83521, 17]
    · exact ![130321, 19]
    · exact ![6436343]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N1, I17N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N1], [I17N1], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
