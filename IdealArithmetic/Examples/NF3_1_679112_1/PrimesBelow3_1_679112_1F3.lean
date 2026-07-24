
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-485205415, -130527885, -6637981]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-485205415, -130527885, -6637981]] 
 ![![139, 0, 0], ![62, 1, 0], ![48, 0, 1]] where
  M :=![![![-485205415, -130527885, -6637981], ![1048800998, -471929453, -137165866], ![21672206828, 1323132730, -609095319]]]
  hmulB := by decide  
  f := ![![![-468938667463924687, 88286853674688445, -14771311640819017]], ![![-192376475852618172, 36218625062218683, -6059753810769134]], ![![-245500084026041400, 46220180802638210, -7733118423796619]]]
  g := ![![![57022637, -130527885, -6637981], ![265412868, -471929453, -137165866], ![-223924080, 1323132730, -609095319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617556204550409198134073, -116267004727718069657485, 19452682804915487175133]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![617556204550409198134073, -116267004727718069657485, 19452682804915487175133]] 
 ![![139, 0, 0], ![87, 1, 0], ![76, 0, 1]] where
  M :=![![![617556204550409198134073, -116267004727718069657485, 19452682804915487175133], ![-3073523883176646973671014, 578650838940578223783807, -96814321922802582482352], ![15296662863802808032211616, -2879895239331041808706310, 481836517017775641301455]]]
  hmulB := by decide  
  f := ![![![-2909491501935, -1695650048555, -223241266611]], ![![-1567292378013, -1079025634482, -153531521657]], ![![590384702512, -645751805290, -153584435585]]]
  g := ![![![66578285774736001676440, -116267004727718069657485, 19452682804915487175133], ![-331354377013481699094989, 578650838940578223783807, -96814321922802582482352], ![1649122110735629472307554, -2879895239331041808706310, 481836517017775641301455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7661, 1390, -30]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![7661, 1390, -30]] 
 ![![139, 0, 0], ![128, 1, 0], ![18, 0, 1]] where
  M :=![![![7661, 1390, -30], ![4740, 7721, 1360], ![-214880, 2020, 9081]]]
  hmulB := by decide  
  f := ![![![-67367201, 12683190, -2122030]], ![![-59623892, 11225361, -1878120]], ![![-20728582, 3902560, -652939]]]
  g := ![![![-1221, 1390, -30], ![-7252, 7721, 1360], ![-4582, 2020, 9081]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-485205415, -130527885, -6637981]] ![![617556204550409198134073, -116267004727718069657485, 19452682804915487175133]]
  ![![-67367201, 12683190, -2122030]] where
 M := ![![![-67367201, 12683190, -2122030]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-67367201, 12683190, -2122030]] ![![7661, 1390, -30]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [45, 53, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 47, 24], [61, 101, 125], [0, 1]]
 g := ![![[147, 14, 39], [39, 35], [84, 88, 113], [143, 1], [39, 81, 17], [2, 1], []], ![[35, 33, 6, 54], [67, 16], [91, 92, 56, 120], [73, 25], [138, 48, 75, 130], [77, 69], [130, 129]], ![[68, 73, 103, 123], [75, 119], [61, 87, 130, 119], [141, 36], [78, 97, 61, 85], [59, 123], [29, 129]]]
 h' := ![![[90, 47, 24], [78, 84, 28], [94, 107, 66], [18, 90, 34], [33, 4, 148], [59, 147, 100], [0, 0, 1], [0, 1]], ![[61, 101, 125], [12, 98, 76], [135, 126, 145], [135, 2, 81], [80, 102, 144], [38, 13, 69], [15, 86, 101], [90, 47, 24]], ![[0, 1], [138, 116, 45], [91, 65, 87], [40, 57, 34], [96, 43, 6], [8, 138, 129], [32, 63, 47], [61, 101, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 45], []]
 b := ![[], [67, 34, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [45, 53, 147, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94913, -23691, 1043]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-637, -159, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [7, 57, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 47, 40], [9, 103, 111], [0, 1]]
 g := ![![[68, 13, 43], [113, 40, 69], [16, 96, 45], [35, 123], [101, 140, 144], [137, 1], []], ![[138, 97, 66, 29], [9, 143, 106, 31], [10, 55, 54, 145], [77, 74], [6, 37, 138, 16], [69, 39], [84, 90]], ![[0, 43, 104, 56], [23, 67, 50, 93], [84, 41, 7, 117], [16, 81], [7, 138, 88, 106], [131, 95], [13, 90]]]
 h' := ![![[128, 47, 40], [115, 85, 88], [39, 82, 89], [96, 123, 14], [48, 149, 127], [98, 36, 139], [0, 0, 1], [0, 1]], ![[9, 103, 111], [65, 147, 82], [150, 127, 65], [65, 76, 20], [0, 22, 15], [129, 89, 53], [92, 121, 103], [128, 47, 40]], ![[0, 1], [0, 70, 132], [38, 93, 148], [6, 103, 117], [119, 131, 9], [89, 26, 110], [141, 30, 47], [9, 103, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 9], []]
 b := ![[], [67, 134, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [7, 57, 14, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![679047, 0, 0]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4497, 0, 0]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![147610629023899, -27790580964331, 4649654110635]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![147610629023899, -27790580964331, 4649654110635]] 
 ![![157, 0, 0], ![0, 157, 0], ![40, 50, 1]] where
  M :=![![![147610629023899, -27790580964331, 4649654110635], ![-734645349480330, 138311320802629, -23140926853696], ![3656266442883968, -688363495772938, 115170393948933]]]
  hmulB := by decide  
  f := ![![![-9961363, 111549, 424573]], ![![-67082534, -10810509, 536122]], ![![-24441328, -3848524, 213469]]]
  g := ![![![-244430161793, -1657791633733, 4649654110635], ![1216507800430, 8250685754697, -23140926853696], ![-6054454236136, -41062950275284, 115170393948933]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [24, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 156], [0, 1]]
 g := ![![[69, 64], [67], [100, 132], [101, 130], [102, 9], [17], [1]], ![[60, 93], [67], [52, 25], [68, 27], [113, 148], [17], [1]]]
 h' := ![![[71, 156], [103, 8], [112, 58], [88, 140], [64, 82], [11, 154], [133, 71], [0, 1]], ![[0, 1], [43, 149], [148, 99], [137, 17], [77, 75], [112, 3], [150, 86], [71, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [15, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [24, 86, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1226, -198, 40]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -14, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9961363, 111549, 424573]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-9961363, 111549, 424573]] 
 ![![157, 0, 0], ![106, 1, 0], ![68, 0, 1]] where
  M :=![![![-9961363, 111549, 424573], ![-67082534, -10810509, 536122], ![-84707276, -68154778, -10274387]]]
  hmulB := by decide  
  f := ![![![147610629023899, -27790580964331, 4649654110635]], ![![94981409726452, -17882103575901, 2991862476902]], ![![87221587366300, -16421165613678, 2747432315109]]]
  g := ![![![-322653, 111549, 424573], ![6639332, -10810509, 536122], ![49925844, -68154778, -10274387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![147610629023899, -27790580964331, 4649654110635]] ![![-9961363, 111549, 424573]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![942143980973, 756745807014, 114015028366]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![942143980973, 756745807014, 114015028366]] 
 ![![163, 0, 0], ![0, 163, 0], ![130, 68, 1]] where
  M :=![![![942143980973, 756745807014, 114015028366], ![-18014374481828, 714113924241, 870760835380], ![-137580211990040, -19755896152588, 1584874759621]]]
  hmulB := by decide  
  f := ![![![112481237862156556495927, -21176787663917693190754, 3543097495441286584878]], ![![-559809404279723280410724, 105395042871273983326171, -17633690168476406605876]], ![![-126738377437555573495278, 23860972361929817694372, -3992189597216139978191]]]
  g := ![![![-85152206789, -42921939398, 114015028366], ![-804989466756, -358881121973, 870760835380], ![-2108060924790, -782376563232, 1584874759621]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [146, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 162], [0, 1]]
 g := ![![[41, 115], [46, 133], [24], [144], [10], [71, 69], [1]], ![[0, 48], [0, 30], [24], [144], [10], [79, 94], [1]]]
 h' := ![![[45, 162], [130, 142], [156, 40], [143, 26], [125, 12], [66, 93], [17, 45], [0, 1]], ![[0, 1], [0, 21], [0, 123], [9, 137], [13, 151], [13, 70], [86, 118], [45, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [155, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [146, 118, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-209, -1308, -374]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![297, 148, -374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112481237862156556495927, -21176787663917693190754, 3543097495441286584878]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![112481237862156556495927, -21176787663917693190754, 3543097495441286584878]] 
 ![![163, 0, 0], ![94, 1, 0], ![129, 0, 1]] where
  M :=![![![112481237862156556495927, -21176787663917693190754, 3543097495441286584878], ![-559809404279723280410724, 105395042871273983326171, -17633690168476406605876], ![2786123046619272243728408, -524542023942770467198972, 87761352702797576720295]]]
  hmulB := by decide  
  f := ![![![942143980973, 756745807014, 114015028366]], ![![432804660918, 440786624439, 71093088968]], ![![-98427229721, 477695171486, 99955910545]]]
  g := ![![![10098403075818980042807, -21176787663917693190754, 3543097495441286584878], ![-50258879769607492398238, 105395042871273983326171, -17633690168476406605876], ![250134103058765697935667, -524542023942770467198972, 87761352702797576720295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![942143980973, 756745807014, 114015028366]] ![![112481237862156556495927, -21176787663917693190754, 3543097495441286584878]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [117, 130, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 111, 98], [7, 55, 69], [0, 1]]
 g := ![![[50, 59, 63], [6, 110, 162], [19, 95, 107], [105, 127], [77, 18], [41, 2, 1], []], ![[34, 97, 70, 16], [159, 101, 63, 127], [81, 92, 101, 147], [22, 42], [82, 12], [163, 102, 88, 25], [49, 85]], ![[161, 107, 49, 55], [150, 140, 90, 142], [78, 16, 40, 159], [119, 38], [7, 16], [58, 5, 90, 119], [78, 85]]]
 h' := ![![[162, 111, 98], [133, 76, 49], [115, 99, 117], [18, 25, 21], [121, 42, 36], [46, 114, 39], [0, 0, 1], [0, 1]], ![[7, 55, 69], [120, 132, 123], [118, 145, 105], [98, 75, 98], [0, 105, 84], [143, 77, 124], [137, 110, 55], [162, 111, 98]], ![[0, 1], [112, 126, 162], [84, 90, 112], [123, 67, 48], [128, 20, 47], [46, 143, 4], [108, 57, 111], [7, 55, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 122], []]
 b := ![[], [122, 4, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [117, 130, 165, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103373, -26720, 1002]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-619, -160, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-570459842260051, -62717023224826, 10428990145870]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-570459842260051, -62717023224826, 10428990145870]] 
 ![![173, 0, 0], ![0, 173, 0], ![61, 90, 1]] where
  M :=![![![-570459842260051, -62717023224826, 10428990145870], ![-1647780443047460, -591317822551791, -52288033078956], ![8261509226475048, -1543204376889548, -643605855630747]]]
  hmulB := by decide  
  f := ![![![1733436367784770537552626393, -326353217542613403801258334, 54602297858169290113971762]], ![![-8627163061590747838007538396, 1624231772068431957324682869, -271750919684444113687286572]], ![![-3628719143341931402701600967, 683177179155130629576368408, -114302669074379512666278137]]]
  g := ![![![-6974729717677, -5788012348862, 10428990145870], ![8912078466872, 23783844824013, -52288033078956], ![274690557340755, 325903599016634, -643605855630747]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [15, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 172], [0, 1]]
 g := ![![[101, 150], [159], [89, 52], [95, 88], [57], [168, 34], [1]], ![[0, 23], [159], [24, 121], [158, 85], [57], [39, 139], [1]]]
 h' := ![![[42, 172], [16, 82], [49, 141], [132, 15], [99, 112], [75, 24], [158, 42], [0, 1]], ![[0, 1], [0, 91], [89, 32], [70, 158], [132, 61], [45, 149], [19, 131], [42, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [25, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [15, 131, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6015, 2291, 531]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-222, -263, 531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1733436367784770537552626393, 326353217542613403801258334, -54602297858169290113971762]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-1733436367784770537552626393, 326353217542613403801258334, -54602297858169290113971762]] 
 ![![173, 0, 0], ![82, 1, 0], ![23, 0, 1]] where
  M :=![![![-1733436367784770537552626393, 326353217542613403801258334, -54602297858169290113971762], ![8627163061590747838007538396, -1624231772068431957324682869, 271750919684444113687286572], ![-42936645310142169962591278376, 8083661222221859610632965252, -1352480852383987843637396297]]]
  hmulB := by decide  
  f := ![![![570459842260051, 62717023224826, -10428990145870]], ![![279916112765154, 33145166051951, -4640977797008]], ![![28087093326625, 17258357867402, 2333751920669]]]
  g := ![![![-157448250610064601021008435, 326353217542613403801258334, -54602297858169290113971762], ![783606342303236726727306026, -1624231772068431957324682869, 271750919684444113687286572], ![-3899941074725450506536614533, 8083661222221859610632965252, -1352480852383987843637396297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-570459842260051, -62717023224826, 10428990145870]] ![![-1733436367784770537552626393, 326353217542613403801258334, -54602297858169290113971762]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31062107585265115, 5848047809831552, -978439406253264]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-31062107585265115, 5848047809831552, -978439406253264]] 
 ![![179, 0, 0], ![41, 1, 0], ![109, 0, 1]] where
  M :=![![![-31062107585265115, 5848047809831552, -978439406253264], ![154593426188015712, -29105228772758587, 4869608403578288], ![-769398127765369504, 144854209380859136, -24235620369180299]]]
  hmulB := by decide  
  f := ![![![-127438345, -382774144, -71765008]], ![![34155861, -87584627, -18977120]], ![![323611209, -164661632, -46149907]]]
  g := ![![![-917218840819849, 5848047809831552, -978439406253264], ![4564918937883153, -29105228772758587, 4869608403578288], ![-22719207218658891, 144854209380859136, -24235620369180299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-302664320934072844085, 56982463739591472567, -9533760632818760883]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-302664320934072844085, 56982463739591472567, -9533760632818760883]] 
 ![![179, 0, 0], ![47, 1, 0], ![118, 0, 1]] where
  M :=![![![-302664320934072844085, 56982463739591472567, -9533760632818760883], ![1506334179985364219514, -283596799668435322319, 47448703106772711684], ![-7496895090870088446072, 1411436773771818796146, -236148096561662610635]]]
  hmulB := by decide  
  f := ![![![-148393892701, -44708993127, -2992325151]], ![![-36322489291, -12534815192, -1052182125]], ![![-55718832686, -26298721668, -3034664405]]]
  g := ![![![-10367912636995856260, 56982463739591472567, -9533760632818760883], ![51600205574316449105, -283596799668435322319, 47448703106772711684], ![-256809765719940691676, 1411436773771818796146, -236148096561662610635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3927032498915715481, -108558968183274821, -180354492426523517]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![3927032498915715481, -108558968183274821, -180354492426523517]] 
 ![![179, 0, 0], ![90, 1, 0], ![134, 0, 1]] where
  M :=![![![3927032498915715481, -108558968183274821, -180354492426523517], ![28496009803390715686, 4287741483768762515, -288913460609798338], ![45648326776348137404, 29073836724610312362, 3998828023158964177]]]
  hmulB := by decide  
  f := ![![![-25545763582667134303306942732513879511, 4809488421222210135316048637023729837, -804677586139322907544464907878612753]], ![![-12133964602402397027405583187047085704, 2284455583796706277599029968801000175, -382213250935509354476146692625307434]], ![![-22658616938661967478385701426602169574, 4265926733986722922172250309205085916, -713734045351814921069300149962824837]]]
  g := ![![![211535428047846931, -108558968183274821, -180354492426523517], ![-1780370502871982868, 4287741483768762515, -288913460609798338], ![-17356647673418330586, 29073836724610312362, 3998828023158964177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-31062107585265115, 5848047809831552, -978439406253264]] ![![-302664320934072844085, 56982463739591472567, -9533760632818760883]]
  ![![25545763582667134303306942732513879511, -4809488421222210135316048637023729837, 804677586139322907544464907878612753]] where
 M := ![![![25545763582667134303306942732513879511, -4809488421222210135316048637023729837, 804677586139322907544464907878612753]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![25545763582667134303306942732513879511, -4809488421222210135316048637023729837, 804677586139322907544464907878612753]] ![![3927032498915715481, -108558968183274821, -180354492426523517]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2157677080525, 433273829192, -52913928]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![2157677080525, 433273829192, -52913928]] 
 ![![181, 0, 0], ![40, 1, 0], ![29, 0, 1]] where
  M :=![![![2157677080525, 433273829192, -52913928], ![8360400624, 2157782908381, 433220915264], ![-68448904611712, -858081429904, 2591003823645]]]
  hmulB := by decide  
  f := ![![![5962562588645052456123401, -1122568743662782543541928, 187817461611949944417256]], ![![1153742235420519375839832, -217214486635857177759051, 36342249626669420870528]], ![![1771298439970928573973905, -333481491363575247416536, 55794932431584908045661]]]
  g := ![![![-83821776703, 433273829192, -52913928], ![-546222997112, 2157782908381, 433220915264], ![-603672697797, -858081429904, 2591003823645]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1481334388335, 278890101116, -46661223338]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-1481334388335, 278890101116, -46661223338]] 
 ![![181, 0, 0], ![70, 1, 0], ![168, 0, 1]] where
  M :=![![![-1481334388335, 278890101116, -46661223338], ![7372473287404, -1388011941659, 232228877778], ![-36692162688924, 6908015531848, -1155783063881]]]
  hmulB := by decide  
  f := ![![![16355165, 2477428, -162506]], ![![6467058, 1050277, -50058]], ![![13159724, 2415768, -45889]]]
  g := ![![![-72732353291, 278890101116, -46661223338], ![361982639430, -1388011941659, 232228877778], ![-1801556326996, 6908015531848, -1155783063881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![2157677080525, 433273829192, -52913928]] ![![-1481334388335, 278890101116, -46661223338]]
  ![![16355165, 2477428, -162506]] where
 M := ![![![16355165, 2477428, -162506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![16355165, 2477428, -162506]] ![![-1481334388335, 278890101116, -46661223338]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13268685058897327, -2498088849413367, 417956324925859]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![13268685058897327, -2498088849413367, 417956324925859]] 
 ![![191, 0, 0], ![0, 191, 0], ![126, 22, 1]] where
  M :=![![![13268685058897327, -2498088849413367, 417956324925859], ![-66037099338285722, 12432772409045609, -2080132524487508], ![328660938869026264, -61876834289310706, 10352639884558101]]]
  hmulB := by decide  
  f := ![![![77967371, 22055443, 1283855]], ![![-202849090, 75399661, 23339298]], ![![8762302, 21928014, 4052195]]]
  g := ![![![-206250323988277, -61220565433415, 417956324925859], ![1026490045796546, 304689465695135, -2080132524487508], ![-5108752285786882, -1516413150521408, 10352639884558101]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [31, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 190], [0, 1]]
 g := ![![[22, 1], [155, 5], [30, 39], [179, 43], [122, 1], [24, 39], [1]], ![[104, 190], [183, 186], [172, 152], [76, 148], [13, 190], [166, 152], [1]]]
 h' := ![![[82, 190], [161, 1], [25, 14], [181, 82], [38, 59], [20, 1], [160, 82], [0, 1]], ![[0, 1], [52, 190], [27, 177], [29, 109], [101, 132], [102, 190], [8, 109], [82, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [26, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [31, 109, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![713, 173, -105]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 13, -105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77967371, -22055443, -1283855]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-77967371, -22055443, -1283855]] 
 ![![191, 0, 0], ![168, 1, 0], ![44, 0, 1]] where
  M :=![![![-77967371, -22055443, -1283855], ![202849090, -75399661, -23339298], ![3687609084, 249527686, -98738959]]]
  hmulB := by decide  
  f := ![![![-13268685058897327, 2498088849413367, -417956324925859]], ![![-11325141311813954, 2132178818284817, -356735759492444]], ![![-4777398332253972, 899438448499994, -150485435504167]]]
  g := ![![![19287103, -22055443, -1283855], ![72758750, -75399661, -23339298], ![-177426848, 249527686, -98738959]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![13268685058897327, -2498088849413367, 417956324925859]] ![![-77967371, -22055443, -1283855]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [44, 111, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 71, 45], [140, 121, 148], [0, 1]]
 g := ![![[34, 189, 192], [120, 8], [38, 100], [153, 36], [58, 112], [20, 25], [1]], ![[6, 20, 44, 90], [135, 126], [110, 64], [3, 157], [46, 118], [150, 9], [9, 159, 18, 29]], ![[121, 40, 99, 120], [26, 6], [65, 131], [165, 151], [150, 139], [46, 64], [145, 29, 83, 164]]]
 h' := ![![[48, 71, 45], [52, 118, 112], [11, 118, 89], [77, 162, 10], [132, 117, 187], [91, 79, 43], [149, 82, 188], [0, 1]], ![[140, 121, 148], [182, 57, 141], [116, 127, 60], [18, 51, 8], [27, 85, 100], [11, 7, 73], [186, 64, 190], [48, 71, 45]], ![[0, 1], [42, 18, 133], [118, 141, 44], [58, 173, 175], [62, 184, 99], [183, 107, 77], [108, 47, 8], [140, 121, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 179], []]
 b := ![[], [84, 48, 159], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [44, 111, 5, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![198018, -2123, -4246]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1026, -11, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB234I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB234I3 : PrimesBelowBoundCertificateInterval O 137 193 234 where
  m := 11
  g := ![3, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB234I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![181, 181, 181]
    · exact ![36481, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I157N1, I163N1, I173N1, I179N0, I179N1, I179N2, I181N0, I181N1, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [], [], [I157N1], [I163N1], [], [I173N1], [I179N0, I179N1, I179N2], [I181N0, I181N1, I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
