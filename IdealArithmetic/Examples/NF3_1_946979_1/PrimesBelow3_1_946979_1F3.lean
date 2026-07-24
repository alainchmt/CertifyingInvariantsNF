
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [7, 55, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 106, 50], [31, 32, 89], [0, 1]]
 g := ![![[43, 41, 46], [97, 9, 45], [64, 41], [110, 94, 136], [108, 81], [8, 1], []], ![[110, 96, 56, 132], [7, 123, 64, 103], [115, 28], [25, 33, 79, 10], [116, 131], [117, 51], [20, 137]], ![[86, 73, 66, 112], [57, 133, 52, 7], [137, 57], [13, 82, 92, 107], [120, 80], [111, 116], [120, 137]]]
 h' := ![![[116, 106, 50], [16, 67, 121], [34, 82, 36], [64, 114, 72], [17, 50, 54], [83, 109, 9], [0, 0, 1], [0, 1]], ![[31, 32, 89], [91, 21, 133], [59, 58, 109], [13, 98, 81], [135, 133, 58], [104, 13, 39], [111, 15, 32], [116, 106, 50]], ![[0, 1], [54, 51, 24], [121, 138, 133], [78, 66, 125], [39, 95, 27], [103, 17, 91], [121, 124, 106], [31, 32, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 7], []]
 b := ![[], [88, 133, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [7, 55, 131, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46009, 695, 417]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![331, 5, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-268577873125794393539145, -17472357763929648194420, -16614466918443990390024]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-268577873125794393539145, -17472357763929648194420, -16614466918443990390024]] 
 ![![149, 0, 0], ![0, 149, 0], ![36, 46, 1]] where
  M :=![![![-268577873125794393539145, -17472357763929648194420, -16614466918443990390024], ![-3106905313749026202934488, -202120005452018431979049, -192195935403226130138620], ![-3267330901854844212356540, -212556506557829243852728, -202120005452018431979049]]]
  hmulB := by decide  
  f := ![![![-379176307309, -1469917308, 32566416824]], ![![6089919946088, -509441974605, -16169090388]], ![![1786651650472, -153877443622, -542477361]]]
  g := ![![![2211697556632142687931, 5012034365667744360716, -16614466918443990390024], ![25584888327296070349368, 57979147806015997009379, -192195935403226130138620], ![26905968418911539187176, 60972911035134353202574, -202120005452018431979049]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [69, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 148], [0, 1]]
 g := ![![[67, 54], [69], [86, 113], [130], [67, 42], [16], [1]], ![[0, 95], [69], [81, 36], [130], [48, 107], [16], [1]]]
 h' := ![![[145, 148], [87, 59], [26, 101], [135, 34], [145, 117], [81, 41], [80, 145], [0, 1]], ![[0, 1], [0, 90], [69, 48], [148, 115], [124, 32], [66, 108], [96, 4], [145, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [94, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [69, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2178, 197, 14]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -3, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379176307309, 1469917308, -32566416824]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![379176307309, 1469917308, -32566416824]] 
 ![![149, 0, 0], ![90, 1, 0], ![117, 0, 1]] where
  M :=![![![379176307309, 1469917308, -32566416824], ![-6089919946088, 509441974605, 16169090388], ![274874536596, -559508755240, 509441974605]]]
  hmulB := by decide  
  f := ![![![268577873125794393539145, 17472357763929648194420, 16614466918443990390024]], ![![183079959027318937056762, 11910283249702595768301, 11325489651430773592220]], ![![232825114480354283600245, 15146458825084550889932, 14402769361811847702093]]]
  g := ![![![27229224953, 1469917308, -32566416824], ![-361285108966, 509441974605, 16169090388], ![-60228513561, -559508755240, 509441974605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-268577873125794393539145, -17472357763929648194420, -16614466918443990390024]] ![![379176307309, 1469917308, -32566416824]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247735931032, 72910996500, -89695216283]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![247735931032, 72910996500, -89695216283]] 
 ![![151, 0, 0], ![0, 151, 0], ![47, 10, 1]] where
  M :=![![![247735931032, 72910996500, -89695216283], ![-16773005444921, 606516796164, 802020961500], ![13634356345500, -1816462662811, 606516796164]]]
  hmulB := by decide  
  f := ![![![-12084130830368024091996, -786134221248490916063, -747535117404339996612]], ![![-139789066954611579366444, -9093990360750664105548, -8647476433733400076693]], ![![-13992396807595236604583, -910276636536857817143, -865582153748931421942]]]
  g := ![![![29559013883, 6422934830, -89695216283], ![-360715169771, -49097303436, 802020961500], ![-98489623008, -52196229301, 606516796164]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [64, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 150], [0, 1]]
 g := ![![[10, 59], [112, 127], [43, 139], [58], [135, 68], [88], [1]], ![[0, 92], [70, 24], [22, 12], [58], [103, 83], [88], [1]]]
 h' := ![![[115, 150], [80, 19], [117, 91], [95, 21], [118, 71], [125, 81], [87, 115], [0, 1]], ![[0, 1], [0, 132], [12, 60], [94, 130], [129, 80], [78, 70], [24, 36], [115, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [11, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [64, 36, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1482, -67, 99]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -7, 99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12084130830368024091996, 786134221248490916063, 747535117404339996612]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![12084130830368024091996, 786134221248490916063, 747535117404339996612]] 
 ![![151, 0, 0], ![41, 1, 0], ![108, 0, 1]] where
  M :=![![![12084130830368024091996, 786134221248490916063, 747535117404339996612], ![139789066954611579366444, 9093990360750664105548, 8647476433733400076693], ![147007099373467801303781, 9563560110879816278152, 9093990360750664105548]]]
  hmulB := by decide  
  f := ![![![-247735931032, -72910996500, 89695216283]], ![![43813458759, -23813693064, 19042933153]], ![![-267482363556, -40118708339, 60136202400]]]
  g := ![![![-668087184903899490733, 786134221248490916063, 747535117404339996612], ![-7728423792578628193668, 9093990360750664105548, 8647476433733400076693], ![-8127482279030969466885, 9563560110879816278152, 9093990360750664105548]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![247735931032, 72910996500, -89695216283]] ![![12084130830368024091996, 786134221248490916063, 747535117404339996612]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1946162208, 126607758, 120391331]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![1946162208, 126607758, 120391331]] 
 ![![157, 0, 0], ![0, 157, 0], ![44, 111, 1]] where
  M :=![![![1946162208, 126607758, 120391331], ![22513178897, 1464596884, 1392685338], ![23675650746, 1540221595, 1464596884]]]
  hmulB := by decide  
  f := ![![![-31622, -211, 2800]], ![![523600, -42822, -2321]], ![![361075, -30026, -1129]]]
  g := ![![![-21344308, -84311019, 120391331], ![-246910675, -975308762, 1392685338], ![-259659950, -1025668997, 1464596884]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [123, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 156], [0, 1]]
 g := ![![[130, 75], [89], [82, 101], [3, 37], [49, 33], [105], [1]], ![[46, 82], [89], [151, 56], [106, 120], [56, 124], [105], [1]]]
 h' := ![![[24, 156], [74, 46], [119, 106], [102, 27], [96, 42], [16, 70], [34, 24], [0, 1]], ![[0, 1], [79, 111], [151, 51], [122, 130], [5, 115], [126, 87], [139, 133], [24, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142]]
 b := ![[], [90, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [123, 133, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-865, 312, -430]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![115, 306, -430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31622, -211, 2800]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-31622, -211, 2800]] 
 ![![157, 0, 0], ![35, 1, 0], ![117, 0, 1]] where
  M :=![![![-31622, -211, 2800], ![523600, -42822, -2321], ![-39457, 48444, -42822]]]
  hmulB := by decide  
  f := ![![![1946162208, 126607758, 120391331]], ![![577253861, 37553302, 35709439]], ![![1601125026, 104161333, 99047023]]]
  g := ![![![-2241, -211, 2800], ![14611, -42822, -2321], ![20861, 48444, -42822]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![1946162208, 126607758, 120391331]] ![![-31622, -211, 2800]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -2, -2]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-31, -2, -2]] 
 ![![163, 0, 0], ![33, 1, 0], ![64, 0, 1]] where
  M :=![![![-31, -2, -2], ![-374, -23, -22], ![-374, -26, -23]]]
  hmulB := by decide  
  f := ![![![43, -6, 2]], ![![11, -1, 0]], ![![10, -2, 1]]]
  g := ![![![1, -2, -2], ![11, -23, -22], ![12, -26, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1477845371352, -96141363946, -91420833545]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-1477845371352, -96141363946, -91420833545]] 
 ![![163, 0, 0], ![43, 1, 0], ![69, 0, 1]] where
  M :=![![![-1477845371352, -96141363946, -91420833545], ![-17095695872915, -1112162037172, -1057555003406], ![-17978435057902, -1169588714481, -1112162037172]]]
  hmulB := by decide  
  f := ![![![6764702, 535567, -1065336]], ![![562358, 208929, -244897]], ![![3478009, 102461, -383326]]]
  g := ![![![54995526337, -96141363946, -91420833545], ![636187527365, -1112162037172, -1057555003406], ![669037179323, -1169588714481, -1112162037172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10346572, 513085, 362606]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-10346572, 513085, 362606]] 
 ![![163, 0, 0], ![87, 1, 0], ![38, 0, 1]] where
  M :=![![![-10346572, 513085, 362606], ![67807322, -11796996, 5643935], ![95946895, 4111962, -11796996]]]
  hmulB := by decide  
  f := ![![![-115961468373546, -7543883785632, -7173479921051]], ![![-70123242292853, -4561873853002, -4337886348303]], ![![-35688601632564, -2321725198585, -2207728746560]]]
  g := ![![![-421865, 513085, 362606], ![5396788, -11796996, 5643935], ![1144123, 4111962, -11796996]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-31, -2, -2]] ![![-1477845371352, -96141363946, -91420833545]]
  ![![115961468373546, 7543883785632, 7173479921051]] where
 M := ![![![115961468373546, 7543883785632, 7173479921051]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![115961468373546, 7543883785632, 7173479921051]] ![![-10346572, 513085, 362606]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5146588958, -1291706942, 1651339041]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-5146588958, -1291706942, 1651339041]] 
 ![![167, 0, 0], ![0, 167, 0], ![126, 134, 1]] where
  M :=![![![-5146588958, -1291706942, 1651339041], ![308800400667, -11751945122, -14208776362], ![-241549198154, 33239591465, -11751945122]]]
  hmulB := by decide  
  f := ![![![-3655102608628314642, -237783029921882923, -226107909292030018]], ![![-42282179037609613366, -2750670971460194570, -2615613329140712153]], ![![-36951020037857772111, -2403851941820959876, -2285823075731206020]]]
  g := ![![![-1276738372, -1332761308, 1651339041], ![12569498337, 11330683158, -14208776362], ![7420334654, 9628743939, -11751945122]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [41, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 166], [0, 1]]
 g := ![![[79, 12], [81, 144], [52, 97], [141], [144], [146, 14], [1]], ![[122, 155], [96, 23], [163, 70], [141], [144], [57, 153], [1]]]
 h' := ![![[101, 166], [19, 124], [39, 155], [160, 40], [116, 59], [26, 155], [126, 101], [0, 1]], ![[0, 1], [18, 43], [163, 12], [25, 127], [63, 108], [150, 12], [140, 66], [101, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [114, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [41, 66, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415, -57, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47, 47, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3655102608628314642, 237783029921882923, 226107909292030018]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![3655102608628314642, 237783029921882923, 226107909292030018]] 
 ![![167, 0, 0], ![29, 1, 0], ![45, 0, 1]] where
  M :=![![![3655102608628314642, 237783029921882923, 226107909292030018], ![42282179037609613366, 2750670971460194570, 2615613329140712153], ![44465426595392106601, 2892702338276978614, 2750670971460194570]]]
  hmulB := by decide  
  f := ![![![5146588958, 1291706942, -1651339041]], ![![-955385155, 294679320, -201676981]], ![![2833207792, 149025275, -374600669]]]
  g := ![![![-80332102857770305, 237783029921882923, 226107909292030018], ![-929280712251904647, 2750670971460194570, 2615613329140712153], ![-977264281020054065, 2892702338276978614, 2750670971460194570]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-5146588958, -1291706942, 1651339041]] ![![3655102608628314642, 237783029921882923, 226107909292030018]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [90, 38, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 56, 134], [105, 116, 39], [0, 1]]
 g := ![![[155, 154, 78], [47, 117], [137, 82, 163], [100, 38, 24], [146, 64], [160, 168, 1], []], ![[64, 160, 161, 82], [55, 164], [134, 111, 64, 162], [104, 62, 125, 99], [34, 35], [148, 170, 160, 98], [137, 137]], ![[17, 7, 105, 131], [12, 9], [70, 23, 106, 80], [23, 161, 59, 161], [108, 60], [70, 86, 140, 166], [59, 137]]]
 h' := ![![[63, 56, 134], [55, 130, 50], [126, 59, 64], [169, 170, 110], [132, 33, 102], [132, 79, 165], [0, 0, 1], [0, 1]], ![[105, 116, 39], [32, 31, 38], [22, 18, 106], [111, 77, 75], [30, 125, 165], [29, 34, 143], [116, 73, 116], [63, 56, 134]], ![[0, 1], [165, 12, 85], [131, 96, 3], [168, 99, 161], [57, 15, 79], [75, 60, 38], [6, 100, 56], [105, 116, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 8], []]
 b := ![[], [81, 60, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [90, 38, 5, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14126488, -98610, -5190]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81656, -570, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [110, 113, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 28, 83], [38, 150, 96], [0, 1]]
 g := ![![[54, 152, 66], [100, 44, 95], [104, 177], [144, 13], [91, 100, 70], [91, 5, 1], []], ![[95, 57, 50, 124], [72, 1, 107, 145], [154, 106], [127, 29], [3, 46, 90, 77], [11, 160, 141, 172], [71, 87]], ![[73, 62, 89, 38], [173, 131, 112, 96], [47, 16], [66, 117], [16, 33, 160, 34], [142, 159, 176, 84], [58, 87]]]
 h' := ![![[146, 28, 83], [98, 26, 31], [45, 13, 128], [108, 104, 78], [14, 35, 152], [14, 86, 138], [0, 0, 1], [0, 1]], ![[38, 150, 96], [140, 34, 6], [139, 16, 52], [130, 138, 105], [73, 164, 108], [120, 75, 93], [81, 70, 150], [146, 28, 83]], ![[0, 1], [41, 119, 142], [64, 150, 178], [143, 116, 175], [8, 159, 98], [166, 18, 127], [76, 109, 28], [38, 150, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 123], []]
 b := ![[], [159, 142, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [110, 113, 174, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146064, 358, 19332]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-816, 2, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [108, 72, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 135, 102], [121, 45, 79], [0, 1]]
 g := ![![[13, 57, 136], [141, 39], [26, 50, 42], [122, 167], [79, 60, 136], [3, 165, 1], []], ![[136, 122], [56, 38], [22, 135, 74, 167], [127, 15], [120, 153, 63, 45], [106, 95, 3, 29], [84, 87]], ![[166, 77, 35, 65], [75, 167], [158, 24, 139, 37], [121, 102], [44, 24, 31, 121], [70, 143, 147, 101], [107, 87]]]
 h' := ![![[44, 135, 102], [118, 61, 91], [88, 11, 43], [119, 46, 59], [156, 136, 158], [38, 64, 91], [0, 0, 1], [0, 1]], ![[121, 45, 79], [139, 118], [157, 92, 161], [134, 102, 107], [128, 58, 167], [10, 161, 125], [104, 56, 45], [44, 135, 102]], ![[0, 1], [82, 2, 90], [134, 78, 158], [3, 33, 15], [138, 168, 37], [3, 137, 146], [8, 125, 135], [121, 45, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 85], []]
 b := ![[], [90, 123, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [108, 72, 16, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30589, 1086, 2172]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169, 6, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2323686293222247, 495752007790256, -280401297689194]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-2323686293222247, 495752007790256, -280401297689194]] 
 ![![191, 0, 0], ![0, 191, 0], ![92, 77, 1]] where
  M :=![![![-2323686293222247, 495752007790256, -280401297689194], ![-52435042667879278, -1202081102465471, 5453272085692816], ![92705625456777872, -6749830091877322, -1202081102465471]]]
  hmulB := by decide  
  f := ![![![200280937173343339170498408223, 13029294434648975676377923084, 12389557510208353159081147542]], ![![2316847254408962040748174590354, 150722707132509926534173818055, 143322238781138732440157153924]], ![![1043243784652968705721350621102, 67868318518983854483544611151, 64535991540415501649537907037]]]
  g := ![![![122896508346511, 115636921098734, -280401297689194], ![-2901235992416850, -2204733150266033, 5453272085692816], ![1064382653840844, 449269187423895, -1202081102465471]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [73, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 190], [0, 1]]
 g := ![![[54, 147], [158, 134], [144, 163], [3, 5], [185, 16], [38, 177], [1]], ![[74, 44], [45, 57], [122, 28], [157, 186], [143, 175], [27, 14], [1]]]
 h' := ![![[69, 190], [117, 23], [184, 158], [163, 113], [56, 14], [91, 187], [118, 69], [0, 1]], ![[0, 1], [176, 168], [8, 33], [129, 78], [67, 177], [6, 4], [104, 122], [69, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [114, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [73, 122, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7159, -1032, 1336]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-681, -544, 1336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![200280937173343339170498408223, 13029294434648975676377923084, 12389557510208353159081147542]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![200280937173343339170498408223, 13029294434648975676377923084, 12389557510208353159081147542]] 
 ![![191, 0, 0], ![108, 1, 0], ![103, 0, 1]] where
  M :=![![![200280937173343339170498408223, 13029294434648975676377923084, 12389557510208353159081147542], ![2316847254408962040748174590354, 150722707132509926534173818055, 143322238781138732440157153924], ![2436478059279358451482671616708, 158505299934946100998867815878, 150722707132509926534173818055]]]
  hmulB := by decide  
  f := ![![![-2323686293222247, 495752007790256, -280401297689194]], ![![-1588445876104094, 274026888685247, -130000356359896]], ![![-767717605995359, 232003281206906, -157504789342683]]]
  g := ![![![-13000038143037729891432855925, 13029294434648975676377923084, 12389557510208353159081147542], ![-150384270734865965792035521538, 150722707132509926534173818055, 143322238781138732440157153924], ![-158149388315933732405313904491, 158505299934946100998867815878, 150722707132509926534173818055]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-2323686293222247, 495752007790256, -280401297689194]] ![![200280937173343339170498408223, 13029294434648975676377923084, 12389557510208353159081147542]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 0, 6]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-73, 0, 6]] 
 ![![193, 0, 0], ![72, 1, 0], ![20, 0, 1]] where
  M :=![![![-73, 0, 6], ![1122, -97, 0], ![0, 102, -97]]]
  hmulB := by decide  
  f := ![![![-9409, -612, -582]], ![![-4074, -265, -252]], ![![-1568, -102, -97]]]
  g := ![![![-1, 0, 6], ![42, -97, 0], ![-28, 102, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-876694871106687288314526, -57033463924273984556377, -54233127115238382883592]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-876694871106687288314526, -57033463924273984556377, -54233127115238382883592]] 
 ![![193, 0, 0], ![146, 1, 0], ![115, 0, 1]] where
  M :=![![![-876694871106687288314526, -57033463924273984556377, -54233127115238382883592], ![-10141594770549577599231704, -659762362645733756780158, -627368103167013830120147], ![-10665257753839235112042499, -693829305261956570795556, -659762362645733756780158]]]
  hmulB := by decide  
  f := ![![![2815311161768, 672767050414, -871155659883]], ![![1285644151399, 541574731408, -620664708748]], ![![2329369026066, 310194281751, -486440243965]]]
  g := ![![![70917100933107401494972, -57033463924273984556377, -54233127115238382883592], ![820368093471161354168333, -659762362645733756780158, -627368103167013830120147], ![862727940511221794061279, -693829305261956570795556, -659762362645733756780158]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55199721152, 1082235724, -5566570443]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![55199721152, 1082235724, -5566570443]] 
 ![![193, 0, 0], ![168, 1, 0], ![66, 0, 1]] where
  M :=![![![55199721152, 1082235724, -5566570443], ![-1040948672841, 77466002924, 11904592964], ![202378080388, -98960640427, 77466002924]]]
  hmulB := by decide  
  f := ![![![-7179067752761374705404, -467034900261447842185, -444103537999409821268]], ![![-6679433907097412368316, -434531175361072398484, -413195742418532519363]], ![![-2907533668555137186763, -189149865089117788482, -179862627506346029140]]]
  g := ![![![1247553206, 1082235724, -5566570443], ![-76896063729, 77466002924, 11904592964], ![60699530980, -98960640427, 77466002924]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-73, 0, 6]] ![![-876694871106687288314526, -57033463924273984556377, -54233127115238382883592]]
  ![![7179067752761374705404, 467034900261447842185, 444103537999409821268]] where
 M := ![![![7179067752761374705404, 467034900261447842185, 444103537999409821268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![7179067752761374705404, 467034900261447842185, 444103537999409821268]] ![![55199721152, 1082235724, -5566570443]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB276I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB276I3 : PrimesBelowBoundCertificateInterval O 137 193 276 where
  m := 11
  g := ![1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB276I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![193, 193, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I149N1, I151N1, I157N1, I163N0, I163N1, I163N2, I167N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N1], [I151N1], [I157N1], [I163N0, I163N1, I163N2], [I167N1], [], [], [], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
