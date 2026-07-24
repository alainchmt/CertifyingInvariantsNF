
import IdealArithmetic.Examples.NF3_1_400040_1.RI3_1_400040_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1098120528, -667163798, 418500235]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1098120528, -667163798, 418500235]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1098120528, -667163798, 418500235], ![52888683392, 3857785501, -5834637510], ![-65830647770, 2104684065, 2274794342]]]
  hmulB := by decide  
  f := ![![![-21055737222672713492, -2398471208680886191, -2278174782376770245]], ![![-131893544525244442318, -15024069962937839263, -14270530825781201200]], ![![-182637243821258265625, -20804314107151222070, -19760864167147553672]]]
  g := ![![![549060264, -667163798, 418500235], ![26444341696, 3857785501, -5834637510], ![-32915323885, 2104684065, 2274794342]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![954094467346180109723087324460787975895, 108681452759936397257002697713518718869, 103230484524320012740092888817220541610]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![954094467346180109723087324460787975895, 108681452759936397257002697713518718869, 103230484524320012740092888817220541610]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![954094467346180109723087324460787975895, 108681452759936397257002697713518718869, 103230484524320012740092888817220541610], ![11952932331878655939783135867212390117724, 1361565437207843776166549070833371965076, 1293275496648003998050212754769628271910], ![16551610805019248104003481945407744679020, 1885403562615842151906221043191460635275, 1790840280011972980677650052791148663293]]]
  hmulB := by decide  
  f := ![![![-61629687750958469982, -2425590313035482867, 5304224586854857430]], ![![292289811961883176543, -17554282408342091416, -4171614684895128190]], ![![-86178444681075630701, 27200688875450124694, -14675648134522716853]]]
  g := ![![![371091265030961849862995868965024357708, 108681452759936397257002697713518718869, 103230484524320012740092888817220541610], ![4649045699011404082783187020804694940369, 1361565437207843776166549070833371965076, 1293275496648003998050212754769628271910], ![6437683481195716485709805424712567690226, 1885403562615842151906221043191460635275, 1790840280011972980677650052791148663293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1098120528, -667163798, 418500235]] ![![1098120528, -667163798, 418500235]]
  ![![-61629687750958469982, -2425590313035482867, 5304224586854857430]] where
 M := ![![![-61629687750958469982, -2425590313035482867, 5304224586854857430]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-61629687750958469982, -2425590313035482867, 5304224586854857430]] ![![954094467346180109723087324460787975895, 108681452759936397257002697713518718869, 103230484524320012740092888817220541610]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 1], [2, 2, 2], [0, 1]]
 g := ![![[1]], ![[0, 1, 1, 1]], ![[2, 2, 2, 2]]]
 h' := ![![[2, 0, 1], [0, 1]], ![[2, 2, 2], [2, 0, 1]], ![[0, 1], [2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5430087, -398166, -206550]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1810029, -132722, -68850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2076852628612038961749238973660947, 236575484473437697958939400588158, 224709932270719601534012319490532]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2076852628612038961749238973660947, 236575484473437697958939400588158, 224709932270719601534012319490532]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![2076852628612038961749238973660947, 236575484473437697958939400588158, 224709932270719601534012319490532], ![26018889934592601392245720736511208, 2963826805492199271460361170525449, 2815174709275816182657418644862644], ![36029195834016990207229146933257048, 4104106541886543309736857156317706, 3898263191183231966871191691780455]]]
  hmulB := by decide  
  f := ![![![-80266278496875369, 13883941842107702, -5399607697579116]], ![![-188857505313710167, -15899286660111109, 22368275986636288]], ![![232284249069546564, 10952115302088162, -21298894357690225]]]
  g := ![![![93657289221769492347274298786869, 236575484473437697958939400588158, 224709932270719601534012319490532], ![1173342136202547769446992529096857, 2963826805492199271460361170525449, 2815174709275816182657418644862644], ![1624764688724886482106761739436422, 4104106541886543309736857156317706, 3898263191183231966871191691780455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1276914571804509644833685, -145454077624048226556850, -138158761480079239749978]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-1276914571804509644833685, -145454077624048226556850, -138158761480079239749978]] 
 ![![5, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![-1276914571804509644833685, -145454077624048226556850, -138158761480079239749978], ![-15997235067113315863769960, -1822254301580857617026725, -1730858299200640745068456], ![-22151887205208481338321252, -2523334287361271249533964, -2396775295933081536447253]]]
  hmulB := by decide  
  f := ![![![-3416376796841, -162548419742, 314318438450]], ![![5623855180489, -433976288815, -10778401034]], ![![-1763796692348, 654679520228, -371112601125]]]
  g := ![![![-168110467786472993032627, -145454077624048226556850, -138158761480079239749978], ![-2106094432474148602537957, -1822254301580857617026725, -1730858299200640745068456], ![-2916376868624933517943872, -2523334287361271249533964, -2396775295933081536447253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2076852628612038961749238973660947, 236575484473437697958939400588158, 224709932270719601534012319490532]] ![![-1276914571804509644833685, -145454077624048226556850, -138158761480079239749978]]
  ![![-11414266094754029318870158903454305116705880069009395119439, -1300205654495477130221835621209304698190636826572235288348, -1234993242051204931384265462073905979849286789618246561810]] where
 M := ![![![-11414266094754029318870158903454305116705880069009395119439, -1300205654495477130221835621209304698190636826572235288348, -1234993242051204931384265462073905979849286789618246561810]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-11414266094754029318870158903454305116705880069009395119439, -1300205654495477130221835621209304698190636826572235288348, -1234993242051204931384265462073905979849286789618246561810]] ![![-1276914571804509644833685, -145454077624048226556850, -138158761480079239749978]]
  ![![5, 0, 0]] where
 M := ![![![62732169190512668245737813585304391892869318585253322750609349248246560133060514915, 7145857685739295098942464319696445890163074764366427117832364762117889680091022290, 6787453907799007455914689855313365890759074026408975397310234693473902207635980960]]]
 hmul := by decide  
 g := ![![![![12546433838102533649147562717060878378573863717050664550121869849649312026612102983, 1429171537147859019788492863939289178032614952873285423566472952423577936018204458, 1357490781559801491182937971062673178151814805281795079462046938694780441527196192]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-5, -1, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 6, 1]] where
  M :=![![![-5, -1, 1], ![124, 1, -8], ![-86, 8, -1]]]
  hmulB := by decide  
  f := ![![![-9, -1, -1]], ![![-116, -13, -12]], ![![-124, -14, -13]]]
  g := ![![![-1, -1, 1], ![20, 7, -8], ![-12, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]], ![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]], ![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![681, 5683, 2290]
  a := ![9, 3, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-557, -1151, 2290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -1, -1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-9, -1, -1]] 
 ![![7, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-9, -1, -1], ![-116, -13, -12], ![-154, -18, -17]]]
  hmulB := by decide  
  f := ![![![-5, -1, 1]], ![![17, 0, -1]], ![![-13, 1, 0]]]
  g := ![![![-1, -1, -1], ![-13, -13, -12], ![-17, -18, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-5, -1, 1]] ![![-9, -1, -1]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-253537201508851, -45742312991578, 47648124548628]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-253537201508851, -45742312991578, 47648124548628]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 5, 1]] where
  M :=![![![-253537201508851, -45742312991578, 47648124548628], ![5900744197801672, 30445734225867, -362126880818524], ![-3869041324336008, 390714054174274, -59133080200239]]]
  hmulB := by decide  
  f := ![![![-12698882880577845055277279033, -1446537095774525369467182630, -1373985362608750119580130036]], ![![-159092095129951912871746873800, -18122272597847070283710746583, -17213341682962753933832086372]], ![![-100422964512313184377041969005, -11439237986585764309700146813, -10865497745532219728901251511]]]
  g := ![![![-53370370304477, -25816630521338, 47648124548628], ![766875669411940, 167370921665317, -362126880818524], ![-314100887539485, 62398132288679, -59133080200239]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[7, 9], [1, 4], [1]], ![[0, 2], [4, 7], [1]]]
 h' := ![![[9, 10], [6, 3], [6, 9], [0, 1]], ![[0, 1], [0, 8], [10, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4099, 2788, 1090]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-321, -242, 1090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12698882880577845055277279033, 1446537095774525369467182630, 1373985362608750119580130036]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![12698882880577845055277279033, 1446537095774525369467182630, 1373985362608750119580130036]] 
 ![![11, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![12698882880577845055277279033, 1446537095774525369467182630, 1373985362608750119580130036], ![159092095129951912871746873800, 18122272597847070283710746583, 17213341682962753933832086372], ![220299953821640548401786336824, 25094495192786378401877603618, 23835869247779396511692424509]]]
  hmulB := by decide  
  f := ![![![253537201508851, 45742312991578, -47648124548628]], ![![-467284781206829, 9707382249897, 19925682470240]], ![![582219394493138, 6064461431046, -37940742298731]]]
  g := ![![![-489143821166657477175051747, 1446537095774525369467182630, 1373985362608750119580130036], ![-6128012681201530665246020879, 18122272597847070283710746583, 17213341682962753933832086372], ![-8485656748592050174615519920, 25094495192786378401877603618, 23835869247779396511692424509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-253537201508851, -45742312991578, 47648124548628]] ![![12698882880577845055277279033, 1446537095774525369467182630, 1373985362608750119580130036]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1790797347205510170942398790259, 203990761873182027062092734585, 193759511415148015310140640009]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1790797347205510170942398790259, 203990761873182027062092734585, 193759511415148015310140640009]] 
 ![![13, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![1790797347205510170942398790259, 203990761873182027062092734585, 193759511415148015310140640009], ![22435178322325033728968505862740, 2555604142408068220431009255719, 2427426641562116301241208625868], ![31066714812896875767995909910506, 3538827457762834334342291993042, 3361335939442762316927428099483]]]
  hmulB := by decide  
  f := ![![![-486225318517179, 699133160097823, -476859114216691]], ![![-4803904072229239, -5691403785334, 281024446266261]], ![![4907151290787218, 222274045881132, -443383584411939]]]
  g := ![![![-59940965652429545142245384826, 203990761873182027062092734585, 193759511415148015310140640009], ![-750942732477864444855093032523, 2555604142408068220431009255719, 2427426641562116301241208625868], ![-1039854614727645726087305757736, 3538827457762834334342291993042, 3361335939442762316927428099483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1454881, 12336, 74956]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1454881, 12336, 74956]] 
 ![![13, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![-1454881, 12336, 74956], ![8945376, -1092437, 273272], ![4028824, 1036108, -980473]]]
  hmulB := by decide  
  f := ![![![-787965677325, -89757626176, -85255791164]], ![![-1304873502377, -148638895581, -141183843428]], ![![-1536410573792, -175013417340, -166235538921]]]
  g := ![![![-166581, 12336, 74956], ![1276241, -1092437, 273272], ![195972, 1036108, -980473]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-980379549, -354584207, 312579591]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-980379549, -354584207, 312579591]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![-980379549, -354584207, 312579591], ![38927887748, 937102613, -2920682888], ![-31922398746, 2290613648, 185929583]]]
  hmulB := by decide  
  f := ![![![-6864391182796155803, -781926770976753649, -742708874243378533]], ![![-12423512372004317169, -1415169481829275766, -1344191005763958263]], ![![-15496616033464552126, -1765228497828364074, -1676692650856190515]]]
  g := ![![![-63916028, -354584207, 312579591], ![4897534897, 937102613, -2920682888], ![-4565407990, 2290613648, 185929583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1790797347205510170942398790259, 203990761873182027062092734585, 193759511415148015310140640009]] ![![-1454881, 12336, 74956]]
  ![![-6864391182796155803, -781926770976753649, -742708874243378533]] where
 M := ![![![-6864391182796155803, -781926770976753649, -742708874243378533]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-6864391182796155803, -781926770976753649, -742708874243378533]] ![![-980379549, -354584207, 312579591]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [11, 14, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 5, 9], [13, 11, 8], [0, 1]]
 g := ![![[7, 0, 4], [3, 4], [4, 1], []], ![[10, 16, 5, 13], [2, 9], [4, 2], [6, 13]], ![[11, 2, 13, 13], [2, 1], [6, 8], [7, 13]]]
 h' := ![![[8, 5, 9], [16, 13, 2], [7, 1, 2], [0, 0, 1], [0, 1]], ![[13, 11, 8], [14, 9, 3], [11, 0, 14], [15, 6, 11], [8, 5, 9]], ![[0, 1], [12, 12, 12], [0, 16, 1], [7, 11, 5], [13, 11, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 16], []]
 b := ![[], [16, 13, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [11, 14, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2155775695, 160926318, 108391626]
  a := ![-43, -1, 108]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![126810335, 9466254, 6375978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [15, 6, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 16], [1, 12, 3], [0, 1]]
 g := ![![[0, 2, 16], [11, 7, 6], [1, 1], []], ![[5, 9, 7, 16], [5, 7, 13, 11], [13, 11], [11, 9]], ![[8, 8, 8, 18], [16, 9, 5, 12], [16, 17], [5, 9]]]
 h' := ![![[0, 6, 16], [6, 16, 15], [4, 17, 14], [0, 0, 1], [0, 1]], ![[1, 12, 3], [1, 7, 18], [12, 5, 3], [6, 8, 12], [0, 6, 16]], ![[0, 1], [14, 15, 5], [11, 16, 2], [2, 11, 6], [1, 12, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 16], []]
 b := ![[], [15, 4, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [15, 6, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33858, 3591, 3382]
  a := ![-1, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1782, 189, 178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9501093, -1082275, -1027993]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-9501093, -1082275, -1027993]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 7, 1]] where
  M :=![![![-9501093, -1082275, -1027993], ![-119030060, -13558783, -12878736], ![-164824762, -18775284, -17833601]]]
  hmulB := by decide  
  f := ![![![-4633, -119, 353]], ![![42836, -2749, -484]], ![![12938, -663, -267]]]
  g := ![![![-413091, 265812, -1027993], ![-5175220, 3330103, -12878736], ![-7166294, 4611301, -17833601]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 22], [0, 1]]
 g := ![![[12, 4], [9, 12], [4, 6], [1]], ![[14, 19], [15, 11], [7, 17], [1]]]
 h' := ![![[12, 22], [9, 21], [4, 9], [1, 12], [0, 1]], ![[0, 1], [8, 2], [20, 14], [7, 11], [12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [15, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [22, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9246, 7639, 3365]
  a := ![-10, -2, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![402, -692, 3365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4633, 119, -353]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![4633, 119, -353]] 
 ![![23, 0, 0], ![20, 1, 0], ![3, 0, 1]] where
  M :=![![![4633, 119, -353], ![-42836, 2749, 484], ![2278, -3994, 2753]]]
  hmulB := by decide  
  f := ![![![9501093, 1082275, 1027993]], ![![13437040, 1530621, 1453852]], ![![8405567, 957483, 909460]]]
  g := ![![![144, 119, -353], ![-4316, 2749, 484], ![3213, -3994, 2753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-9501093, -1082275, -1027993]] ![![4633, 119, -353]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1633276315716161466951024297216475, 186047450043563705642406247579599, 176716154640796167321763866470251]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![1633276315716161466951024297216475, 186047450043563705642406247579599, 176716154640796167321763866470251]] 
 ![![29, 0, 0], ![0, 29, 0], ![7, 3, 1]] where
  M :=![![![1633276315716161466951024297216475, 186047450043563705642406247579599, 176716154640796167321763866470251], ![20461748756721285256042038986111724, 2330809638876578597917437381988131, 2213906809717229391067590208736492], ![28334043263014714366028721169540414, 3227547260548168703394961502011258, 3065668143648065882166419991197179]]]
  hmulB := by decide  
  f := ![![![43426743755836397, -4947171358022947, 1069381628946063]], ![![148114480905619348, 53720823258589659, -47332950322337344]], ![![6587209014797425, 3989599126061808, -3260844439686990]]]
  g := ![![![13664249421744423989609559721542, -11865552202718096424927081097626, 176716154640796167321763866470251], ![171186244437954466157548535343320, -148652096216383088802942525662805, 2213906809717229391067590208736492], ![237047112326836316926337283833109, -205843350703311342865665464537251, 3065668143648065882166419991197179]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [3, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 28], [0, 1]]
 g := ![![[5, 22], [16], [7, 13], [14, 1]], ![[23, 7], [16], [15, 16], [28, 28]]]
 h' := ![![[14, 28], [16, 15], [8, 25], [16, 19], [0, 1]], ![[0, 1], [23, 14], [10, 4], [21, 10], [14, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [13, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [3, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7753, 2925, 975]
  a := ![5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 0, 975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43426743755836397, -4947171358022947, 1069381628946063]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![43426743755836397, -4947171358022947, 1069381628946063]] 
 ![![29, 0, 0], ![26, 1, 0], ![10, 0, 1]] where
  M :=![![![43426743755836397, -4947171358022947, 1069381628946063], ![148114480905619348, 53720823258589659, -47332950322337344], ![-557301587578587498, -10833895613815916, 39948690813466881]]]
  hmulB := by decide  
  f := ![![![1633276315716161466951024297216475, 186047450043563705642406247579599, 176716154640796167321763866470251]], ![![2169894240184189082647195541853106, 247173908276180515331724131691645, 234776787254411370394256921964242]], ![![1540234704144011346053067729024316, 175449026240820888269621516476112, 166649299657104398461519263996541]]]
  g := ![![![5564116647412841, -4947171358022947, 1069381628946063], ![-26734393813597874, 53720823258589659, -47332950322337344], ![-23279558957035948, -10833895613815916, 39948690813466881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![1633276315716161466951024297216475, 186047450043563705642406247579599, 176716154640796167321763866470251]] ![![43426743755836397, -4947171358022947, 1069381628946063]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-817533556531683488560983348003367, -93125720402718443834734170157092, -88454957076105657668537003555130]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-817533556531683488560983348003367, -93125720402718443834734170157092, -88454957076105657668537003555130]] 
 ![![31, 0, 0], ![0, 31, 0], ![2, 10, 1]] where
  M :=![![![-817533556531683488560983348003367, -93125720402718443834734170157092, -88454957076105657668537003555130], ![-10242091967521805144885503745987232, -1166682621509493333068934195621925, -1108167118179395753684415708681180], ![-14182554988913805620898358539725460, -1615543044002965768864651897002150, -1534514739793754322241673709648331]]]
  hmulB := by decide  
  f := ![![![-6587209014797425, -3989599126061808, 3260844439686990]], ![![407259729266686032, 13706612309699333, -33374302381244100]], ![![119081925498684070, 4888061513886824, -10394279856834391]]]
  g := ![![![-20665278786434586233029333577197, 25529801624462520414536640819168, -88454957076105657668537003555130], ![-258895410682677859274731365439512, 319838340654337554960491061006125, -1108167118179395753684415708681180], ![-358500822881493450852097132917058, 442890463030147659792002748370360, -1534514739793754322241673709648331]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 30], [0, 1]]
 g := ![![[6, 18], [11, 2], [17, 20], [10, 1]], ![[0, 13], [0, 29], [0, 11], [20, 30]]]
 h' := ![![[10, 30], [8, 24], [18, 23], [27, 19], [0, 1]], ![[0, 1], [0, 7], [0, 8], [0, 12], [10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [3, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31417, 7882, 2704]
  a := ![10, -2, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![839, -618, 2704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6587209014797425, 3989599126061808, -3260844439686990]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![6587209014797425, 3989599126061808, -3260844439686990]] 
 ![![31, 0, 0], ![22, 1, 0], ![3, 0, 1]] where
  M :=![![![6587209014797425, 3989599126061808, -3260844439686990], ![-407259729266686032, -13706612309699333, 33374302381244100], ![367883184178059300, -22442982085621830, -4998659371200899]]]
  hmulB := by decide  
  f := ![![![817533556531683488560983348003367, 93125720402718443834734170157092, 88454957076105657668537003555130]], ![![910575168103833609458939916195526, 103724144205461261207518901260579, 98521812059797426528781606028840]], ![![536617924468027615696171244636631, 61126458232616809689317884112046, 58060632613615203072493055493991]]]
  g := ![![![-2303272207725851, 3989599126061808, -3260844439686990], ![-6639908567646226, -13706612309699333, 33374302381244100], ![28278218328236847, -22442982085621830, -4998659371200899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-817533556531683488560983348003367, -93125720402718443834734170157092, -88454957076105657668537003555130]] ![![6587209014797425, 3989599126061808, -3260844439686990]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB179I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB179I0 : PrimesBelowBoundCertificateInterval O 1 31 179 where
  m := 11
  g := ![3, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB179I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I13N2, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1, I13N2], [], [], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
