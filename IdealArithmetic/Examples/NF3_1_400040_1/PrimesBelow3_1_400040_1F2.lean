
import IdealArithmetic.Examples.NF3_1_400040_1.RI3_1_400040_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227570731756674298047934903005748766561761, -25922713713822666511141038198382173684701, -24622548088072824546617206330062164452503]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-227570731756674298047934903005748766561761, -25922713713822666511141038198382173684701, -24622548088072824546617206330062164452503]] 
 ![![83, 0, 0], ![0, 83, 0], ![78, 8, 1]] where
  M :=![![![-227570731756674298047934903005748766561761, -25922713713822666511141038198382173684701, -24622548088072824546617206330062164452503], ![-2851014915713448279549500606813931039561556, -324760758483215754269879896457677415139575, -308472233314372314204644794643946065752016], ![-3947892280653196015921909599027974433549222, -449706693714060051661728873282719006306044, -427151447712756578349920217382886100646181]]]
  hmulB := by decide  
  f := ![![![-468488745077550599137, -49031001692769470497, 62413669416216433723]], ![![7685764336717049928748, -107389396303698960025, -365482678095261837524]], ![![255208881141041867280, -49606151909863181844, 21112482623337303523]]]
  g := ![![![20397446013409711043231411936615663382331, 2060935795069396745322850752314640264281, -24622548088072824546617206330062164452503], ![255539991359127617209792691270046531193924, 25819483229298346498400945309564953143091, -308472233314372314204644794643946065752016], ![353854465553515868618938160925748691769312, 35753070939614368375152203202173130106788, -427151447712756578349920217382886100646181]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [74, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 82], [0, 1]]
 g := ![![[30, 30], [34, 38], [41], [63], [11, 26], [1]], ![[79, 53], [2, 45], [41], [63], [59, 57], [1]]]
 h' := ![![[21, 82], [57, 69], [3, 11], [76, 37], [16, 48], [9, 21], [0, 1]], ![[0, 1], [12, 14], [68, 72], [23, 46], [28, 35], [35, 62], [21, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [82, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [74, 62, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4528, 2848, 190]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-124, 16, 190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1063167073373619945553979619589526445242223, 121105976415698498539851085506746718944513, 115031850483250244701139535947516316870539]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![1063167073373619945553979619589526445242223, 121105976415698498539851085506746718944513, 115031850483250244701139535947516316870539]] 
 ![![83, 0, 0], ![1, 1, 0], ![66, 0, 1]] where
  M :=![![![1063167073373619945553979619589526445242223, 121105976415698498539851085506746718944513, 115031850483250244701139535947516316870539], ![13319398152327235369977339971674971148686628, 1517220349374172670519826213820361310650405, 1441123465123485474800789926962499823186208], ![18443800086314328144620874483025161046939886, 2100943938360745673814069394851445714039572, 1995570129104518410840519006288117784354483]]]
  hmulB := by decide  
  f := ![![![-13130323242729829107361, 875037438420247167529, 124960977842145958409]], ![![-19700670546425334559, -150668895825531317052, 109942859249745898199]], ![![-9124676724856699980680, 768098202888981281372, -28711541701865370685]]]
  g := ![![![-80120976324537285581458805282569845628408, 121105976415698498539851085506746718944513, 115031850483250244701139535947516316870539], ![-1003758685484300947438489414718920222798235, 1517220349374172670519826213820361310650405, 1441123465123485474800789926962499823186208], ![-1389937016541501598128523485865566969090308, 2100943938360745673814069394851445714039572, 1995570129104518410840519006288117784354483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-227570731756674298047934903005748766561761, -25922713713822666511141038198382173684701, -24622548088072824546617206330062164452503]] ![![1063167073373619945553979619589526445242223, 121105976415698498539851085506746718944513, 115031850483250244701139535947516316870539]]
  ![![83, 0, 0]] where
 M := ![![![-1041354008562510292879247705516052905421630688515205157660115197520892898208804547589, -118621237583272298642444907706961001776707041088482690156017255051156968689510970014, -112671734869463523768183851598201873786600628838388991595349895911666776646757283936]]]
 hmul := by decide  
 g := ![![![![-12546433838102533649147562717060878378573863717050664550121869849649312026612102983, -1429171537147859019788492863939289178032614952873285423566472952423577936018204458, -1357490781559801491182937971062673178151814805281795079462046938694780441527196192]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 42, 40]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![367, 42, 40]] 
 ![![89, 0, 0], ![0, 89, 0], ![47, 50, 1]] where
  M :=![![![367, 42, 40], ![4632, 525, 500], ![6400, 730, 691]]]
  hmulB := by decide  
  f := ![![![-25, 2, 0]], ![![-8, -27, 20]], ![![-15, -14, 11]]]
  g := ![![![-17, -22, 40], ![-212, -275, 500], ![-293, -380, 691]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [68, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 88], [0, 1]]
 g := ![![[28, 72], [17], [44], [26, 16], [66, 68], [1]], ![[0, 17], [17], [44], [0, 73], [0, 21], [1]]]
 h' := ![![[54, 88], [1, 28], [0, 27], [12, 69], [51, 4], [21, 54], [0, 1]], ![[0, 1], [0, 61], [34, 62], [0, 20], [0, 85], [0, 35], [54, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [39, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [68, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2578, 3175, 1977]
  a := ![-7, -3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1073, -1075, 1977]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 2, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-25, 2, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![25, 0, 1]] where
  M :=![![![-25, 2, 0], ![-8, -27, 20], ![240, 10, -21]]]
  hmulB := by decide  
  f := ![![![367, 42, 40]], ![![184, 21, 20]], ![![175, 20, 19]]]
  g := ![![![-1, 2, 0], ![4, -27, 20], ![5, 10, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![367, 42, 40]] ![![-25, 2, 0]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-462563674284246083, -52690895750625244, -50048159646634646]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-462563674284246083, -52690895750625244, -50048159646634646]] 
 ![![97, 0, 0], ![53, 1, 0], ![15, 0, 1]] where
  M :=![![![-462563674284246083, -52690895750625244, -50048159646634646], ![-5795015574593656544, -660113576766794069, -627005276799521732], ![-8024544918060607244, -914080554159376618, -868234423665304447]]]
  hmulB := by decide  
  f := ![![![2624737533, 902552840, -803088034]], ![![403405297, 469505619, -362312510]], ![![1240952687, 78463014, -128195933]]]
  g := ![![![31760579331942387, -52690895750625244, -50048159646634646], ![397897764392157269, -660113576766794069, -627005276799521732], ![550981863993463095, -914080554159376618, -868234423665304447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34184121, 3893933, 3698631]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![34184121, 3893933, 3698631]] 
 ![![97, 0, 0], ![63, 1, 0], ![94, 0, 1]] where
  M :=![![![34184121, 3893933, 3698631], ![428259988, 48783343, 46336592], ![593025414, 67551868, 64163773]]]
  hmulB := by decide  
  f := ![![![79283, 3499, -7097]], ![![42569, 2688, -4395]], ![![78672, 2620, -6427]]]
  g := ![![![-5760876, 3893933, 3698631], ![-72172477, 48783343, 46336592], ![-99939556, 67551868, 64163773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7387651872837, 1088655809043, -360334200091]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-7387651872837, 1088655809043, -360334200091]] 
 ![![97, 0, 0], ![77, 1, 0], ![74, 0, 1]] where
  M :=![![![-7387651872837, 1088655809043, -360334200091], ![-47594727247092, -10277978682335, 10165889690248], ![118387334282066, 758934444032, -7372345455297]]]
  hmulB := by decide  
  f := ![![![-68057565588192879133878559, -7752476670369061196043859, -7363647638327296690220179]], ![![-62815055259883000529390671, -7155299285854412510147554, -6796421960119041757606523]], ![![-64091969831687510174224356, -7300753363478460736704404, -6934580721599120997356501]]]
  g := ![![![-665457921262, 1088655809043, -360334200091], ![-87280472017, -10277978682335, 10165889690248], ![6242298410140, 758934444032, -7372345455297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-462563674284246083, -52690895750625244, -50048159646634646]] ![![34184121, 3893933, 3698631]]
  ![![-68057565588192879133878559, -7752476670369061196043859, -7363647638327296690220179]] where
 M := ![![![-68057565588192879133878559, -7752476670369061196043859, -7363647638327296690220179]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-68057565588192879133878559, -7752476670369061196043859, -7363647638327296690220179]] ![![-7387651872837, 1088655809043, -360334200091]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [90, 6, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 89, 50], [85, 11, 51], [0, 1]]
 g := ![![[98, 61, 56], [72, 96], [32, 63, 68], [29, 4], [99, 78], [1]], ![[64, 83, 30, 40], [45, 9], [65, 99, 0, 11], [35, 17], [65, 52], [38, 65, 35, 63]], ![[57, 68, 81, 29], [81, 31], [44, 92, 52, 99], [35, 47], [42, 37], [49, 52, 40, 38]]]
 h' := ![![[68, 89, 50], [62, 42, 37], [49, 93, 55], [20, 49, 13], [99, 31, 2], [11, 95, 52], [0, 1]], ![[85, 11, 51], [58, 46, 83], [88, 81, 3], [76, 42, 68], [87, 59, 57], [33, 67, 70], [68, 89, 50]], ![[0, 1], [46, 13, 82], [93, 28, 43], [37, 10, 20], [37, 11, 42], [79, 40, 80], [85, 11, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 3], []]
 b := ![[], [69, 36, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [90, 6, 49, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13094053292, -963275986, -663982080]
  a := ![66, 1, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129644092, -9537386, -6574080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-878664201125898500507230688250151100319123, -100089147495142867420179116237227732312522, -95069130280880279246936134801754728363684]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-878664201125898500507230688250151100319123, -100089147495142867420179116237227732312522, -95069130280880279246936134801754728363684]] 
 ![![103, 0, 0], ![0, 103, 0], ![81, 66, 1]] where
  M :=![![![-878664201125898500507230688250151100319123, -100089147495142867420179116237227732312522, -95069130280880279246936134801754728363684], ![-11007939043725062039951619711261656474391992, -1253920705035157029321732246021697009825021, -1191029735513189232695663431975786779852588], ![-15243048128967073584817322531726988641867896, -1736344431127157967311065333608950130290502, -1649257277801465910829205729535134935126271]]]
  hmulB := by decide  
  f := ![![![1172485700749717730995, -102213044349855557902, 6228003040650334276]], ![![1156212542277462344728, 1305838760302824960277, -1009674437417254910468]], ![![1545898605169311605629, 752194178693469162566, -632316669834487751395]]]
  g := ![![![66232382054615573965966953696038659195527, 59946344184883063717258308550277517861074, -95069130280880279246936134801754728363684], ![829761840124691901052399206590068666928812, 751010114940148857559146157906604179227629, -1191029735513189232695663431975786779852588], ![1148997974494676361090760597675912049547185, 1039947921395821282984626338016601510563528, -1649257277801465910829205729535134935126271]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [4, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 102], [0, 1]]
 g := ![![[94, 26], [56, 1], [54, 56], [26], [46], [36, 1]], ![[0, 77], [92, 102], [10, 47], [26], [46], [72, 102]]]
 h' := ![![[36, 102], [85, 52], [93, 102], [37, 57], [55, 51], [62, 56], [0, 1]], ![[0, 1], [0, 51], [57, 1], [29, 46], [37, 52], [18, 47], [36, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [57, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [4, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1268, 5878, 860]
  a := ![9, 3, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-664, -494, 860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![341707195187753413470987376177432810228843, 38924064296091816213069429471862233051824, 36971809953782355865003581417261111506412]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![341707195187753413470987376177432810228843, 38924064296091816213069429471862233051824, 36971809953782355865003581417261111506412]] 
 ![![103, 0, 0], ![59, 1, 0], ![90, 0, 1]] where
  M :=![![![341707195187753413470987376177432810228843, 38924064296091816213069429471862233051824, 36971809953782355865003581417261111506412], ![4280920937269515438948152052183884448562144, 487642180660573376582935853791876134709079, 463184262868482873860701457553144553531064], ![5927929253959618044978453304810345757436888, 675253850879629707310393705783705614842476, 641386183502631181087147723624723945370963]]]
  hmulB := by decide  
  f := ![![![4572638615682806398613, 695436245289160169600, -765800485208957253812]], ![![1700076457466544333809, 398824644819507863751, -386014244124803794044]], ![![4552937945136381064054, 544767349463628852548, -655857625959211355613]]]
  g := ![![![-51284228098272580300489624176853776460251, 38924064296091816213069429471862233051824, 36971809953782355865003581417261111506412], ![-642490790095803615795225189333202109874459, 487642180660573376582935853791876134709079, 463184262868482873860701457553144553531064], ![-889677713234712048390078354006344083511222, 675253850879629707310393705783705614842476, 641386183502631181087147723624723945370963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-878664201125898500507230688250151100319123, -100089147495142867420179116237227732312522, -95069130280880279246936134801754728363684]] ![![341707195187753413470987376177432810228843, 38924064296091816213069429471862233051824, 36971809953782355865003581417261111506412]]
  ![![103, 0, 0]] where
 M := ![![![-1292282685324560965862198959857270472993107962856218448662552594513879138741046607249, -147204668326229479038214764985746785337359340145948398627346714099628527409875059174, -139821550500659553591842611019455337349636924944024893184590834685562385477301207776]]]
 hmul := by decide  
 g := ![![![![-12546433838102533649147562717060878378573863717050664550121869849649312026612102983, -1429171537147859019788492863939289178032614952873285423566472952423577936018204458, -1357490781559801491182937971062673178151814805281795079462046938694780441527196192]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [20, 85, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 50, 19], [105, 56, 88], [0, 1]]
 g := ![![[50, 67, 35], [14, 41, 16], [105, 53], [35, 44, 90], [62, 23], [1]], ![[91, 40, 105, 105], [86, 96, 2, 36], [45, 16], [97, 22, 24, 10], [5, 27], [101, 106, 7, 11]], ![[80, 78, 3, 43], [37, 47, 76, 2], [24, 86], [91, 6, 1, 45], [49, 89], [56, 22, 87, 96]]]
 h' := ![![[70, 50, 19], [41, 102, 28], [87, 43, 4], [49, 39, 69], [16, 24, 25], [87, 22, 68], [0, 1]], ![[105, 56, 88], [98, 51, 82], [98, 53, 78], [79, 97, 4], [99, 51, 37], [78, 12, 53], [70, 50, 19]], ![[0, 1], [22, 61, 104], [58, 11, 25], [18, 78, 34], [30, 32, 45], [49, 73, 93], [105, 56, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 71], []]
 b := ![[], [43, 96, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [20, 85, 39, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5278524, -294999, -166385]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49332, -2757, -1555]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32385757743449146779, -190850269691018836, 2004656406789979250]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-32385757743449146779, -190850269691018836, 2004656406789979250]] 
 ![![109, 0, 0], ![0, 109, 0], ![34, 80, 1]] where
  M :=![![![-32385757743449146779, -190850269691018836, 2004656406789979250], ![241322169893561585344, -22171625439808231693, 2100810116669770140], ![45256285467937034180, 25106281939814636070, -20739519842091308951]]]
  hmulB := by decide  
  f := ![![![-3734727840818285661856485791636695727, -425425009047702713128864016748304096, -404087622105717584717981339047082690]], ![![-46788814616495299313642304618656706416, -5329740942299170872317528470123805081, -5062425334688462300724602845577206340]], ![![-36099778863713434688535595724271389642, -4112146695634572515584970015327526066, -3905900087323113564539465092047643291]]]
  g := ![![![-922422711690903131, -1473058374430177604, 2004656406789979250], ![1558666292906324776, -1745288392416420577, 2100810116669770140], ![6884403303660931546, 15451998800982746350, -20739519842091308951]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [107, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 108], [0, 1]]
 g := ![![[16, 84], [88], [18, 60], [24, 61], [63], [32, 1]], ![[88, 25], [88], [85, 49], [14, 48], [63], [64, 108]]]
 h' := ![![[32, 108], [55, 53], [36, 57], [48, 96], [80, 37], [64, 45], [0, 1]], ![[0, 1], [7, 56], [7, 52], [68, 13], [65, 72], [87, 64], [32, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [22, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [107, 77, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![369297, 150560, 68590]
  a := ![-43, -1, 108]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18007, -48960, 68590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471819468505020614394839, 1044734176392486948750, -27951840268125359744878]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![471819468505020614394839, 1044734176392486948750, -27951840268125359744878]] 
 ![![109, 0, 0], ![70, 1, 0], ![18, 0, 1]] where
  M :=![![![471819468505020614394839, 1044734176392486948750, -27951840268125359744878], ![-3358399768880613117180360, 331015532988001328721699, -45456338772325850002256], ![-824994467949163797475852, -358150252603667241939664, 306197895249053429823071]]]
  hmulB := by decide  
  f := ![![![-85076060281923244467373762041755043475952635645, -9691063246860322654609832593315238791764429742, -9205003513699870205555019099069817562446327722]], ![![-64414315489827249970314920224201561427919138558, -7337471943887934483148874371338124843302109417, -6969457664724714507762015606111736260676879756]], ![![-27589603616180300054630993369888011327541781222, -3142747709687025080075609155359248812131964628, -2985121753251750226696457666110652684020122573]]]
  g := ![![![8273588999851403700827, 1044734176392486948750, -27951840268125359744878], ![-235883238349897622272098, 331015532988001328721699, -45456338772325850002256], ![171871202750684233041150, -358150252603667241939664, 306197895249053429823071]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-32385757743449146779, -190850269691018836, 2004656406789979250]] ![![471819468505020614394839, 1044734176392486948750, -27951840268125359744878]]
  ![![109, 0, 0]] where
 M := ![![![-16293109949765993250145328628020313457883621, -814977110161016330245781518575481723470614, 1527738454377581156183269199320499015218728]]]
 hmul := by decide  
 g := ![![![![-149478072933632965597663565394681774842969, -7476854221660700277484234115371391958446, 14015949122730102350305222012114669864392]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 6, -2]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-39, 6, -2]] 
 ![![113, 0, 0], ![0, 113, 0], ![76, 110, 1]] where
  M :=![![![-39, 6, -2], ![-264, -55, 56], ![652, 4, -39]]]
  hmulB := by decide  
  f := ![![![17, 2, 2]], ![![232, 25, 24]], ![![240, 26, 25]]]
  g := ![![![1, 2, -2], ![-40, -55, 56], ![32, 38, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [67, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 112], [0, 1]]
 g := ![![[69, 105], [60], [51], [53], [5, 72], [10, 1]], ![[102, 8], [60], [51], [53], [47, 41], [20, 112]]]
 h' := ![![[10, 112], [109, 52], [93, 25], [81, 27], [4, 36], [8, 33], [0, 1]], ![[0, 1], [64, 61], [4, 88], [12, 86], [25, 77], [112, 80], [10, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [82, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [67, 103, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![577, 172, 244]
  a := ![-1, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-159, -236, 244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 2, 2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![17, 2, 2]] 
 ![![113, 0, 0], ![28, 1, 0], ![37, 0, 1]] where
  M :=![![![17, 2, 2], ![232, 25, 24], ![308, 36, 33]]]
  hmulB := by decide  
  f := ![![![-39, 6, -2]], ![![-12, 1, 0]], ![![-7, 2, -1]]]
  g := ![![![-1, 2, 2], ![-12, 25, 24], ![-17, 36, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-39, 6, -2]] ![![17, 2, 2]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8383186331354292730175528727, -954933605037085974802167855, -907038470991742687321310839]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-8383186331354292730175528727, -954933605037085974802167855, -907038470991742687321310839]] 
 ![![127, 0, 0], ![0, 127, 0], ![113, 40, 1]] where
  M :=![![![-8383186331354292730175528727, -954933605037085974802167855, -907038470991742687321310839], ![-105024882098860778579348629260, -11963445081275920191979915067, -11363412992354345122664300228], ![-145431340618169568345184711126, -16566168148078084809187880182, -15735284367378920803707729471]]]
  hmulB := by decide  
  f := ![![![-67598663413843, 12625407578441, -5220949954801]], ![![-677015624889884, -106328820766289, 115812175874808]], ![![-262848325593779, -22293126659905, 31250757024520]]]
  g := ![![![741040636934745125489233040, 278162245941989145811419415, -907038470991742687321310839], ![9283785716828190710879663752, 3484827359156676257595213339, -11363412992354345122664300228], ![12855557424375184901368415111, 4825552807457312971174183454, -15735284367378920803707729471]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [94, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 126], [0, 1]]
 g := ![![[66, 50], [73, 84], [74, 4], [102, 76], [82, 42], [19, 1]], ![[0, 77], [18, 43], [23, 123], [22, 51], [118, 85], [38, 126]]]
 h' := ![![[19, 126], [123, 47], [29, 46], [64, 125], [39, 87], [119, 13], [0, 1]], ![[0, 1], [0, 80], [14, 81], [26, 2], [41, 40], [112, 114], [19, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [58, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [94, 108, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8348, 7445, 5790]
  a := ![-10, -2, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5086, -1765, 5790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67598663413843, -12625407578441, 5220949954801]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![67598663413843, -12625407578441, 5220949954801]] 
 ![![127, 0, 0], ![106, 1, 0], ![55, 0, 1]] where
  M :=![![![67598663413843, -12625407578441, 5220949954801], ![677015624889884, 106328820766289, -115812175874808], ![-1337536610949686, 4745311520208, 73673547985767]]]
  hmulB := by decide  
  f := ![![![8383186331354292730175528727, 954933605037085974802167855, 907038470991742687321310839]], ![![7823957741908785889590194286, 891231552875645933236296911, 846531424547079291171049206]], ![![4775642431831934397675895993, 543996192323762310419741041, 516711813164761957530549808]]]
  g := ![![![8808973379642, -12625407578441, 5220949954801], ![-33261178765530, 106328820766289, -115812175874808], ![-46398305285897, 4745311520208, 73673547985767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-8383186331354292730175528727, -954933605037085974802167855, -907038470991742687321310839]] ![![67598663413843, -12625407578441, 5220949954801]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [31, 59, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 118, 77], [106, 12, 54], [0, 1]]
 g := ![![[97, 50, 107], [54, 41, 49], [128, 49], [106, 11], [77, 28], [112, 1], []], ![[98, 92, 55, 55], [117, 71, 101, 11], [100, 84], [49, 11], [18, 20], [12, 13], [103, 34]], ![[33, 23, 103, 82], [82, 16, 87, 79], [54, 60], [48, 44], [130, 60], [28, 38], [126, 34]]]
 h' := ![![[6, 118, 77], [29, 35, 99], [118, 32, 7], [5, 85, 7], [4, 49, 50], [65, 42, 40], [0, 0, 1], [0, 1]], ![[106, 12, 54], [0, 73, 84], [88, 58, 59], [31, 24, 79], [41, 110, 50], [59, 104, 46], [118, 49, 12], [6, 118, 77]], ![[0, 1], [1, 23, 79], [62, 41, 65], [65, 22, 45], [51, 103, 31], [85, 116, 45], [125, 82, 118], [106, 12, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 100], []]
 b := ![[], [65, 38, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [31, 59, 19, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5692474, -383175, -282960]
  a := ![5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43454, -2925, -2160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀


def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1641650031641, -70070826942, -44028183614]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1641650031641, -70070826942, -44028183614]] 
 ![![137, 0, 0], ![4, 1, 0], ![108, 0, 1]] where
  M :=![![![1641650031641, -70070826942, -44028183614], ![-5003098725912, 1491579940513, -788764636648], ![-9905457475916, -922720521692, 1237339276073]]]
  hmulB := by decide  
  f := ![![![1117781126779320442077033, 127327094835711990313654, 120940945848397080324398]], ![![134852041091840025153148, 15361074018455779668905, 14590632287937973613744]], ![![1022712446943777717613048, 116497766514340269705548, 110654767468379646567049]]]
  g := ![![![48737059633, -70070826942, -44028183614], ![541731111460, 1491579940513, -788764636648], ![-1020782607336, -922720521692, 1237339276073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-692719755633137, 265967875906227, -152140837925335]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-692719755633137, 265967875906227, -152140837925335]] 
 ![![137, 0, 0], ![66, 1, 0], ![9, 0, 1]] where
  M :=![![![-692719755633137, 265967875906227, -152140837925335], ![-19320772054665108, -1719391821166039, 2355397083211600], ![26743356619285850, -647991513498220, -1073629031372693]]]
  hmulB := by decide  
  f := ![![![-3372266296348202555632526925027, -384136804817580322404171863011, -364870246743342939604278935135]], ![![-1932974145612497811201777823474, -220186203235092249707482428441, -209142662968781920563012308170]], ![![-648557676164358552085685034169, -73877580110288925025649870357, -70172216110463556894197479402]]]
  g := ![![![-123192204555592, 265967875906227, -152140837925335], ![532558499221818, -1719391821166039, 2355397083211600], ![577908451040311, -647991513498220, -1073629031372693]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1641650031641, -70070826942, -44028183614]] ![![-692719755633137, 265967875906227, -152140837925335]]
  ![![-960842349413816294956409981, 585635267979976237137718325, -367536696664828158842799433]] where
 M := ![![![-960842349413816294956409981, 585635267979976237137718325, -367536696664828158842799433]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-960842349413816294956409981, 585635267979976237137718325, -367536696664828158842799433]] ![![-692719755633137, 265967875906227, -152140837925335]]
  ![![137, 0, 0]] where
 M := ![![![-20478495991907716286879908459071403153486753, -1024329028367515938015340073805880698307102, 1920185029814024021991815415659709771421704]]]
 hmul := by decide  
 g := ![![![![-149478072933632965597663565394681774842969, -7476854221660700277484234115371391958446, 14015949122730102350305222012114669864392]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB179I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB179I2 : PrimesBelowBoundCertificateInterval O 79 137 179 where
  m := 11
  g := ![2, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB179I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I103N1, I109N1, I113N1, I127N1, I137N0, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [], [I103N1], [], [I109N1], [I113N1], [I127N1], [], [I137N0, I137N1, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
