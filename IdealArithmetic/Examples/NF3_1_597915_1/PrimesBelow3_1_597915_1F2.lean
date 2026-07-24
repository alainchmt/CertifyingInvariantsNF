
import IdealArithmetic.Examples.NF3_1_597915_1.RI3_1_597915_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9298782672, 1270141, 394344187]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-9298782672, 1270141, 394344187]] 
 ![![83, 0, 0], ![13, 1, 0], ![78, 0, 1]] where
  M :=![![![-9298782672, 1270141, 394344187], ![67435396259, -2591121070, -1172871433], ![-48681485077, 5936755202, -1810053542]]]
  hmulB := by decide  
  f := ![![![11653118451644274406, 2343423926766600196, 1020303819672938037]], ![![3983726998662423759, 801121279690961737, 348800356757375686]], ![![14254832012842141212, 2866624461902663725, 1248100206983367029]]]
  g := ![![![-482820977, 1270141, 394344187], ![2320529421, -2591121070, -1172871433], ![184637031, 5936755202, -1810053542]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![939224604900672547111505274, 188876601646624273746873313, 82235021971800632946042523]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![939224604900672547111505274, 188876601646624273746873313, 82235021971800632946042523]] 
 ![![83, 0, 0], ![72, 1, 0], ![10, 0, 1]] where
  M :=![![![939224604900672547111505274, 188876601646624273746873313, 82235021971800632946042523], ![14439941960471156781267018059, 2903849783361156128434848104, 1264307747257592291136858935], ![22100756157069472325406063671, 4444427557569622147887484166, 1935060217425011751845693272]]]
  hmulB := by decide  
  f := ![![![531147106633078, 29497684740682, -41845232824737]], ![![375253641373891, 24483186797153, -31943850445559]], ![![187281735268130, 2033240911173, -9287442162727]]]
  g := ![![![-162436637751497367374985524, 188876601646624273746873313, 82235021971800632946042523], ![-2497353251977204908161573913, 2903849783361156128434848104, 1264307747257592291136858935], ![-3822272652556547467963249747, 4444427557569622147887484166, 1935060217425011751845693272]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88770, 1115, -4501]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![88770, 1115, -4501]] 
 ![![83, 0, 0], ![81, 1, 0], ![42, 0, 1]] where
  M :=![![![88770, 1115, -4501], ![-767441, 15598, 22423], ![748789, -48560, -94]]]
  hmulB := by decide  
  f := ![![![-1087394668, -218673370, -95208243]], ![![-1262613547, -253909613, -110549758]], ![![-858528918, -172648825, -75169607]]]
  g := ![![![2259, 1115, -4501], ![-35815, 15598, 22423], ![56459, -48560, -94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-9298782672, 1270141, 394344187]] ![![939224604900672547111505274, 188876601646624273746873313, 82235021971800632946042523]]
  ![![1087394668, 218673370, 95208243]] where
 M := ![![![1087394668, 218673370, 95208243]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![1087394668, 218673370, 95208243]] ![![88770, 1115, -4501]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1047202884, -21607322, -30385849]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![1047202884, -21607322, -30385849]] 
 ![![89, 0, 0], ![0, 89, 0], ![73, 86, 1]] where
  M :=![![![1047202884, -21607322, -30385849], ![-5239194823, 465821485, -81701029], ![72993214, -823112209, 534693719]]]
  hmulB := by decide  
  f := ![![![2042951772438086, 410834411803831, 178873278039327]], ![![31408999368332579, 6316300734518138, 2750055460312667]], ![![32566087898945625, 6548989431477467, 2851365839365551]]]
  g := ![![![36689549, 29118828, -30385849], ![8145846, 84181011, -81701029], ![-437748857, -525918787, 534693719]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [27, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 88], [0, 1]]
 g := ![![[6, 21], [22], [40], [0, 8], [28, 78], [1]], ![[75, 68], [22], [40], [39, 81], [30, 11], [1]]]
 h' := ![![[16, 88], [84, 33], [77, 17], [0, 29], [45, 50], [62, 16], [0, 1]], ![[0, 1], [78, 56], [82, 72], [19, 60], [44, 39], [51, 73], [16, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [41, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [27, 73, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2531, 3940, 1772]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1425, -1668, 1772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2042951772438086, 410834411803831, 178873278039327]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![2042951772438086, 410834411803831, 178873278039327]] 
 ![![89, 0, 0], ![27, 1, 0], ![77, 0, 1]] where
  M :=![![![2042951772438086, 410834411803831, 178873278039327], ![31408999368332579, 6316300734518138, 2750055460312667], ![48072397941578553, 9667284171255032, 4209040819773806]]]
  hmulB := by decide  
  f := ![![![1047202884, -21607322, -30385849]], ![![258823405, -1321081, -10136168]], ![![906827138, -27942427, -20281086]]]
  g := ![![![-256436177025770, 410834411803831, 178873278039327], ![-3942532482109354, 6316300734518138, 2750055460312667], ![-6034161997807757, 9667284171255032, 4209040819773806]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![1047202884, -21607322, -30385849]] ![![2042951772438086, 410834411803831, 178873278039327]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6400687891801778145374, 1287168341732345197871, 560420485867299694063]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![6400687891801778145374, 1287168341732345197871, 560420485867299694063]] 
 ![![97, 0, 0], ![0, 97, 0], ![44, 15, 1]] where
  M :=![![![6400687891801778145374, 1287168341732345197871, 560420485867299694063], ![98406239766772938080515, 19789341176742908538058, 8616085276256862500779], ![150613646188685866772129, 30288169097459363774752, 13187172098083436738958]]]
  hmulB := by decide  
  f := ![![![-138816765652, -9000419186, 11779943215]], ![![1996369451393, 34441011445, -107343183133]], ![![214822880853, 1487512882, -10101307552]]]
  g := ![![![-188224881302674313334, -73393185013166497042, 560420485867299694063], ![-2893830024624010432513, -1128370494506288958491, 8616085276256862500779], ![-4429092021927684017959, -1727004251276208116594, 13187172098083436738958]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [12, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 96], [0, 1]]
 g := ![![[38, 89], [22], [86], [75], [93], [29, 1]], ![[0, 8], [22], [86], [75], [93], [58, 96]]]
 h' := ![![[29, 96], [81, 34], [32, 33], [71, 38], [96, 50], [40, 53], [0, 1]], ![[0, 1], [0, 63], [19, 64], [9, 59], [91, 47], [25, 44], [29, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [93, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [12, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3728, 1983, 2111]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-996, -306, 2111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-138816765652, -9000419186, 11779943215]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-138816765652, -9000419186, 11779943215]] 
 ![![97, 0, 0], ![77, 1, 0], ![79, 0, 1]] where
  M :=![![![-138816765652, -9000419186, 11779943215], ![1996369451393, 34441011445, -107343183133], ![-2999784639466, 23692022063, 112003412991]]]
  hmulB := by decide  
  f := ![![![6400687891801778145374, 1287168341732345197871, 560420485867299694063]], ![![6095455746757833559529, 1225786633918901946125, 533695491629267411790]], ![![6765649377742539590275, 1360561526745511694913, 592375159604124871855]]]
  g := ![![![-3880412395, -9000419186, 11779943215], ![80665185955, 34441011445, -107343183133], ![-140951958398, 23692022063, 112003412991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![6400687891801778145374, 1287168341732345197871, 560420485867299694063]] ![![-138816765652, -9000419186, 11779943215]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [56, 22, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 66, 83], [83, 34, 18], [0, 1]]
 g := ![![[14, 82, 70], [89, 16], [95, 8, 80], [50, 5], [53, 36], [1]], ![[41, 65, 82, 57], [87, 19], [42, 40, 41, 73], [62, 20], [49, 36], [42, 64, 72, 26]], ![[28, 64, 65, 51], [27, 37], [42, 71, 65, 18], [82, 5], [], [41, 48, 67, 75]]]
 h' := ![![[24, 66, 83], [44, 57, 75], [33, 64, 97], [73, 75, 79], [67, 90, 45], [45, 79, 6], [0, 1]], ![[83, 34, 18], [6, 89, 9], [63, 54, 25], [54, 94, 23], [30, 80, 11], [59, 56, 95], [24, 66, 83]], ![[0, 1], [26, 56, 17], [15, 84, 80], [11, 33, 100], [82, 32, 45], [53, 67], [83, 34, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 53], []]
 b := ![[], [14, 71, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [56, 22, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-394199974242, -90222182334, -33585765128]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3902970042, -893288934, -332532328]
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


def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84793687918981977302, -2027588332022051333, 4928273724836488301]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-84793687918981977302, -2027588332022051333, 4928273724836488301]] 
 ![![103, 0, 0], ![14, 1, 0], ![22, 0, 1]] where
  M :=![![![-84793687918981977302, -2027588332022051333, 4928273724836488301], ![838679630282995396805, -7095799592827830184, -31005527830685875567], ![-957823546655495327267, 39455104228172451854, 14926277848977454416]]]
  hmulB := by decide  
  f := ![![![-1117412455926003635981668446036093558674, -224709900285493217142566974551176296582, -97836489147722513773270634776655158195]], ![![-318672173085394050419978356703064994815, -64084476468841466616999104899118721261, -27901753232125178530548667756821525367]], ![![-493948954610425518593107764550873450390, -99332363576214302671448267273259251841, -43248337962389777177262752895392486941]]]
  g := ![![![-1600286147738601954, -2027588332022051333, 4928273724836488301], ![15729538221919167785, -7095799592827830184, -31005527830685875567], ![-17850224451722462625, 39455104228172451854, 14926277848977454416]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6206959826, -883497759, 313470133]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![6206959826, -883497759, 313470133]] 
 ![![103, 0, 0], ![96, 1, 0], ![74, 0, 1]] where
  M :=![![![6206959826, -883497759, 313470133], ![51836397225, 8885458810, -8008392471], ![-189948413281, -10317409908, 14813385630]]]
  hmulB := by decide  
  f := ![![![48997860024562897632, 9853393151231525406, 4290070846384250759]], ![![52981587023225321391, 10654514430922487143, 4638871203141626445]], ![![46396146463365030826, 9330192616095461877, 4062274459073821767]]]
  g := ![![![658504416, -883497759, 313470133], ![-2024724327, 8885458810, -8008392471], ![-2870559211, -10317409908, 14813385630]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-84793687918981977302, -2027588332022051333, 4928273724836488301]] ![![6206959826, -883497759, 313470133]]
  ![![-1567531662846107470235356145958, 6051960487983359299965286180, 62661853679128480349408307307]] where
 M := ![![![-1567531662846107470235356145958, 6051960487983359299965286180, 62661853679128480349408307307]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-1567531662846107470235356145958, 6051960487983359299965286180, 62661853679128480349408307307]] ![![6206959826, -883497759, 313470133]]
  ![![103, 0, 0]] where
 M := ![![![-21318413909020302585673344299790903577075, 792177126919116714889399770556271556166, 388393369198728573913561937683043775216]]]
 hmul := by decide  
 g := ![![![![-206974892320585461996828585434863141525, 7691040067175890435819415248119141322, 3770809409696393921490892598864502672]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [87, 83, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 27, 34], [68, 79, 73], [0, 1]]
 g := ![![[53, 67, 40], [79, 84, 52], [68, 23], [88, 100, 12], [53, 47], [1]], ![[41, 54, 86, 36], [32, 4, 30, 41], [24, 87], [89, 70, 76, 62], [92, 57], [7, 1, 8, 35]], ![[17, 43, 96, 59], [104, 87, 1, 103], [64, 76], [29, 47, 47, 18], [19, 1], [23, 60, 55, 72]]]
 h' := ![![[97, 27, 34], [82, 79, 88], [26, 40, 65], [48, 99, 39], [69, 69, 36], [20, 24, 58], [0, 1]], ![[68, 79, 73], [92, 73, 8], [71, 1, 75], [74, 14, 27], [37, 67, 54], [103, 49, 48], [97, 27, 34]], ![[0, 1], [67, 62, 11], [23, 66, 74], [53, 101, 41], [33, 78, 17], [98, 34, 1], [68, 79, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 45], []]
 b := ![[], [65, 33, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [87, 83, 49, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7023373, -1622548, -516596]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65639, -15164, -4828]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24420, 761, -1535]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![24420, 761, -1535]] 
 ![![109, 0, 0], ![0, 109, 0], ![48, 85, 1]] where
  M :=![![![24420, 761, -1535], ![-260963, 608, 10693], ![320471, -10088, -7028]]]
  hmulB := by decide  
  f := ![![![-950440, -191132, -83217]], ![![-14612371, -2938525, -1279405]], ![![-12018691, -2416940, -1052312]]]
  g := ![![![900, 1204, -1535], ![-7103, -8333, 10693], ![6035, 5388, -7028]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [67, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 108], [0, 1]]
 g := ![![[45, 27], [63], [60, 27], [33, 7], [36], [37, 1]], ![[63, 82], [63], [78, 82], [74, 102], [36], [74, 108]]]
 h' := ![![[37, 108], [90, 71], [13, 64], [78, 38], [7, 15], [28, 103], [0, 1]], ![[0, 1], [101, 38], [92, 45], [67, 71], [17, 94], [24, 6], [37, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [43, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [67, 72, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2574, 3945, 1784]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-762, -1355, 1784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![950440, 191132, 83217]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![950440, 191132, 83217]] 
 ![![109, 0, 0], ![86, 1, 0], ![79, 0, 1]] where
  M :=![![![950440, 191132, 83217], ![14612371, 2938525, 1279405], ![22364664, 4497499, 1958167]]]
  hmulB := by decide  
  f := ![![![-24420, -761, 1535]], ![![-16873, -606, 1113]], ![![-20639, -459, 1177]]]
  g := ![![![-202395, 191132, 83217], ![-3111686, 2938525, 1279405], ![-4762527, 4497499, 1958167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![24420, 761, -1535]] ![![950440, 191132, 83217]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46887268973, 9428956586, 4105275324]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![46887268973, 9428956586, 4105275324]] 
 ![![113, 0, 0], ![10, 1, 0], ![97, 0, 1]] where
  M :=![![![46887268973, 9428956586, 4105275324], ![720859993576, 144963819239, 63115826716], ![1103297436030, 221871391822, 96600630371]]]
  hmulB := by decide  
  f := ![![![5991117, -73078, -206860]], ![![215858, 13491, -17988]], ![![5259227, -101184, -157393]]]
  g := ![![![-3943486755, 9428956586, 4105275324], ![-60628437082, 144963819239, 63115826716], ![-92793607329, 221871391822, 96600630371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, -2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![47, 0, -2]] 
 ![![113, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, -2], ![-342, 13, 6], ![248, -30, 9]]]
  hmulB := by decide  
  f := ![![![-297, -60, -26]], ![![-114, -23, -10]], ![![-149, -30, -13]]]
  g := ![![![1, 0, -2], ![-8, 13, 6], ![7, -30, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86543, 5626, 2]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-86543, 5626, 2]] 
 ![![113, 0, 0], ![75, 1, 0], ![60, 0, 1]] where
  M :=![![![-86543, 5626, 2], ![11594, -69631, 45002], ![961798, 95672, -103383]]]
  hmulB := by decide  
  f := ![![![2893230329, 581824102, 253320514]], ![![2313926821, 465327071, 202598848]], ![![2138707942, 430090828, 187257333]]]
  g := ![![![-4501, 5626, 2], ![22423, -69631, 45002], ![-94, 95672, -103383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![46887268973, 9428956586, 4105275324]] ![![47, 0, -2]]
  ![![-2893230329, -581824102, -253320514]] where
 M := ![![![-2893230329, -581824102, -253320514]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-2893230329, -581824102, -253320514]] ![![-86543, 5626, 2]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-340291308490, -29974093845, 34045629021]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-340291308490, -29974093845, 34045629021]] 
 ![![127, 0, 0], ![23, 1, 0], ![116, 0, 1]] where
  M :=![![![-340291308490, -29974093845, 34045629021], ![5761854374901, 148562103332, -341929637823], ![-9347228046099, 1124839950, 396497924444]]]
  hmulB := by decide  
  f := ![![![-59289181738885398076258, -11922961880277875636130, -5191140795872723501463]], ![![-17914820313772878943121, -3602642394928712316067, -1568555204406909252900]], ![![-65139134681496103908998, -13099378283583057575805, -5703340972762751526499]]]
  g := ![![![-28347874933, -29974093845, 34045629021], ![330777669179, 148562103332, -341929637823], ![-435959516539, 1124839950, 396497924444]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![529556074, -18965160, -10113513]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![529556074, -18965160, -10113513]] 
 ![![127, 0, 0], ![46, 1, 0], ![36, 0, 1]] where
  M :=![![![529556074, -18965160, -10113513], ![-1767341043, 300730873, -121380741], ![-1988966748, -474110415, 394294807]]]
  hmulB := by decide  
  f := ![![![61028748039958996, 12272785947462015, 5343450767570409]], ![![29492898133760455, 5930975767829092, 2582288744765541]], ![![28607034891935415, 5752830052984590, 2504725845779098]]]
  g := ![![![13905826, -18965160, -10113513], ![-88435075, 300730873, -121380741], ![44295270, -474110415, 394294807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71510969258397881921, 3155515956055801846, -5100745345878572802]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![71510969258397881921, 3155515956055801846, -5100745345878572802]] 
 ![![127, 0, 0], ![58, 1, 0], ![66, 0, 1]] where
  M :=![![![71510969258397881921, 3155515956055801846, -5100745345878572802], ![-865916422233124345450, -5735153753370450175, 40546363686082133174], ![1172085651374485143114, -22867408935229960648, -34869740181462406855]]]
  hmulB := by decide  
  f := ![![![-1127173600526964700409576082806271286377, -226672851224801067939306262262975150026, -98691138756071356405659493153475898854]], ![![-651225191025998084291352745327039870976, -130960369166086951996877712318557840303, -57018861743167977526186789146023430214]], ![![-794620582586360666538201694182296410216, -159796958527555582559427654843536030984, -69574030245028557410021371764273994007]]]
  g := ![![![1772757768780686455, 3155515956055801846, -5100745345878572802], ![-25270374077315425392, -5735153753370450175, 40546363686082133174], ![37793686784207415064, -22867408935229960648, -34869740181462406855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-340291308490, -29974093845, 34045629021]] ![![529556074, -18965160, -10113513]]
  ![![-194944507098797881633, -18701843601350922000, 20503833017939058462]] where
 M := ![![![-194944507098797881633, -18701843601350922000, 20503833017939058462]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-194944507098797881633, -18701843601350922000, 20503833017939058462]] ![![71510969258397881921, 3155515956055801846, -5100745345878572802]]
  ![![127, 0, 0]] where
 M := ![![![26285811324714353673597230350227618973675, -976762088531338085349065736511130947894, -478892795031442028029343360055791839344]]]
 hmul := by decide  
 g := ![![![![206974892320585461996828585434863141525, -7691040067175890435819415248119141322, -3770809409696393921490892598864502672]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [9, 51, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 77, 86], [2, 53, 45], [0, 1]]
 g := ![![[7, 71, 53], [117, 44, 99], [4, 62], [39, 39], [112, 4], [70, 1], []], ![[88, 8, 84, 90], [95, 12, 31, 111], [116, 60], [106, 112], [56, 44], [126, 58], [21, 60]], ![[32, 32, 49, 11], [85, 115, 70, 113], [116, 74], [130, 13], [6, 41], [55, 34], [62, 60]]]
 h' := ![![[68, 77, 86], [126, 76, 70], [85, 67, 19], [11, 127, 18], [10, 12, 68], [25, 89, 2], [0, 0, 1], [0, 1]], ![[2, 53, 45], [34, 73, 28], [88, 74, 88], [52, 25, 86], [58, 86, 51], [13, 78, 31], [112, 84, 53], [68, 77, 86]], ![[0, 1], [12, 113, 33], [42, 121, 24], [118, 110, 27], [90, 33, 12], [12, 95, 98], [101, 47, 77], [2, 53, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 52], []]
 b := ![[], [6, 125, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [9, 51, 61, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3650700009, 811339330, 309935782]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27867939, 6193430, 2365922]
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

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![510371234589719466128912666, 102634858440162702381789387, 44686211872291360060219849]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![510371234589719466128912666, 102634858440162702381789387, 44686211872291360060219849]] 
 ![![137, 0, 0], ![0, 137, 0], ![16, 5, 1]] where
  M :=![![![510371234589719466128912666, 102634858440162702381789387, 44686211872291360060219849], ![7846611947042147975061172953, 1577941411739160694298018260, 687020231904427538873655549], ![12009470521103693459818723901, 2415085771567136341393717314, 1051504684842767200127721636]]]
  hmulB := by decide  
  f := ![![![33126325632102, -2485335162858, 216057557779]], ![![31975172054493, 29343298625771, -20530853976201]], ![![1738055623159, 495921869498, -397882658672]]]
  g := ![![![-1493490185160162736019014, -881724094316015313279634, 44686211872291360060219849], ![-22961399733056150707425663, -13555910567758956204892405, 687020231904427538873655549], ![-35143098075770669651276075, -20747720092311676344853218, 1051504684842767200127721636]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [90, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 136], [0, 1]]
 g := ![![[31, 123], [32], [118], [9, 101], [14], [34], [1]], ![[46, 14], [32], [118], [28, 36], [14], [34], [1]]]
 h' := ![![[87, 136], [120, 64], [73, 124], [12, 114], [129, 52], [108, 39], [47, 87], [0, 1]], ![[0, 1], [71, 73], [38, 13], [66, 23], [132, 85], [76, 98], [81, 50], [87, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [80, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [90, 50, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1075, 135, 27]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, 0, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33126325632102, -2485335162858, 216057557779]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![33126325632102, -2485335162858, 216057557779]] 
 ![![137, 0, 0], ![100, 1, 0], ![117, 0, 1]] where
  M :=![![![33126325632102, -2485335162858, 216057557779], ![31975172054493, 29343298625771, -20530853976201], ![-451783450013314, -39009834401901, 44687424718477]]]
  hmulB := by decide  
  f := ![![![510371234589719466128912666, 102634858440162702381789387, 44686211872291360060219849]], ![![429808287635139376554397369, 86433775589455700237058080, 37632419117763237553982777]], ![![523524853781758182459135079, 105280030723110748321628289, 45837893970079243264039737]]]
  g := ![![![1871394946407, -2485335162858, 216057557779], ![-3651421717570, 29343298625771, -20530853976201], ![-12987070816679, -39009834401901, 44687424718477]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![510371234589719466128912666, 102634858440162702381789387, 44686211872291360060219849]] ![![33126325632102, -2485335162858, 216057557779]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB219I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB219I2 : PrimesBelowBoundCertificateInterval O 79 137 219 where
  m := 11
  g := ![3, 2, 2, 1, 3, 1, 2, 3, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB219I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I103N0, I103N1, I109N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [], [I103N0, I103N1, I103N1], [], [I109N1], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
