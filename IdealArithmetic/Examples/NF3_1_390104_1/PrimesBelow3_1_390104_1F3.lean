
import IdealArithmetic.Examples.NF3_1_390104_1.RI3_1_390104_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20926304289898947879933101956987, -466200065432720949834216007856, -778768739966919262912847859117]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-20926304289898947879933101956987, -466200065432720949834216007856, -778768739966919262912847859117]] 
 ![![139, 0, 0], ![67, 1, 0], ![55, 0, 1]] where
  M :=![![![-20926304289898947879933101956987, -466200065432720949834216007856, -778768739966919262912847859117], ![-79434411476625764817110481629934, -1769654465260164620190537330323, -2956137676232001375328343741802], ![-126986818150763301700200514431246, -2829035749019243936410077275562, -4725792141492165995518881072125]]]
  hmulB := by decide  
  f := ![![![19385163419896349, -2940145060384754, -1355346471491721]], ![![8349356899574819, -1022561836328749, -736254256935849]], ![![4518301092394955, -831228297545168, -224615541439568]]]
  g := ![![![382312092030747591504791387200, -466200065432720949834216007856, -778768739966919262912847859117], ![1451223092723491657400823203603, -1769654465260164620190537330323, -2956137676232001375328343741802], ![2319979459105001235919518863297, -2829035749019243936410077275562, -4725792141492165995518881072125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16082033, 4548756, -195219]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-16082033, 4548756, -195219]] 
 ![![139, 0, 0], ![93, 1, 0], ![67, 0, 1]] where
  M :=![![![-16082033, 4548756, -195219], ![-19912338, -15945533, 13255830], ![444060774, -112684086, -2689703]]]
  hmulB := by decide  
  f := ![![![1536609835668079, 34232877244302, 57184665240753]], ![![1070054320659627, 23838867455869, 39821883666219]], ![![807751426785877, 17995235221860, 30060327525112]]]
  g := ![![![-3065012, 4548756, -195219], ![4135839, -15945533, 13255830], ![79884107, -112684086, -2689703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90418583, -92230682, 42793128]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![90418583, -92230682, 42793128]] 
 ![![139, 0, 0], ![117, 1, 0], ![63, 0, 1]] where
  M :=![![![90418583, -92230682, 42793128], ![4364899056, -844385807, -191105790], ![-5042630508, 2983812672, -1035491597]]]
  hmulB := by decide  
  f := ![![![-1444578285669134659, -32182581404338862, -53759727266183076]], ![![-1255389579888053445, -27967800533698193, -46719102797761170]], ![![-717802499867256987, -15991336442881374, -26712894002815241]]]
  g := ![![![58888067, -92230682, 42793128], ![828760455, -844385807, -191105790], ![-2078508939, 2983812672, -1035491597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-20926304289898947879933101956987, -466200065432720949834216007856, -778768739966919262912847859117]] ![![-16082033, 4548756, -195219]]
  ![![-1444578285669134659, -32182581404338862, -53759727266183076]] where
 M := ![![![-1444578285669134659, -32182581404338862, -53759727266183076]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-1444578285669134659, -32182581404338862, -53759727266183076]] ![![90418583, -92230682, 42793128]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3208114002678431174284145, -1631666008165305982717728, 491991689988778991190681]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![3208114002678431174284145, -1631666008165305982717728, 491991689988778991190681]] 
 ![![149, 0, 0], ![77, 1, 0], ![36, 0, 1]] where
  M :=![![![3208114002678431174284145, -1631666008165305982717728, 491991689988778991190681], ![50183152378855457101449462, -6968020548886958631574471, -3911014644518359965771822], ![-116246780454005753135758794, 48015834615765365426657730, -10879035193405318597346293]]]
  hmulB := by decide  
  f := ![![![263595973130742612086392090514822305916254277770063, 5872439692118582951151800708333692352010066431826, 9809677858620759783439293543219626220718694965167]], ![![142936087735882541131295294705031674027281115937865, 3184356517616487795781113418194039566253494278019, 5319341408774468266746037530465446634179913433179]], ![![74423026999209040228445683705986855754385823236346, 1658009917856353500105563035422534095282263802382, 2769639882789734328569434909641372199398229128497]]]
  g := ![![![745870441555778175575065, -1631666008165305982717728, 491991689988778991190681], ![4882666186884645842285029, -6968020548886958631574471, -3911014644518359965771822], ![-22965240126881526318684144, 48015834615765365426657730, -10879035193405318597346293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7522621330578277287761764627669, -167590345048839513277642995516, -279953032016768234794804031402]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-7522621330578277287761764627669, -167590345048839513277642995516, -279953032016768234794804031402]] 
 ![![149, 0, 0], ![102, 1, 0], ![142, 0, 1]] where
  M :=![![![-7522621330578277287761764627669, -167590345048839513277642995516, -279953032016768234794804031402], ![-28555209265710359949070011203004, -636158217127000139408824878505, -1062677099180055009422537049352], ![-45649424460691990303389596745636, -1016986295129679907643040672852, -1698835316307055148831361927857]]]
  hmulB := by decide  
  f := ![![![-10560611789421881, 3896949949590708, -697374351891622]], ![![-7706809304791794, 2683008842715695, -408295857368836]], ![![-7874162168675170, 3001928561863452, -580212309511645]]]
  g := ![![![331039761146204311459194586403, -167590345048839513277642995516, -279953032016768234794804031402], ![1256597831978600440326378439010, -636158217127000139408824878505, -1062677099180055009422537049352], ![2008844245356625445706402319738, -1016986295129679907643040672852, -1698835316307055148831361927857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26740340007912570727, 595726225170084522, 995137058400751817]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![26740340007912570727, 595726225170084522, 995137058400751817]] 
 ![![149, 0, 0], ![118, 1, 0], ![17, 0, 1]] where
  M :=![![![26740340007912570727, 595726225170084522, 995137058400751817], ![101503979956876685334, 2261324381124442597, 3777452792311757200], ![162268054924225306578, 3615037647131504178, 6038777173436199797]]]
  hmulB := by decide  
  f := ![![![23227971209, -3692650608, -1517890349]], ![![17356213336, -2499213299, -1296810696]], ![![-916776289, -9889074, 157262562]]]
  g := ![![![-405856943321947542, 595726225170084522, 995137058400751817], ![-1540597278423539688, 2261324381124442597, 3777452792311757200], ![-2462856371716158275, 3615037647131504178, 6038777173436199797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![3208114002678431174284145, -1631666008165305982717728, 491991689988778991190681]] ![![-7522621330578277287761764627669, -167590345048839513277642995516, -279953032016768234794804031402]]
  ![![-23227971209, 3692650608, 1517890349]] where
 M := ![![![-23227971209, 3692650608, 1517890349]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-23227971209, 3692650608, 1517890349]] ![![26740340007912570727, 595726225170084522, 995137058400751817]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [48, 6, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 0, 115], [86, 150, 36], [0, 1]]
 g := ![![[64, 27, 121], [49, 143, 84], [114, 44, 78], [92, 22], [28, 7, 42], [34, 1], []], ![[126, 56, 148, 70], [110, 95, 125, 140], [43, 0, 112, 51], [78, 99], [88, 145, 86, 119], [143, 1], [123, 88]], ![[146, 76, 61, 78], [32, 149, 146, 20], [104, 44, 140, 145], [13, 137], [61, 141, 27, 50], [], [51, 88]]]
 h' := ![![[99, 0, 115], [64, 27, 11], [115, 83, 101], [37, 46, 57], [15, 35, 133], [29, 50, 93], [0, 0, 1], [0, 1]], ![[86, 150, 36], [2, 80, 74], [118, 7, 82], [69, 140, 99], [76, 75, 117], [17, 141, 70], [122, 21, 150], [99, 0, 115]], ![[0, 1], [38, 44, 66], [94, 61, 119], [35, 116, 146], [31, 41, 52], [17, 111, 139], [116, 130], [86, 150, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 92], []]
 b := ![[], [142, 19, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [48, 6, 117, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11778, 137410, -81238]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 910, -538]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-777708532850635680843203668969, -17325934091360887264522990568, -28942286502158841792998885703]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-777708532850635680843203668969, -17325934091360887264522990568, -28942286502158841792998885703]] 
 ![![157, 0, 0], ![0, 157, 0], ![66, 95, 1]] where
  M :=![![![-777708532850635680843203668969, -17325934091360887264522990568, -28942286502158841792998885703], ![-2952113223220201862885886341706, -65767722707462590546707421529, -109862375278400345379566743110], ![-4719358500539012363867231379642, -105138738846197857925428169022, -175630097985862935926274164639]]]
  hmulB := by decide  
  f := ![![![-374813917103023, 96710641610398, 1270345882251]], ![![129575279989602, -502012859887445, 292672616595696]], ![![-15503224239090, -277748461884013, 176295548799541]]]
  g := ![![![7213263543260177563660654697, 17402492252316745752040580581, -28942286502158841792998885703], ![27380914300345356255831329322, 66058330756309364461860720853, -109862375278400345379566743110], ![43772152653044212785139257876, 105603315731278860223379729119, -175630097985862935926274164639]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [27, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 156], [0, 1]]
 g := ![![[6, 64], [148], [80, 1], [106, 4], [25, 144], [25], [1]], ![[0, 93], [148], [75, 156], [86, 153], [90, 13], [25], [1]]]
 h' := ![![[152, 156], [117, 149], [38, 84], [121, 1], [110, 2], [54, 145], [130, 152], [0, 1]], ![[0, 1], [0, 8], [89, 73], [116, 156], [100, 155], [114, 12], [155, 5], [152, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [36, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [27, 5, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![737, 1872, -1114]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![473, 686, -1114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![374813917103023, -96710641610398, -1270345882251]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![374813917103023, -96710641610398, -1270345882251]] 
 ![![157, 0, 0], ![27, 1, 0], ![80, 0, 1]] where
  M :=![![![374813917103023, -96710641610398, -1270345882251], ![-129575279989602, 502012859887445, -292672616595696], ![-9994060724250198, 2298189172769034, 209340243291749]]]
  hmulB := by decide  
  f := ![![![777708532850635680843203668969, 17325934091360887264522990568, 28942286502158841792998885703]], ![![152549322357881307297148951617, 3398521931045901571266421445, 5677096247367446329876029663]], ![![426344211010126540326901432466, 9498174943662858847689601366, 15866324956424014518255955547]]]
  g := ![![![19666426185757, -96710641610398, -1270345882251], ![61973801469459, 502012859887445, -292672616595696], ![-565556610524548, 2298189172769034, 209340243291749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-777708532850635680843203668969, -17325934091360887264522990568, -28942286502158841792998885703]] ![![374813917103023, -96710641610398, -1270345882251]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23874510097640087842235036491561, -6041095316848991178528294408874, -155405200277972570317660985526]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![23874510097640087842235036491561, -6041095316848991178528294408874, -155405200277972570317660985526]] 
 ![![163, 0, 0], ![6, 1, 0], ![153, 0, 1]] where
  M :=![![![23874510097640087842235036491561, -6041095316848991178528294408874, -155405200277972570317660985526], ![-15851330428353202172401420523652, 33645330221160420708387194553059, -18434096351102918676220205197674], ![-632043052746950302382287450228800, 142188993999372282018961168073508, 15211233870057502032166989355385]]]
  hmulB := by decide  
  f := ![![![3132912602080208040335287909275565340255427940864456672492493107, 69795604606103242052893056407227575033968703823774690791641282, 116590792418428876968103293695272109186523686892885189187783110]], ![![188280591651294439832872781672215626862318918455589137006802674, 4194549736616142351934197194019463772691429291742856355484079, 7006829160526016821493898888244537414687703108063837950166802]], ![![3057343807452601879211292502022186900917611649112645267786826585, 68112069065760969388031064803970890458523859860974653481606266, 113778512994519002498543592001047035544527413076564207593100387]]]
  g := ![![![514712132768489804736238857241, -6041095316848991178528294408874, -155405200277972570317660985526], ![15967444355603870129073415996332, 33645330221160420708387194553059, -18434096351102918676220205197674], ![-23389544778294366904402477484931, 142188993999372282018961168073508, 15211233870057502032166989355385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![190429996536115706754746605846116108907965807086321293, 4242434574954690832447153552039705700694369705397686, 7086818885928173935945291615057605646035346632998688]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![190429996536115706754746605846116108907965807086321293, 4242434574954690832447153552039705700694369705397686, 7086818885928173935945291615057605646035346632998688]] 
 ![![163, 0, 0], ![20, 1, 0], ![145, 0, 1]] where
  M :=![![![190429996536115706754746605846116108907965807086321293, 4242434574954690832447153552039705700694369705397686, 7086818885928173935945291615057605646035346632998688], ![722855526364673741466419744735875775895605356565866176, 16103908698884841459612453532693867702423118188955095, 26900941496720420369232043886234328394153802382190434], ![1155583853010052206376029407043925757366431066516430148, 25744310147794550868283563822083964811971366464431920, 43004850195605261828844497418928196096576920571145529]]]
  hmulB := by decide  
  f := ![![![2202831383530493558622766975, -658960759545521131500524934, 49194399706699184529020364]], ![![301070284912228147205002556, -70540421109172934776587089, -5488377209136081808976238]], ![![1578002342996084217234403345, -483734679204217617116816874, 42551049253763503022645533]]]
  g := ![![![-5656487321610817979179532204773195237920532814763449, 4242434574954690832447153552039705700694369705397686, 7086818885928173935945291615057605646035346632998688], ![-21471528617407877553769789505656314081626738359698458, 16103908698884841459612453532693867702423118188955095, 26900941496720420369232043886234328394153802382190434], ![-34325187903733753228049656411916208422556133408517239, 25744310147794550868283563822083964811971366464431920, 43004850195605261828844497418928196096576920571145529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12554813767, 279698456, 467225190]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![12554813767, 279698456, 467225190]] 
 ![![163, 0, 0], ![136, 1, 0], ![74, 0, 1]] where
  M :=![![![12554813767, 279698456, 467225190], ![47656969380, 1061710751, 1773545748], ![76186211892, 1697290476, 2835256499]]]
  hmulB := by decide  
  f := ![![![224701, 24896, -52602]], ![![154564, 29743, -44076]], ![![84674, 1828, -15097]]]
  g := ![![![-368459143, 279698456, 467225190], ![-1398638516, 1061710751, 1773545748], ![-2235915790, 1697290476, 2835256499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![23874510097640087842235036491561, -6041095316848991178528294408874, -155405200277972570317660985526]] ![![190429996536115706754746605846116108907965807086321293, 4242434574954690832447153552039705700694369705397686, 7086818885928173935945291615057605646035346632998688]]
  ![![224701, 24896, -52602]] where
 M := ![![![224701, 24896, -52602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![224701, 24896, -52602]] ![![12554813767, 279698456, 467225190]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [79, 148, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 120, 94], [100, 46, 73], [0, 1]]
 g := ![![[30, 157, 98], [67, 76, 85], [137, 18, 84], [74, 88], [155, 6], [134, 68, 1], []], ![[44, 22, 101, 128], [111, 69, 65, 122], [17, 156, 43, 152], [158, 18], [42, 19], [148, 86, 123, 7], [164, 152]], ![[91, 9, 62, 123], [153, 121, 3, 69], [154, 135, 21, 80], [5, 88], [37, 8], [43, 125, 83, 102], [18, 152]]]
 h' := ![![[135, 120, 94], [51, 134, 91], [32, 70, 69], [15, 63, 90], [163, 113, 64], [102, 13, 138], [0, 0, 1], [0, 1]], ![[100, 46, 73], [127, 6, 82], [132, 31, 68], [100, 42, 42], [97, 42, 39], [24, 19, 55], [92, 128, 46], [135, 120, 94]], ![[0, 1], [131, 27, 161], [52, 66, 30], [115, 62, 35], [3, 12, 64], [134, 135, 141], [61, 39, 120], [100, 46, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 147], []]
 b := ![[], [26, 83, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [79, 148, 99, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![109385, -2338, 4676]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![655, -14, 28]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44514581, -13917216, 1370065]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![44514581, -13917216, 1370065]] 
 ![![173, 0, 0], ![0, 173, 0], ![77, 17, 1]] where
  M :=![![![44514581, -13917216, 1370065], ![139746630, 25550237, -39011518], ![-1279809402, 358674354, -13461281]]]
  hmulB := by decide  
  f := ![![![78893017903675, 1757593199418, 2935989809471]], ![![299470960566042, 6671669276953, 11144759217196]], ![![67309330491979, 1499529675421, 2504904916276]]]
  g := ![![![-352488, -215077, 1370065], ![18171292, 3981191, -39011518], ![-1406305, 3396047, -13461281]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [104, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 172], [0, 1]]
 g := ![![[41, 159], [43], [47, 64], [70, 130], [139], [119, 88], [1]], ![[52, 14], [43], [145, 109], [42, 43], [139], [124, 85], [1]]]
 h' := ![![[61, 172], [59, 141], [129, 40], [159, 8], [75, 86], [80, 100], [69, 61], [0, 1]], ![[0, 1], [10, 32], [147, 133], [128, 165], [131, 87], [125, 73], [157, 112], [61, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [13, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [104, 112, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1849, 2637, -2389]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1074, 250, -2389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78893017903675, 1757593199418, 2935989809471]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![78893017903675, 1757593199418, 2935989809471]] 
 ![![173, 0, 0], ![120, 1, 0], ![84, 0, 1]] where
  M :=![![![78893017903675, 1757593199418, 2935989809471], ![299470960566042, 6671669276953, 11144759217196], ![478745466906678, 10665579784446, 17816428494149]]]
  hmulB := by decide  
  f := ![![![44514581, -13917216, 1370065]], ![![31684950, -9505871, 724834]], ![![14216274, -4684230, 587423]]]
  g := ![![![-2188678092613, 1757593199418, 2935989809471], ![-8308029635334, 6671669276953, 11144759217196], ![-13281526593846, 10665579784446, 17816428494149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![44514581, -13917216, 1370065]] ![![78893017903675, 1757593199418, 2935989809471]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB177I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 176 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 176 (by omega)

def PB177I3 : PrimesBelowBoundCertificateInterval O 137 176 177 where
  m := 7
  g := ![3, 3, 1, 2, 3, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB177I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![4657463]
    · exact ![29929, 173]
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
      exact NI149N1
      exact NI149N2
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
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I139N0, I139N1, I139N2, I149N0, I149N1, I149N2, I157N1, I163N0, I163N1, I163N2, I173N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N0, I149N1, I149N2], [], [I157N1], [I163N0, I163N1, I163N2], [], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
