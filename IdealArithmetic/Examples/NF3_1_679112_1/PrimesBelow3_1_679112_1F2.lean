
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2501345, 470927, -78791]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2501345, 470927, -78791]] 
 ![![83, 0, 0], ![32, 1, 0], ![55, 0, 1]] where
  M :=![![![-2501345, 470927, -78791], ![12448978, -2343763, 392136], ![-61957488, 11664706, -1951627]]]
  hmulB := by decide  
  f := ![![![-385, 2217, 461]], ![![-1026, 839, 210]], ![![-5353, 527, 322]]]
  g := ![![![-159488, 470927, -78791], ![793758, -2343763, 392136], ![-3950465, 11664706, -1951627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-180760826121917086354330891566582973642313, 34031752365930030056231510399368335331672, -5693867194912315793504918916657785935226]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-180760826121917086354330891566582973642313, 34031752365930030056231510399368335331672, -5693867194912315793504918916657785935226]] 
 ![![83, 0, 0], ![52, 1, 0], ![35, 0, 1]] where
  M :=![![![-180760826121917086354330891566582973642313, 34031752365930030056231510399368335331672, -5693867194912315793504918916657785935226], ![899631016796145895373777188831930177765708, -169373091732092454767321053733267401771861, 28337885171017714262726591482710549396446], ![-4477385857020798853510801454268266804638468, 842955246454110466848324005866509078972816, -141035206561074740504594462250556852375415]]]
  hmulB := by decide  
  f := ![![![-2878770870219314185379, -733015566161092827464, -31061548599452562126]], ![![-1744438079189046178600, -493174183293942603485, -28665995685928658074]], ![![240568718969761145385, -231562239848236787544, -56239507093515591869]]]
  g := ![![![-21097910811184910801273461087357998833209, 34031752365930030056231510399368335331672, -5693867194912315793504918916657785935226], ![105002479588907633061193268446589949891890, -169373091732092454767321053733267401771861, 28337885171017714262726591482710549396446], ![-522588270397553339903166790127195772025125, 842955246454110466848324005866509078972816, -141035206561074740504594462250556852375415]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8317238791788139859424122133176393048472343807, -1565882481304512425757498419394435926635803254, 261988474631520896936310245404523610955771850]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![8317238791788139859424122133176393048472343807, -1565882481304512425757498419394435926635803254, 261988474631520896936310245404523610955771850]] 
 ![![83, 0, 0], ![81, 1, 0], ![79, 0, 1]] where
  M :=![![![8317238791788139859424122133176393048472343807, -1565882481304512425757498419394435926635803254, 261988474631520896936310245404523610955771850], ![-41394178991780301715937018773914730531011952300, 7793261842525098065551501642367345826560800107, -1303894006672991528821188173989912315680031404], ![206015253054332661553747731490406145877444961832, -38786390978434318658294642425934905899651889492, 6489367835852106536730313468377433510880768703]]]
  hmulB := by decide  
  f := ![![![-525686692247071612955547, 47350435154229624359362, 30737016037967737800666]], ![![-571530971156767508697645, 39135235218910752825921, 30937177714067278602578]], ![![-649000794890190851141839, -15324566978303096053442, 23122301130947488672961]]]
  g := ![![![1378995545561005969732686562857449853499595557, -1565882481304512425757498419394435926635803254, 261988474631520896936310245404523610955771850], ![-6863141707339119448779937181451405657153184097, 7793261842525098065551501642367345826560800107, -1303894006672991528821188173989912315680031404], ![34157263412954169355107457879389352727586352809, -38786390978434318658294642425934905899651889492, 6489367835852106536730313468377433510880768703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2501345, 470927, -78791]] ![![-180760826121917086354330891566582973642313, 34031752365930030056231510399368335331672, -5693867194912315793504918916657785935226]]
  ![![1228583433523211054904630131553919880834272514489, -231304802415242172270660905997582523295765429443, 38699706448743445552205109229949425411279327677]] where
 M := ![![![1228583433523211054904630131553919880834272514489, -231304802415242172270660905997582523295765429443, 38699706448743445552205109229949425411279327677]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![1228583433523211054904630131553919880834272514489, -231304802415242172270660905997582523295765429443, 38699706448743445552205109229949425411279327677]] ![![8317238791788139859424122133176393048472343807, -1565882481304512425757498419394435926635803254, 261988474631520896936310245404523610955771850]]
  ![![83, 0, 0]] where
 M := ![![![27765824002248697999371316832968420016638154074964105218841942615890649741934307630252414712787, -5227458111102056384559364105397708135055227742253166678536780724197239104986150670257864767691, 874608275575611448385387260301936569885061890102567999514219423912799464111849123929872855553]]]
 hmul := by decide  
 g := ![![![![334528000027092746980377311240583373694435591264627773720987260432417466770292863015089333889, -62981423025325980536859808498767567892231659545218875645021454508400471144411453858528491177, 10537449103320619860064906750625741805844119157862265054388185830274692338696977396745456091]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [35, 86, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 86, 51], [21, 2, 38], [0, 1]]
 g := ![![[87, 8, 85], [88, 18], [46, 50], [26, 51, 47], [7, 2, 1], []], ![[71, 51, 23, 58], [49, 85], [39, 21], [81, 46, 5, 43], [74, 88, 12, 26], [1, 20]], ![[77, 59, 32, 19], [5, 68], [34, 9], [48, 61, 76, 46], [32, 39, 32, 75], [14, 20]]]
 h' := ![![[70, 86, 51], [85, 47, 21], [36, 49, 75], [69, 23, 53], [22, 40, 74], [0, 0, 1], [0, 1]], ![[21, 2, 38], [75, 76, 36], [59, 5, 68], [0, 4, 33], [68, 81, 52], [59, 40, 2], [70, 86, 51]], ![[0, 1], [43, 55, 32], [60, 35, 35], [2, 62, 3], [84, 57, 52], [40, 49, 86], [21, 2, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 33], []]
 b := ![[], [28, 64, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [35, 86, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-66483, -13884, 890]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-747, -156, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![725146536671380823336263, -136522983958746389065608, 22841719443529539883866]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![725146536671380823336263, -136522983958746389065608, 22841719443529539883866]] 
 ![![97, 0, 0], ![0, 97, 0], ![1, 35, 1]] where
  M :=![![![725146536671380823336263, -136522983958746389065608, 22841719443529539883866], ![-3608991672077667301650828, 679463097784321743568531, -113681264515216849181742], ![17961639793404262170715236, -3381629143047233603287344, 565781833269104894386789]]]
  hmulB := by decide  
  f := ![![![-76534659137, 124827441864, 28171149570]], ![![-4451041632060, -132876958277, 152998591434]], ![![-1856049167297, -95700050647, 55703541061]]]
  g := ![![![7240255847709807045901, -9649310974044126649494, 22841719443529539883866], ![-36034127913014953118238, 48023787173370221287933, -113681264515216849181742], ![179338741857063477075551, -239010240283153658833247, 565781833269104894386789]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [74, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 96], [0, 1]]
 g := ![![[95, 4], [61], [6], [49], [25], [51, 1]], ![[8, 93], [61], [6], [49], [25], [5, 96]]]
 h' := ![![[51, 96], [94, 2], [90, 35], [7, 43], [74, 7], [9, 5], [0, 1]], ![[0, 1], [2, 95], [32, 62], [66, 54], [43, 90], [70, 92], [51, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [2, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [74, 46, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![503, -1504, 115]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -57, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76534659137, 124827441864, 28171149570]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-76534659137, 124827441864, 28171149570]] 
 ![![97, 0, 0], ![61, 1, 0], ![62, 0, 1]] where
  M :=![![![-76534659137, 124827441864, 28171149570], ![-4451041632060, -132876958277, 152998591434], ![-24173777446572, -4757038814928, 20121633157]]]
  hmulB := by decide  
  f := ![![![725146536671380823336263, -136522983958746389065608, 22841719443529539883866]], ![![418813887266768689916095, -78849885811332041128181, 13192408469485413234372]], ![![648667268732266734201686, -122124269572056801292320, 20432664317195220280273]]]
  g := ![![![-97295050373, 124827441864, 28171149570], ![-60118142743, -132876958277, 152998591434], ![2729464422766, -4757038814928, 20121633157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![725146536671380823336263, -136522983958746389065608, 22841719443529539883866]] ![![-76534659137, 124827441864, 28171149570]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1410373382435, -1665985936172, -391682319880]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![1410373382435, -1665985936172, -391682319880]] 
 ![![101, 0, 0], ![0, 101, 0], ![18, 80, 1]] where
  M :=![![![1410373382435, -1665985936172, -391682319880], ![61885806541040, 2193738022195, -2057668256052], ![325111584456216, 66001143053144, 136069766143]]]
  hmulB := by decide  
  f := ![![![-1347593646962974952764073, 253710797119353832505724, -42448463105272260935144]], ![![6706857170633017227752752, -1262696720752430430893785, 211262334014081571570580]], ![![4741707319119633076854606, -892718918905358528730576, 149361188103893823460303]]]
  g := ![![![83768862775, 293748511428, -391682319880], ![979443912376, 1651556420855, -2057668256052], ![3194676521442, 545698631304, 136069766143]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [53, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 100], [0, 1]]
 g := ![![[23, 87], [17], [30, 43], [76], [16], [94, 1]], ![[20, 14], [17], [32, 58], [76], [16], [87, 100]]]
 h' := ![![[94, 100], [78, 17], [26, 57], [18, 12], [39, 51], [68, 97], [0, 1]], ![[0, 1], [60, 84], [31, 44], [35, 89], [86, 50], [96, 4], [94, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [5, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [53, 7, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3859, -277, 119]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, -97, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1347593646962974952764073, 253710797119353832505724, -42448463105272260935144]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1347593646962974952764073, 253710797119353832505724, -42448463105272260935144]] 
 ![![101, 0, 0], ![20, 1, 0], ![4, 0, 1]] where
  M :=![![![-1347593646962974952764073, 253710797119353832505724, -42448463105272260935144], ![6706857170633017227752752, -1262696720752430430893785, 211262334014081571570580], ![-33379448774224888308151640, 6284332502604854084611592, -1051434386738348859323205]]]
  hmulB := by decide  
  f := ![![![1410373382435, -1665985936172, -391682319880]], ![![892012615740, -308178026745, -97933808452]], ![![3274782950356, 587497022856, -14164945677]]]
  g := ![![![-61901145910187748110277, 253710797119353832505724, -42448463105272260935144], ![308076655936884154052932, -1262696720752430430893785, 211262334014081571570580], ![-1533270903756124500624660, 6284332502604854084611592, -1051434386738348859323205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![1410373382435, -1665985936172, -391682319880]] ![![-1347593646962974952764073, 253710797119353832505724, -42448463105272260935144]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4591, 272, 240]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-4591, 272, 240]] 
 ![![103, 0, 0], ![0, 103, 0], ![74, 8, 1]] where
  M :=![![![-4591, 272, 240], ![-37920, -5071, 512], ![-80896, -38944, -4559]]]
  hmulB := by decide  
  f := ![![![418039, -78704, 13168]], ![![-2080544, 391703, -65536]], ![![239274, -45048, 7537]]]
  g := ![![![-217, -16, 240], ![-736, -89, 512], ![2490, -24, -4559]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [85, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 102], [0, 1]]
 g := ![![[48, 23], [4, 50], [80, 92], [100], [76], [40, 1]], ![[41, 80], [47, 53], [52, 11], [100], [76], [80, 102]]]
 h' := ![![[40, 102], [72, 34], [101, 87], [22, 68], [30, 10], [102, 73], [0, 1]], ![[0, 1], [93, 69], [79, 16], [64, 35], [18, 93], [35, 30], [40, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [36, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [85, 63, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-325, -1363, -209]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147, 3, -209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![418039, -78704, 13168]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![418039, -78704, 13168]] 
 ![![103, 0, 0], ![94, 1, 0], ![22, 0, 1]] where
  M :=![![![418039, -78704, 13168], ![-2080544, 391703, -65536], ![10354688, -1949472, 326167]]]
  hmulB := by decide  
  f := ![![![-4591, 272, 240]], ![![-4558, 199, 224]], ![![-1766, -320, 7]]]
  g := ![![![73073, -78704, 13168], ![-363678, 391703, -65536], ![1809994, -1949472, 326167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-4591, 272, 240]] ![![418039, -78704, 13168]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![264839752874864687542961, -134671037092718959372489, -37751245916689364522635]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![264839752874864687542961, -134671037092718959372489, -37751245916689364522635]] 
 ![![107, 0, 0], ![0, 107, 0], ![14, 3, 1]] where
  M :=![![![264839752874864687542961, -134671037092718959372489, -37751245916689364522635], ![5964696854836919594576330, 340342244708243416588231, -172422283009408323895124], ![27242720715486515175429592, 6309541420855736242366578, 167919961698835092693107]]]
  hmulB := by decide  
  f := ![![![-10701456011423138886839871545817320609199119527, 2014757891679539778718620521335945610727782801, -337090013519535337847808634272061148775336003]], ![![53260222136086583379953764214985661506503088474, -10027275984384068211144254277273198311648447521, 1677667878160004440870811887063884461952446798]], ![![-2384217219634999027415749412640927560726775720, 448875410375027352961122101941509684091979547, -75101538888014440911498388867537537819564153]]]
  g := ![![![7414553230920708325793, -200161676099540801912, -37751245916689364522635], ![78304755298772300272038, 8015038259219330731529, -172422283009408323895124], ![232634030389746017548842, 54259640521114308077451, 167919961698835092693107]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [61, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 106], [0, 1]]
 g := ![![[47, 100], [65, 52], [9], [66, 69], [25], [22, 1]], ![[0, 7], [32, 55], [9], [86, 38], [25], [44, 106]]]
 h' := ![![[22, 106], [101, 10], [88, 65], [40, 104], [20, 60], [49, 102], [0, 1]], ![[0, 1], [0, 97], [20, 42], [81, 3], [56, 47], [46, 5], [22, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [42, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [61, 85, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-413, -249, -83]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 0, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10701456011423138886839871545817320609199119527, -2014757891679539778718620521335945610727782801, 337090013519535337847808634272061148775336003]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![10701456011423138886839871545817320609199119527, -2014757891679539778718620521335945610727782801, 337090013519535337847808634272061148775336003]] 
 ![![107, 0, 0], ![103, 1, 0], ![91, 0, 1]] where
  M :=![![![10701456011423138886839871545817320609199119527, -2014757891679539778718620521335945610727782801, 337090013519535337847808634272061148775336003], ![-53260222136086583379953764214985661506503088474, 10027275984384068211144254277273198311648447521, -1677667878160004440870811887063884461952446798], ![265071524749280701657588278156093744988486594084, -49904886379766574498212140440857892582598194878, 8349608106224063770273442390209313849696000723]]]
  hmulB := by decide  
  f := ![![![-264839752874864687542961, 134671037092718959372489, 37751245916689364522635]], ![![-310684031784560583285059, 126455837157400087839048, 37951407592788905324547]], ![![-479842413337375717213449, 55565635089548495892803, 30536854361868196998754]]]
  g := ![![![1752769417048018881782310275931421999772010951, -2014757891679539778718620521335945610727782801, 337090013519535337847808634272061148775336003], ![-8723381977711076682323066103283285995968416117, 10027275984384068211144254277273198311648447521, -1677667878160004440870811887063884461952446798], ![43415518543914467961481826972480459071717426175, -49904886379766574498212140440857892582598194878, 8349608106224063770273442390209313849696000723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![264839752874864687542961, -134671037092718959372489, -37751245916689364522635]] ![![10701456011423138886839871545817320609199119527, -2014757891679539778718620521335945610727782801, 337090013519535337847808634272061148775336003]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1783688383452616819291728003163061391013881, -335814139965835416196382362666098668015034, 56185208877265793647165255967299826216074]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1783688383452616819291728003163061391013881, -335814139965835416196382362666098668015034, 56185208877265793647165255967299826216074]] 
 ![![109, 0, 0], ![0, 109, 0], ![41, 43, 1]] where
  M :=![![![1783688383452616819291728003163061391013881, -335814139965835416196382362666098668015034, 56185208877265793647165255967299826216074], ![-8877263002607995396252110442833372542139692, 1671317965698085231997397491228461738581733, -279628931088569622549217106698798841798960], ![44181371111994000362776302858410217004235680, -8318005140430856151153676229435774858541772, 1391689034609515609448180384529662896782773]]]
  hmulB := by decide  
  f := ![![![610105288158778171821, 253332800426792379506, 26270442772404754022]], ![![-4150729958039951135476, 557564402613968663777, 279603243199197133528]], ![![-1813251227584230650259, 272036492527163254125, 127864176670158141779]]]
  g := ![![![-4769772298305327708642637536662674163717, -25245670841176738926830168525321020140424, 56185208877265793647165255967299826216074], ![23738744697462010351062302126764953868052, 125645522958775954143245257608044146201257, -279628931088569622549217106698798841798960], ![-118145681715560913987147641351430841870257, -625326914024220434471792961139553022203679, 1391689034609515609448180384529662896782773]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [68, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 108], [0, 1]]
 g := ![![[95, 83], [36], [49, 104], [35, 80], [100], [80, 1]], ![[86, 26], [36], [85, 5], [4, 29], [100], [51, 108]]]
 h' := ![![[80, 108], [88, 65], [47, 6], [18, 70], [58, 25], [10, 10], [0, 1]], ![[0, 1], [56, 44], [91, 103], [59, 39], [96, 84], [47, 99], [80, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [76, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [68, 29, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6064, 353, 429]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-217, -166, 429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7523384309468103372299255980317898671770292586627537, 1416423886007556300611147831858497144904731115339107, -236982492464967297221547125288377287274685518403857]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7523384309468103372299255980317898671770292586627537, 1416423886007556300611147831858497144904731115339107, -236982492464967297221547125288377287274685518403857]] 
 ![![109, 0, 0], ![65, 1, 0], ![26, 0, 1]] where
  M :=![![![-7523384309468103372299255980317898671770292586627537, 1416423886007556300611147831858497144904731115339107, -236982492464967297221547125288377287274685518403857], ![37443233809464832961004445795563611389400311907809406, -7049419324538168777856161729741144097220921549819823, 1179441393542589003389600706570119857630045596935250], ![-186351740179729062535556911638078937505547204315769500, 35084351022379654954225244382423371674140220713938906, -5869977930995579774466561023171024239590875952884573]]]
  hmulB := by decide  
  f := ![![![-895947286535620615928454079, -140201980495036511191135869, 8000677750414225226435561]], ![![-545877804673218235056204897, -91973186919392865080781254, 3558190376443140860124873]], ![![-22080950608034998456120710, -42614274971992222979972024, -7670938745599096297786247]]]
  g := ![![![-857150386200643240222602199941489941481064143166690, 1416423886007556300611147831858497144904731115339107, -236982492464967297221547125288377287274685518403857], ![4265963428186591646179131558329494141379624102071389, -7049419324538168777856161729741144097220921549819823, 1179441393542589003389600706570119857630045596935250], ![-21231331471821298719486855136634417120140355742631188, 35084351022379654954225244382423371674140220713938906, -5869977930995579774466561023171024239590875952884573]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1783688383452616819291728003163061391013881, -335814139965835416196382362666098668015034, 56185208877265793647165255967299826216074]] ![![-7523384309468103372299255980317898671770292586627537, 1416423886007556300611147831858497144904731115339107, -236982492464967297221547125288377287274685518403857]]
  ![![109, 0, 0]] where
 M := ![![![-36463552002953109420861126925223587732693479447844427335587611387133503877961922068644737393901, 6864975109760531878517719126365664900253250890428857445307338541415651354740848470579605538293, -1148581952261947564747074835818205856837008988206986890928312255499941464917970536245254713919]]]
 hmul := by decide  
 g := ![![![![-334528000027092746980377311240583373694435591264627773720987260432417466770292863015089333889, 62981423025325980536859808498767567892231659545218875645021454508400471144411453858528491177, -10537449103320619860064906750625741805844119157862265054388185830274692338696977396745456091]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [89, 31, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 44, 48], [102, 68, 65], [0, 1]]
 g := ![![[10, 109, 41], [102, 109], [14, 91], [87, 69], [10, 67, 9], [1]], ![[110, 44, 6, 58], [47, 105], [108, 26], [58, 51], [77, 101, 111, 6], [32, 54, 53, 78]], ![[37, 95, 105, 108], [20, 57], [97, 61], [23, 15], [13, 58, 80, 70], [56, 12, 41, 35]]]
 h' := ![![[14, 44, 48], [26, 79, 70], [8, 32, 83], [24, 16, 59], [14, 66, 71], [24, 82, 3], [0, 1]], ![[102, 68, 65], [23, 55, 77], [108, 33, 61], [51, 37, 34], [44, 75, 86], [9, 73, 72], [14, 44, 48]], ![[0, 1], [59, 92, 79], [12, 48, 82], [82, 60, 20], [35, 85, 69], [13, 71, 38], [102, 68, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 6], []]
 b := ![[], [48, 108, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [89, 31, 110, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60681, -14012, -678]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![537, -124, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [19, 75, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 69, 11], [16, 57, 116], [0, 1]]
 g := ![![[88, 101, 103], [55, 52, 74], [2, 57, 104], [77, 89, 38], [53, 117, 25], [1]], ![[2, 35, 1, 61], [13, 20, 90, 84], [121, 10, 75, 21], [31, 17, 47, 31], [103, 77, 123, 41], [35, 123, 104, 61]], ![[32, 68, 43, 86], [22, 28, 56, 24], [17, 93, 34, 24], [121, 56, 124, 55], [121, 37, 120, 12], [77, 116, 41, 66]]]
 h' := ![![[106, 69, 11], [98, 14, 22], [89, 75, 57], [61, 108, 55], [9, 5, 66], [108, 52, 122], [0, 1]], ![[16, 57, 116], [109, 67, 11], [72, 46, 10], [16, 61, 5], [57, 61, 7], [107, 92, 33], [106, 69, 11]], ![[0, 1], [61, 46, 94], [99, 6, 60], [57, 85, 67], [68, 61, 54], [93, 110, 99], [16, 57, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 88], []]
 b := ![[], [17, 60, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [19, 75, 5, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![197993, -2159, -4318]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1559, -17, -34]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [37, 30, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 66, 49], [121, 64, 82], [0, 1]]
 g := ![![[0, 20, 64], [111, 58, 1], [22, 39], [130, 64], [3, 53], [121, 1], []], ![[64, 48, 106, 94], [76, 100, 84, 89], [63, 89], [15, 53], [42, 123], [1, 35], [12, 43]], ![[68, 100, 66, 68], [48, 126, 2, 98], [129, 25], [21, 58], [108, 65], [49, 33], [110, 43]]]
 h' := ![![[0, 66, 49], [85, 74, 8], [21, 97, 130], [7, 101, 63], [25, 130, 8], [108, 1, 70], [0, 0, 1], [0, 1]], ![[121, 64, 82], [70, 18, 77], [72, 100, 104], [69, 81, 73], [10, 46, 70], [75, 129, 75], [80, 14, 64], [0, 66, 49]], ![[0, 1], [73, 39, 46], [8, 65, 28], [14, 80, 126], [108, 86, 53], [49, 1, 117], [91, 117, 66], [121, 64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 122], []]
 b := ![[], [111, 117, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [37, 30, 10, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![338897, -81220, 16244]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2587, -620, 124]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35725167, 27358213, 4054729]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![35725167, 27358213, 4054729]] 
 ![![137, 0, 0], ![0, 137, 0], ![99, 32, 1]] where
  M :=![![![35725167, 27358213, 4054729], ![-640647182, 27615709, 31412942], ![-4963244836, -703473066, 59028651]]]
  hmulB := by decide  
  f := ![![![-173199099777363, 32608109843721, -5455676949305]], ![![861996957990190, -162287745878753, 27152432894416]], ![![44869396937295, -8447539426207, 1413361471940]]]
  g := ![![![-2669292, -747395, 4054729], ![-27376120, -7135755, 31412942], ![-78883805, -18922554, 59028651]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [5, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 136], [0, 1]]
 g := ![![[15, 9], [18], [9], [129, 34], [32], [8], [1]], ![[25, 128], [18], [9], [45, 103], [32], [8], [1]]]
 h' := ![![[62, 136], [22, 134], [48, 44], [40, 134], [65, 87], [122, 13], [132, 62], [0, 1]], ![[0, 1], [110, 3], [36, 93], [128, 3], [116, 50], [106, 124], [3, 75], [62, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [109, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [5, 75, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1307, -257, 99]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, -25, 99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173199099777363, -32608109843721, 5455676949305]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![173199099777363, -32608109843721, 5455676949305]] 
 ![![137, 0, 0], ![104, 1, 0], ![7, 0, 1]] where
  M :=![![![173199099777363, -32608109843721, 5455676949305], ![-861996957990190, 162287745878753, -27152432894416], ![4290084397317728, -807692092201358, 135135312984337]]]
  hmulB := by decide  
  f := ![![![-35725167, -27358213, -4054729]], ![![-22443578, -20969853, -3307334]], ![![34402691, 3736975, -638042]]]
  g := ![![![25739071422476, -32608109843721, 5455676949305], ![-128101135030070, 162287745878753, -27152432894416], ![637548283177873, -807692092201358, 135135312984337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![35725167, 27358213, 4054729]] ![![173199099777363, -32608109843721, 5455676949305]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB234I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB234I2 : PrimesBelowBoundCertificateInterval O 79 137 234 where
  m := 11
  g := ![3, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB234I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
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
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I97N1, I101N1, I103N1, I107N1, I109N1, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N1], [I103N1], [I107N1], [I109N1], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
