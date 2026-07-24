
import IdealArithmetic.Examples.NF3_1_597915_1.RI3_1_597915_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [33, 39, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 78, 6], [78, 60, 133], [0, 1]]
 g := ![![[41, 119, 9], [79, 51, 64], [127, 118], [13, 46, 86], [112, 83], [115, 1], []], ![[100, 90, 26, 78], [10, 116, 132, 127], [120, 9], [31, 31, 88, 83], [104, 127], [91, 125], [72, 36]], ![[126, 63, 32, 93], [37, 138, 131, 110], [43, 71], [50, 68, 22, 104], [3, 137], [44, 107], [84, 36]]]
 h' := ![![[37, 78, 6], [34, 79, 3], [123, 21, 8], [127, 117, 37], [14, 24, 15], [97, 69, 120], [0, 0, 1], [0, 1]], ![[78, 60, 133], [75, 92, 98], [72, 0, 50], [1, 56, 3], [114, 17, 71], [99, 133, 108], [105, 108, 60], [37, 78, 6]], ![[0, 1], [8, 107, 38], [40, 118, 81], [25, 105, 99], [136, 98, 53], [97, 76, 50], [115, 31, 78], [78, 60, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 53], []]
 b := ![[], [6, 32, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [33, 39, 24, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7143627, -1567920, -558780]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51393, -11280, -4020]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![308, 62, 27]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![308, 62, 27]] 
 ![![149, 0, 0], ![38, 1, 0], ![29, 0, 1]] where
  M :=![![![308, 62, 27], ![4741, 953, 415], ![7254, 1459, 635]]]
  hmulB := by decide  
  f := ![![![-330, 23, -1]], ![![-85, 4, 1]], ![![-37, 7, -3]]]
  g := ![![![-19, 62, 27], ![-292, 953, 415], ![-447, 1459, 635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13063097783906, -72456694653, 602488585715]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-13063097783906, -72456694653, 602488585715]] 
 ![![149, 0, 0], ![114, 1, 0], ![121, 0, 1]] where
  M :=![![![-13063097783906, -72456694653, 602488585715], ![102880634767959, -3038161910710, -2387119314369], ![-87098679414323, 7805564976624, -1398444571362]]]
  hmulB := by decide  
  f := ![![![22881515946212563259397276, 4601437132176408892998774, 2003420648018363359876607]], ![![19867655187541779623464341, 3995354439108487119853397, 1739538181123822846243581]], ![![22195201468051067238021218, 4463420362151811259275033, 1943329498471504744718966]]]
  g := ![![![-521504385671, -72456694653, 602488585715], ![4953506910252, -3038161910710, -2387119314369], ![-5420948279293, 7805564976624, -1398444571362]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12064867371162173110381, -2426225991623530376392, -1056355027516881227864]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-12064867371162173110381, -2426225991623530376392, -1056355027516881227864]] 
 ![![149, 0, 0], ![146, 1, 0], ![112, 0, 1]] where
  M :=![![![-12064867371162173110381, -2426225991623530376392, -1056355027516881227864], ![-185489161688633750717528, -37301580813819745113245, -16240742850437599327544], ![-283896621155530422107896, -57091167270353234816624, -24856934919112325310621]]]
  hmulB := by decide  
  f := ![![![-3500893983689, -67553951704, 192916517432]], ![![-3209912114370, -69039275109, 181521009256]], ![![-2869620805880, -39065181264, 147475380235]]]
  g := ![![![3090442218038684291031, -2426225991623530376392, -1056355027516881227864], ![47513455277705101748330, -37301580813819745113245, -16240742850437599327544], ![72720741686286055677240, -57091167270353234816624, -24856934919112325310621]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![308, 62, 27]] ![![-13063097783906, -72456694653, 602488585715]]
  ![![3500893983689, 67553951704, -192916517432]] where
 M := ![![![3500893983689, 67553951704, -192916517432]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![3500893983689, 67553951704, -192916517432]] ![![-12064867371162173110381, -2426225991623530376392, -1056355027516881227864]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29650214385784, -3477178901854, 1011822875123]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![29650214385784, -3477178901854, 1011822875123]] 
 ![![151, 0, 0], ![40, 1, 0], ![125, 0, 1]] where
  M :=![![![29650214385784, -3477178901854, 1011822875123], ![166067353842325, 36419666557313, -30852899840201], ![-720063628732286, -43934698204673, 59306385718683]]]
  hmulB := by decide  
  f := ![![![-804405949375589800622919506, -161764780511106361337088503, -70430800658320154341208155]], ![![-294989632110056630065811601, -59321954453937787827273270, -25828197804282758949148409]], ![![-791252330183551084292697093, -159119608228158315397249601, -69279118560532271137388267]]]
  g := ![![![279864311719, -3477178901854, 1011822875123], ![16992670010430, 36419666557313, -30852899840201], ![-42224992817091, -43934698204673, 59306385718683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1764, 153, -25]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-1764, 153, -25]] 
 ![![151, 0, 0], ![129, 1, 0], ![99, 0, 1]] where
  M :=![![![-1764, 153, -25], ![-3969, -1730, 1299], ![29263, 2226, -2698]]]
  hmulB := by decide  
  f := ![![![1775966, 357144, 155497]], ![![1698039, 341473, 148674]], ![![1441130, 289809, 126180]]]
  g := ![![![-126, 153, -25], ![600, -1730, 1299], ![61, 2226, -2698]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58203778453421549514495281332851, -11704688974196829103383328456370, -5096106910939711493370054592400]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-58203778453421549514495281332851, -11704688974196829103383328456370, -5096106910939711493370054592400]] 
 ![![151, 0, 0], ![133, 1, 0], ![42, 0, 1]] where
  M :=![![![-58203778453421549514495281332851, -11704688974196829103383328456370, -5096106910939711493370054592400], ![-894843659719084323573045992213140, -179951662861987132211936194772761, -78349191060755498346956463873760], ![-1369584557631133551500662396581670, -275421316225441767158067402644290, -119915742838685580578376333219341]]]
  hmulB := by decide  
  f := ![![![-8893082320340101, 12804320021256170, -7988008870234800]], ![![-16709409439555443, 10574160859447069, -6198719158678640]], ![![18586373285361828, 4209501643712530, -3540229029592261]]]
  g := ![![![11341432750822679496404170173809, -11704688974196829103383328456370, -5096106910939711493370054592400], ![174366844539582352259514168180543, -179951662861987132211936194772761, -78349191060755498346956463873760], ![266873587414419972614662967882922, -275421316225441767158067402644290, -119915742838685580578376333219341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![29650214385784, -3477178901854, 1011822875123]] ![![-1764, 153, -25]]
  ![![-8893082320340101, 12804320021256170, -7988008870234800]] where
 M := ![![![-8893082320340101, 12804320021256170, -7988008870234800]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-8893082320340101, 12804320021256170, -7988008870234800]] ![![-58203778453421549514495281332851, -11704688974196829103383328456370, -5096106910939711493370054592400]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77019971862980018917722, 8147516883611343742468, -2050184073197178474701]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-77019971862980018917722, 8147516883611343742468, -2050184073197178474701]] 
 ![![157, 0, 0], ![0, 157, 0], ![51, 24, 1]] where
  M :=![![![-77019971862980018917722, 8147516883611343742468, -2050184073197178474701], ![-334286442749494831688935, -87430550456498021760235, 71330687288482285363847], ![1647448212173989910824952, 107755025923435166501441, -140416019904560441164445]]]
  hmulB := by decide  
  f := ![![![-29238279332862714807562816143486079957083064, -5879772324501508475986317498195546644710867, -2559995267170292577184715063013342175862673]], ![![-449518735335123047650558910771672605361938817, -90397515848262214047661924709299536880881106, -39358192794501190076336394796524346630098917]], ![![-82596200945092950755553331886724309891314361, -16609967053706688548845391776087173182289335, -7231816930759918672704505689021768862775233]]]
  g := ![![![175410292166089702497, 365298946753781064556, -2050184073197178474701], ![-25300327990204403727676, -11460936594777534206959, 71330687288482285363847], ![56106147944627849746571, 22151207029508826461453, -140416019904560441164445]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [121, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 156], [0, 1]]
 g := ![![[34, 109], [147], [20, 35], [126, 4], [92, 110], [82], [1]], ![[0, 48], [147], [156, 122], [155, 153], [26, 47], [82], [1]]]
 h' := ![![[125, 156], [97, 57], [92, 124], [140, 105], [15, 155], [9, 96], [36, 125], [0, 1]], ![[0, 1], [0, 100], [49, 33], [77, 52], [79, 2], [77, 61], [118, 32], [125, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [86, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [121, 32, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3691, 1911, 1787]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-604, -261, 1787]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241931324445693566, -2180969482566405, -8856474343171949]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![241931324445693566, -2180969482566405, -8856474343171949]] 
 ![![157, 0, 0], ![125, 1, 0], ![2, 0, 1]] where
  M :=![![![241931324445693566, -2180969482566405, -8856474343171949], ![-1518819051647536089, 84828352164071218, 9121667168984607], ![725257037034466421, -169923596351208120, 80201220373125750]]]
  hmulB := by decide  
  f := ![![![8353323855872402040740734403072340, 1679840385482351610226060835454630, 731386046788968096280407355536047]], ![![7468739979337124221509513247462521, 1501951949000164750232123862327247, 653935164280974016738969325216782]], ![![1358391616734999270645651971862526, 273170433286619121264339275201775, 118935730458558453706694944987041]]]
  g := ![![![3390225850018077, -2180969482566405, -8856474343171949], ![-77328703226079029, 84828352164071218, 9121667168984607], ![138887287517128853, -169923596351208120, 80201220373125750]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-77019971862980018917722, 8147516883611343742468, -2050184073197178474701]] ![![241931324445693566, -2180969482566405, -8856474343171949]]
  ![![157, 0, 0]] where
 M := ![![![-32495058094331917533502087913273513219425, 1207493290546614798423648193954705187554, 592017077322333845674070138021726919504]]]
 hmul := by decide  
 g := ![![![![-206974892320585461996828585434863141525, 7691040067175890435819415248119141322, 3770809409696393921490892598864502672]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [14, 77, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 35, 55], [0, 127, 108], [0, 1]]
 g := ![![[14, 56, 21], [89, 72, 40], [65, 119], [90, 71], [149, 95], [34, 130, 1], []], ![[80, 87, 82, 15], [151, 29, 151, 87], [128, 87], [101, 60], [69, 15], [32, 147, 60, 49], [32, 91]], ![[0, 66, 117, 139], [129, 34, 73, 101], [26, 113], [42, 64], [128, 132], [32, 105, 41, 107], [142, 91]]]
 h' := ![![[130, 35, 55], [58, 54, 99], [55, 9, 23], [98, 74, 49], [39, 90, 76], [13, 126, 101], [0, 0, 1], [0, 1]], ![[0, 127, 108], [121, 44, 58], [157, 87, 156], [51, 127, 24], [145, 65, 95], [123, 85, 34], [152, 146, 127], [130, 35, 55]], ![[0, 1], [150, 65, 6], [134, 67, 147], [160, 125, 90], [52, 8, 155], [41, 115, 28], [131, 17, 35], [0, 127, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144, 4], []]
 b := ![[], [66, 55, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [14, 77, 33, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-394484694989, -90606104699, -33819714004]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2420151503, -555865673, -207482908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [91, 113, 143, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 72, 116], [153, 94, 51], [0, 1]]
 g := ![![[84, 76, 32], [10, 27, 132], [123, 89, 12], [32, 32], [89, 11], [129, 24, 1], []], ![[99, 15, 104, 133], [154, 53, 139, 100], [36, 5, 157, 64], [115, 157], [69, 114], [48, 119, 69, 97], [137, 96]], ![[6, 82, 64, 166], [37, 164, 155, 143], [129, 118, 146, 106], [122, 154], [120, 96], [103, 56, 44, 23], [35, 96]]]
 h' := ![![[38, 72, 116], [92, 103, 115], [163, 95, 74], [160, 113, 124], [147, 97, 115], [118, 106, 126], [0, 0, 1], [0, 1]], ![[153, 94, 51], [50, 29, 46], [25, 132, 107], [155, 46, 48], [44, 98, 18], [12, 128, 92], [166, 126, 94], [38, 72, 116]], ![[0, 1], [104, 35, 6], [91, 107, 153], [18, 8, 162], [76, 139, 34], [108, 100, 116], [17, 41, 72], [153, 94, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 7], []]
 b := ![[], [89, 159, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [91, 113, 143, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7317773, -1211418, -225116]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43819, -7254, -1348]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-368058097375, -22782260410, 30526726522]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-368058097375, -22782260410, 30526726522]] 
 ![![173, 0, 0], ![0, 173, 0], ![143, 59, 1]] where
  M :=![![![-368058097375, -22782260410, 30526726522], ![5174505714442, 82549472269, -273838262846], ![-7681080618838, 70602470860, 280296487773]]]
  hmulB := by decide  
  f := ![![![245502804147127726789, 49370230613720006450, 21495314739239386754]], ![![3774439281637375147834, 759033846555357320957, 330475900692041891338]], ![![1523559011658525062419, 306385338532080195201, 133397174802850982373]]]
  g := ![![![-27360577977, -10542538296, 30526726522], ![256262296540, 93867092371, -273838262846], ![-276089470349, -95184337039, 280296487773]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [63, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 172], [0, 1]]
 g := ![![[33, 6], [10], [84, 21], [109, 113], [139], [5, 9], [1]], ![[15, 167], [10], [21, 152], [116, 60], [139], [151, 164], [1]]]
 h' := ![![[170, 172], [86, 122], [71, 23], [53, 114], [162, 74], [31, 100], [110, 170], [0, 1]], ![[0, 1], [66, 51], [2, 150], [57, 59], [113, 99], [77, 73], [119, 3], [170, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [47, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [63, 3, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2777, 4290, 2612]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2143, -866, 2612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245502804147127726789, -49370230613720006450, -21495314739239386754]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-245502804147127726789, -49370230613720006450, -21495314739239386754]] 
 ![![173, 0, 0], ![50, 1, 0], ![15, 0, 1]] where
  M :=![![![-245502804147127726789, -49370230613720006450, -21495314739239386754], ![-3774439281637375147834, -759033846555357320957, -330475900692041891338], ![-5776890407280437145454, -1161723641521830910960, -505803092351516055765]]]
  hmulB := by decide  
  f := ![![![368058097375, 22782260410, -30526726522]], ![![76464734996, 6107303747, -7239873198]], ![![76311861731, 1567233730, -4267036911]]]
  g := ![![![14713517038309036977, -49370230613720006450, -21495314739239386754], ![226210355817983348382, -759033846555357320957, -330475900692041891338], ![346221607249039590977, -1161723641521830910960, -505803092351516055765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-368058097375, -22782260410, 30526726522]] ![![-245502804147127726789, -49370230613720006450, -21495314739239386754]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [12, 125, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 109, 119], [173, 69, 60], [0, 1]]
 g := ![![[34, 18, 19], [150, 36, 76], [40, 85], [27, 29], [104, 84, 81], [147, 123, 1], []], ![[53, 7, 19, 160], [34, 89, 25, 160], [93, 52], [42, 101], [146, 95, 172, 120], [102, 8, 34, 24], [120, 20]], ![[106, 166, 29, 83], [15, 116, 76, 100], [112, 64], [147, 121], [169, 147, 73, 17], [18, 49, 109, 82], [0, 20]]]
 h' := ![![[129, 109, 119], [169, 124, 52], [137, 31, 75], [59, 71, 117], [5, 93, 108], [26, 18, 9], [0, 0, 1], [0, 1]], ![[173, 69, 60], [43, 137, 86], [43, 65, 93], [62, 56, 54], [108, 2, 82], [74, 118, 78], [165, 173, 69], [129, 109, 119]], ![[0, 1], [44, 97, 41], [145, 83, 11], [86, 52, 8], [113, 84, 168], [63, 43, 92], [36, 6, 109], [173, 69, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 121], []]
 b := ![[], [2, 1, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [12, 125, 56, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3648967089, 810001671, 309177571]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20385291, 4525149, 1727249]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9771513935810, -478957392320, -102328144473]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![9771513935810, -478957392320, -102328144473]] 
 ![![181, 0, 0], ![0, 181, 0], ![88, 153, 1]] where
  M :=![![![9771513935810, -478957392320, -102328144473], ![-18456027489523, 6595063302809, -3524674705141], ![-69213024172068, -9677197836535, 9264151367783]]]
  hmulB := by decide  
  f := ![![![-149108786111896920518652, -29985544085535157222915, -13055412132646509152717]], ![![-2292446562853623379560437, -461007424623493047783586, -200718116286341730325169]], ![![-2029693669771434534964474, -408168228057266991472848, -177712447756125705347743]]]
  g := ![![![103736964914, 83852202829, -102328144473], ![1611686997585, 3015857973422, -3524674705141], ![-4886510190812, -7884488160814, 9264151367783]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [176, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 180], [0, 1]]
 g := ![![[165, 36], [44], [32, 108], [12], [39, 33], [154, 65], [1]], ![[0, 145], [44], [80, 73], [12], [114, 148], [22, 116], [1]]]
 h' := ![![[101, 180], [118, 6], [160, 166], [75, 164], [14, 66], [46, 157], [5, 101], [0, 1]], ![[0, 1], [0, 175], [93, 15], [168, 17], [164, 115], [156, 24], [70, 80], [101, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [31, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [176, 80, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1019, 135, -63]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 54, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149108786111896920518652, 29985544085535157222915, 13055412132646509152717]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![149108786111896920518652, 29985544085535157222915, 13055412132646509152717]] 
 ![![181, 0, 0], ![46, 1, 0], ![171, 0, 1]] where
  M :=![![![149108786111896920518652, 29985544085535157222915, 13055412132646509152717], ![2292446562853623379560437, 461007424623493047783586, 200718116286341730325169], ![3508656934178344750181557, 705585431443795310080310, 307204984375575122751530]]]
  hmulB := by decide  
  f := ![![![-9771513935810, 478957392320, 102328144473]], ![![-2381401179877, 85287164331, 45479388679]], ![![-8849258888682, 505960839355, 45491499100]]]
  g := ![![![-19130948709973886059945, 29985544085535157222915, 13055412132646509152717], ![-294125374888350788420378, 461007424623493047783586, 200718116286341730325169], ![-450167542764970085657593, 705585431443795310080310, 307204984375575122751530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![9771513935810, -478957392320, -102328144473]] ![![149108786111896920518652, 29985544085535157222915, 13055412132646509152717]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6853, -1378, -600]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-6853, -1378, -600]] 
 ![![191, 0, 0], ![0, 191, 0], ![176, 143, 1]] where
  M :=![![![-6853, -1378, -600], ![-105356, -21187, -9224], ![-161238, -32426, -14119]]]
  hmulB := by decide  
  f := ![![![-219, 2, 8]], ![![1372, -77, -8]], ![![822, -55, 1]]]
  g := ![![![517, 442, -600], ![7948, 6795, -9224], ![12166, 10401, -14119]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [170, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 190], [0, 1]]
 g := ![![[114, 100], [185, 45], [13, 78], [150, 50], [167, 8], [94, 90], [1]], ![[0, 91], [0, 146], [138, 113], [93, 141], [28, 183], [106, 101], [1]]]
 h' := ![![[102, 190], [65, 181], [82, 149], [94, 101], [69, 97], [64, 77], [21, 102], [0, 1]], ![[0, 1], [0, 10], [0, 42], [82, 90], [31, 94], [87, 114], [111, 89], [102, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [185, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [170, 89, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5888, 12424, 9132]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8384, -6772, 9132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-219, 2, 8]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-219, 2, 8]] 
 ![![191, 0, 0], ![5, 1, 0], ![43, 0, 1]] where
  M :=![![![-219, 2, 8], ![1372, -77, -8], ![-650, 154, -73]]]
  hmulB := by decide  
  f := ![![![-6853, -1378, -600]], ![![-731, -147, -64]], ![![-2387, -480, -209]]]
  g := ![![![-3, 2, 8], ![11, -77, -8], ![9, 154, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-6853, -1378, -600]] ![![-219, 2, 8]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [185, 167, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 159, 123], [157, 33, 70], [0, 1]]
 g := ![![[181, 16, 166], [88, 191], [5, 59], [83, 175], [15, 147], [97, 54], [1]], ![[164, 156, 124, 91], [7, 112], [38, 168], [62, 65], [84, 49], [], [183, 42, 7, 154]], ![[18, 99, 30, 33], [55, 139], [163, 169], [84, 144], [187, 24], [82, 54], [2, 170, 154, 39]]]
 h' := ![![[97, 159, 123], [27, 30, 121], [148, 145, 34], [84, 26, 161], [112, 160, 102], [68, 89, 95], [8, 26, 61], [0, 1]], ![[157, 33, 70], [44, 174, 156], [48, 71, 43], [55, 97, 19], [157, 106, 79], [8, 111, 186], [89, 147], [97, 159, 123]], ![[0, 1], [191, 182, 109], [152, 170, 116], [44, 70, 13], [181, 120, 12], [187, 186, 105], [66, 20, 132], [157, 33, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 99], []]
 b := ![[], [177, 116, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [185, 167, 132, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180159710, -37342605, -12818095]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-933470, -193485, -66415]
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



lemma PB219I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB219I3 : PrimesBelowBoundCertificateInterval O 137 193 219 where
  m := 11
  g := ![1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB219I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N0, I149N1, I149N2, I151N0, I151N1, I151N2, I157N1, I173N1, I181N1, I191N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N0, I151N1, I151N2], [I157N1], [], [], [I173N1], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
