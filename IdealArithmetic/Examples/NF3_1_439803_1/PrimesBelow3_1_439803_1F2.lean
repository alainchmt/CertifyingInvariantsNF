
import IdealArithmetic.Examples.NF3_1_439803_1.RI3_1_439803_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6325018164977308326, -2117691817343618673, 8102011140398522921]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-6325018164977308326, -2117691817343618673, 8102011140398522921]] 
 ![![83, 0, 0], ![0, 83, 0], ![3, 26, 1]] where
  M :=![![![-6325018164977308326, -2117691817343618673, 8102011140398522921], ![619619474175999027571, -174349560296002670994, -8839523398350426463], ![-49634113969879316927, 101185606147005652580, -178584943930689908340]]]
  hmulB := by decide  
  f := ![![![385911313047166308747048768596574131500, 5320711250460555453778901990498919920, 17244595978454238417188198306379891531]], ![![1338475312841897469031049073572249487727, 18454086249166746532317702172097489429, 59810285982138682047419414230371250891]], ![![441074833530297050949759427087059570972, 6081272431556928681838041069761607317, 19709599183386220553305359892311897916]]]
  g := ![![![-369048814291239483, -2563493752622954393, 8102011140398522921], ![7784795715313859120, 668410217603715868, -8839523398350426463], ![5856876118339643471, 57161375281264376740, -178584943930689908340]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [53, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 82], [0, 1]]
 g := ![![[82, 61], [46, 59], [17], [75], [1, 70], [1]], ![[78, 22], [19, 24], [17], [75], [59, 13], [1]]]
 h' := ![![[53, 82], [52, 12], [28, 68], [79, 73], [30, 65], [30, 53], [0, 1]], ![[0, 1], [24, 71], [63, 15], [47, 10], [72, 18], [17, 30], [53, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [61, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [53, 30, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142, 1535, -3328]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![122, 1061, -3328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-385911313047166308747048768596574131500, -5320711250460555453778901990498919920, -17244595978454238417188198306379891531]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-385911313047166308747048768596574131500, -5320711250460555453778901990498919920, -17244595978454238417188198306379891531]] 
 ![![83, 0, 0], ![40, 1, 0], ![75, 0, 1]] where
  M :=![![![-385911313047166308747048768596574131500, -5320711250460555453778901990498919920, -17244595978454238417188198306379891531], ![-1338475312841897469031049073572249487727, -18454086249166746532317702172097489429, -59810285982138682047419414230371250891], ![-651119109983822107781610229557735315274, -8977235589508004390960446344181922397, -29095508750087857439875506153095329269]]]
  hmulB := by decide  
  f := ![![![6325018164977308326, 2117691817343618673, -8102011140398522921]], ![![-4417093344300080657, 3121171481804185758, -3798083400211933619]], ![![6313379233050330619, 694473254864647565, -5169468573484329045]]]
  g := ![![![13497130546449684225219544385564753375, -5320711250460555453778901990498919920, -17244595978454238417188198306379891531], ![46812766093797271636362832296258962726, -18454086249166746532317702172097489429, -59810285982138682047419414230371250891], ![22772692407868522600571934767369774407, -8977235589508004390960446344181922397, -29095508750087857439875506153095329269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-6325018164977308326, -2117691817343618673, 8102011140398522921]] ![![-385911313047166308747048768596574131500, -5320711250460555453778901990498919920, -17244595978454238417188198306379891531]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187551803412412884195675569160, -2585850574270743397337890924, -8380824727162747275467185765]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-187551803412412884195675569160, -2585850574270743397337890924, -8380824727162747275467185765]] 
 ![![89, 0, 0], ![0, 89, 0], ![28, 80, 1]] where
  M :=![![![-187551803412412884195675569160, -2585850574270743397337890924, -8380824727162747275467185765], ![-650495205140073027005649085753, -8968633567724448013526777171, -29067629321328694454170313157], ![-316442040399125703451558201858, -4362911030453619584174590951, -14140334716265934808202559019]]]
  hmulB := by decide  
  f := ![![![55468495045922, -23861830455831, 16176074495323]], ![![1197834075228209, -260367238900030, -174718569151325]], ![![1076055595251439, -234642465210404, -155422992652232]]]
  g := ![![![529340325260045387836018340, 7504271096615157737528505284, -8380824727162747275467185765], ![1835937256821690086641794187, 26027434967849113576630317701, -29067629321328694454170313157], ![893116086026072709866443266, 12661391755851923203056518321, -14140334716265934808202559019]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [49, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 88], [0, 1]]
 g := ![![[33, 20], [32], [2], [61, 47], [53, 47], [1]], ![[0, 69], [32], [2], [68, 42], [60, 42], [1]]]
 h' := ![![[74, 88], [36, 38], [25, 78], [37, 64], [73, 15], [40, 74], [0, 1]], ![[0, 1], [0, 51], [12, 11], [56, 25], [26, 74], [87, 15], [74, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [67, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [49, 15, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3519, 2749, -3282]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![993, 2981, -3282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55468495045922, -23861830455831, 16176074495323]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![55468495045922, -23861830455831, 16176074495323]] 
 ![![89, 0, 0], ![71, 1, 0], ![2, 0, 1]] where
  M :=![![![55468495045922, -23861830455831, 16176074495323], ![1197834075228209, -260367238900030, -174718569151325], ![-1610895902164465, 614330961039712, -308090899811692]]]
  hmulB := by decide  
  f := ![![![-187551803412412884195675569160, -2585850574270743397337890924, -8380824727162747275467185765]], ![![-156928912892375143875265331417, -2163640722931991339601314975, -7012429044380716303509443848]], ![![-7770175811505072717336060002, -107130473921293330099442391, -347213305287544150102662141]]]
  g := ![![![19295576499093, -23861830455831, 16176074495323], ![225093766016101, -260367238900030, -174718569151325], ![-501260812768097, 614330961039712, -308090899811692]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-187551803412412884195675569160, -2585850574270743397337890924, -8380824727162747275467185765]] ![![55468495045922, -23861830455831, 16176074495323]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10929840935023187846020, -150694021301247812084, -488404160906806991341]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-10929840935023187846020, -150694021301247812084, -488404160906806991341]] 
 ![![97, 0, 0], ![0, 97, 0], ![68, 41, 1]] where
  M :=![![![-10929840935023187846020, -150694021301247812084, -488404160906806991341], ![-37908508432426633957425, -522659534678993215775, -1693956331316789488013], ![-18441097892891379409242, -254254679021444885623, -824047577281488839943]]]
  hmulB := by decide  
  f := ![![![24079142642, -5695661023, -2563143761]], ![![-208753391643, 83600822646, -48128431945]], ![![-76246982156, 32391707774, -21395360669]]]
  g := ![![![229707649552986469744, 204885325524513802401, -488404160906806991341], ![796706413372320115747, 710613918034117276214, -1693956331316789488013], ![387568426414947027906, 345687587520820593320, -824047577281488839943]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [53, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 96], [0, 1]]
 g := ![![[55, 11], [96], [16], [66], [8], [92, 1]], ![[0, 86], [96], [16], [66], [8], [87, 96]]]
 h' := ![![[92, 96], [88, 37], [36, 22], [60, 93], [58, 58], [71, 69], [0, 1]], ![[0, 1], [0, 60], [23, 75], [80, 4], [59, 39], [17, 28], [92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [27, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [53, 5, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![511595, 277018, -782620]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![553915, 333654, -782620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24079142642, -5695661023, -2563143761]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![24079142642, -5695661023, -2563143761]] 
 ![![97, 0, 0], ![59, 1, 0], ![9, 0, 1]] where
  M :=![![![24079142642, -5695661023, -2563143761], ![-208753391643, 83600822646, -48128431945], ![-474449911425, 101666875156, 72209500600]]]
  hmulB := by decide  
  f := ![![![-10929840935023187846020, -150694021301247812084, -488404160906806991341]], ![![-7038856944317471307965, -97047492695387774523, -314534039431117546156]], ![![-1204223364001031649726, -16603101760130672107, -53811185829306719196]]]
  g := ![![![3950427184, -5695661023, -2563143761], ![-48536557116, 83600822646, -48128431945], ![-73429701557, 101666875156, 72209500600]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-10929840935023187846020, -150694021301247812084, -488404160906806991341]] ![![24079142642, -5695661023, -2563143761]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-273137058984921484103931, 45281892647626349670412, 68801521810994815285980]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-273137058984921484103931, 45281892647626349670412, 68801521810994815285980]] 
 ![![101, 0, 0], ![9, 1, 0], ![67, 0, 1]] where
  M :=![![![-273137058984921484103931, 45281892647626349670412, 68801521810994815285980], ![5388280964741853476361284, -1763250909663438954779923, 431056662992005612649276], ![4449927039221156338625444, -469309092923189636076792, -1672687124368186255439099]]]
  hmulB := by decide  
  f := ![![![3151665905131801464216363535908808781273373611969, 43453259005854010489151845364416535142267262628, 140833407458113592134845725571517591547957801252]], ![![389070020182897700923848479038762046048887601281, 5364261589685624884136812493289818216875226601, 17385744026019485200610614045846615808096199144]], ![![2143358260313812348515335536207440671613287331107, 29551324420555243836088167977859245122574244452, 95776791160503769434736819381812223045759403289]]]
  g := ![![![-52379960932180309458399, 45281892647626349670412, 68801521810994815285980], ![-75477794740114574040801, -1763250909663438954779923, 431056662992005612649276], ![1195482635724736061165705, -469309092923189636076792, -1672687124368186255439099]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17001874428018590, -4619861614283246, -579993674774859]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![17001874428018590, -4619861614283246, -579993674774859]] 
 ![![101, 0, 0], ![15, 1, 0], ![75, 0, 1]] where
  M :=![![![17001874428018590, -4619861614283246, -579993674774859], ![-53899236186230635, 33801603212573875, -37538886589040827], ![-363849255746657968, 92957138176524153, 24561879984007383]]]
  hmulB := by decide  
  f := ![![![-4319738389024615517486953501513656, -59557934345191117693714866535791, -193029177256184250428272766293067]], ![![-789885528245403982976918170894481, -10890462846311107982230035058023, -35296339711489870776258249435400]], ![![-3279888600029826330494389862028545, -45221115796372377311470417395883, -146563088071324318399083146018565]]]
  g := ![![![1285141824261205, -4619861614283246, -579993674774859], ![22321714948546765, 33801603212573875, -37538886589040827], ![-35647003239555188, 92957138176524153, 24561879984007383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8730, 1243, 2619]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-8730, 1243, 2619]] 
 ![![101, 0, 0], ![77, 1, 0], ![1, 0, 1]] where
  M :=![![![-8730, 1243, 2619], ![204149, -64972, 12563], ![132377, -7770, -62486]]]
  hmulB := by decide  
  f := ![![![4157454902, 57320468, 185777477]], ![![3312312219, 45668153, 148011950]], ![![110614016, 1525079, 4942830]]]
  g := ![![![-1060, 1243, 2619], ![51430, -64972, 12563], ![7853, -7770, -62486]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-273137058984921484103931, 45281892647626349670412, 68801521810994815285980]] ![![17001874428018590, -4619861614283246, -579993674774859]]
  ![![-32117883910441813739945811385515993237550, 9188048551971875024583533237060660001466, 148480655360215772734210549446696350345]] where
 M := ![![![-32117883910441813739945811385515993237550, 9188048551971875024583533237060660001466, 148480655360215772734210549446696350345]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-32117883910441813739945811385515993237550, 9188048551971875024583533237060660001466, 148480655360215772734210549446696350345]] ![![-8730, 1243, 2619]]
  ![![101, 0, 0]] where
 M := ![![![2175775474089282631690667250112356622372713999, -638042114911544715130138780999702411851704252, 22034753766137112973854967645800417161616238]]]
 hmul := by decide  
 g := ![![![![21542331426626560709808586634775808142304099, -6317248662490541733961770108907944671799052, 218165878872644682909455125205944724372438]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [102, 47, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 80, 88], [34, 22, 15], [0, 1]]
 g := ![![[50, 29, 7], [49, 67, 68], [45, 43, 1], [19, 19], [77, 52], [1]], ![[85, 82, 37, 89], [84, 34, 75, 21], [88, 73, 93, 5], [8, 30], [69, 72], [77, 57, 87, 24]], ![[70, 13, 30, 13], [78, 27, 91, 76], [37, 101, 85, 7], [9, 26], [20, 33], [52, 81, 62, 79]]]
 h' := ![![[50, 80, 88], [49, 98, 25], [45, 46, 45], [26, 72, 102], [78, 47, 15], [1, 56, 84], [0, 1]], ![[34, 22, 15], [72, 33, 7], [76, 51, 94], [76, 20, 31], [58, 44, 37], [35, 68, 81], [50, 80, 88]], ![[0, 1], [101, 75, 71], [31, 6, 67], [92, 11, 73], [17, 12, 51], [10, 82, 41], [34, 22, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 84], []]
 b := ![[], [5, 44, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [102, 47, 19, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5398951, 2598793, -2143842]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52417, 25231, -20814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128973111132217224, -295342912002790924, 530681727161019491]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![128973111132217224, -295342912002790924, 530681727161019491]] 
 ![![107, 0, 0], ![0, 107, 0], ![48, 11, 1]] where
  M :=![![![128973111132217224, -295342912002790924, 530681727161019491], ![40271807167392918959, -10720000247246401163, -1832061568861307901], ![-15311860043960628274, 9916973242185745841, -11310686071251983011]]]
  hmulB := by decide  
  f := ![![![-1302981897540019741679030853153250762, -17964724554577377831274065685422381, -58224249019543705525785967820003351]], ![![-4519196623614020081148067653511102789, -62307943575024547806251463247758010, -201942045456162728175978493303382399]], ![![-1069651562791133069753190016329305958, -14747707340520235196202501345530522, -47797792949907169893853172675850187]]]
  g := ![![![-236857474697165592, -57316279539943975, 530681727161019491], ![1198231424978838301, 88155859908672764, -1832061568861307901], ![4930851134356397722, 1255462803980911766, -11310686071251983011]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [9, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 106], [0, 1]]
 g := ![![[106, 12], [36, 57], [52], [47, 9], [48], [9, 1]], ![[0, 95], [14, 50], [52], [21, 98], [48], [18, 106]]]
 h' := ![![[9, 106], [104, 36], [92, 48], [5, 65], [30, 3], [26, 72], [0, 1]], ![[0, 1], [0, 71], [96, 59], [55, 42], [57, 104], [32, 35], [9, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [43, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [9, 98, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-106, 1603, -4144]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1858, 441, -4144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1302981897540019741679030853153250762, 17964724554577377831274065685422381, 58224249019543705525785967820003351]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1302981897540019741679030853153250762, 17964724554577377831274065685422381, 58224249019543705525785967820003351]] 
 ![![107, 0, 0], ![18, 1, 0], ![69, 0, 1]] where
  M :=![![![1302981897540019741679030853153250762, 17964724554577377831274065685422381, 58224249019543705525785967820003351], ![4519196623614020081148067653511102789, 62307943575024547806251463247758010, 201942045456162728175978493303382399], ![2198423276976069970369106607257570251, 30310527490681004223746395346153456, 98237392684179303468799594618602772]]]
  hmulB := by decide  
  f := ![![![-128973111132217224, 295342912002790924, -530681727161019491]], ![![-398068440820306813, 149870772554174185, -72151490841467691]], ![![59931919400351774, 97772782112213345, -236507972923909924]]]
  g := ![![![-28391180624213913463206860829575545, 17964724554577377831274065685422381, 58224249019543705525785967820003351], ![-98470537357118224518756773111046046, 62307943575024547806251463247758010, 201942045456162728175978493303382399], ![-47902301991257570514070098482773675, 30310527490681004223746395346153456, 98237392684179303468799594618602772]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![128973111132217224, -295342912002790924, 530681727161019491]] ![![1302981897540019741679030853153250762, 17964724554577377831274065685422381, 58224249019543705525785967820003351]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1187084, -623697, 578533]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1187084, -623697, 578533]] 
 ![![109, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![1187084, -623697, 578533], ![43299647, -10338412, -4411043], ![-39925207, 17147368, -11585806]]]
  hmulB := by decide  
  f := ![![![195416613364896, 2694285806362, 8732266795567]], ![![31317483504403, 431786478355, 1399433838389]], ![![60394893301876, 832688178339, 2698769118555]]]
  g := ![![![-78846, -623697, 578533], ![3020099, -10338412, -4411043], ![832637, 17147368, -11585806]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -10, 17]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![6, -10, 17]] 
 ![![109, 0, 0], ![41, 1, 0], ![95, 0, 1]] where
  M :=![![![6, -10, 17], ![1289, -341, -63], ![-532, 329, -361]]]
  hmulB := by decide  
  f := ![![![-143828, -1983, -6427]], ![![-58677, -809, -2622]], ![![-127581, -1759, -5701]]]
  g := ![![![-11, -10, 17], ![195, -341, -63], ![186, 329, -361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-289628092854443689, -3993216575933154, -12942143120522298]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-289628092854443689, -3993216575933154, -12942143120522298]] 
 ![![109, 0, 0], ![54, 1, 0], ![24, 0, 1]] where
  M :=![![![-289628092854443689, -3993216575933154, -12942143120522298], ![-1004531453432083254, -13849870747542277, -44887875727987530], ![-488667680034165030, -6737453749059852, -21836303899408585]]]
  hmulB := by decide  
  f := ![![![-1104602485, 391147194, -149377074]], ![![-645580500, 208835939, -46665702]], ![![13913718, 1172496, -10656757]]]
  g := ![![![2170798505857631, -3993216575933154, -12942143120522298], ![7529087930338536, -13849870747542277, -44887875727987530], ![3662624917439202, -6737453749059852, -21836303899408585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1187084, -623697, 578533]] ![![6, -10, 17]]
  ![![-1104602485, 391147194, -149377074]] where
 M := ![![![-1104602485, 391147194, -149377074]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-1104602485, 391147194, -149377074]] ![![-289628092854443689, -3993216575933154, -12942143120522298]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [100, 67, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 27, 60], [12, 85, 53], [0, 1]]
 g := ![![[36, 41, 49], [66, 98], [97, 56], [23, 56], [6, 7, 106], [1]], ![[90, 109, 44, 111], [44, 72], [23, 62], [89, 41], [4, 97, 63, 22], [74, 111, 74, 57]], ![[10, 89, 53, 60], [78, 112], [89, 26], [47, 85], [13, 20, 65, 14], [49, 46, 87, 56]]]
 h' := ![![[16, 27, 60], [18, 26, 7], [105, 70, 18], [55, 87, 100], [78, 84, 13], [13, 46, 28], [0, 1]], ![[12, 85, 53], [14, 92, 8], [32, 47, 80], [80, 108, 47], [77, 102, 43], [86, 45, 55], [16, 27, 60]], ![[0, 1], [102, 108, 98], [52, 109, 15], [5, 31, 79], [33, 40, 57], [105, 22, 30], [12, 85, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 30], []]
 b := ![[], [77, 90, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [100, 67, 85, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211772509, -195205579, 279821222]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1874093, -1727483, 2476294]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-210567049606410634086704, 44125959003372050119842, 34093147438326821211183]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-210567049606410634086704, 44125959003372050119842, 34093147438326821211183]] 
 ![![127, 0, 0], ![0, 127, 0], ![39, 105, 1]] where
  M :=![![![-210567049606410634086704, 44125959003372050119842, 34093147438326821211183], ![2713424270757909333500775, -970649104814645929641389, 387100819465303222169919], ![3875002907396223356184396, -687993107002525304038401, -882397186807901829401705]]]
  hmulB := by decide  
  f := ![![![8841108149395349584009868624648689169543293132, 121895839812493294254372879055822967310602301, 395068330167113097053593038642157684008377055]], ![![30664053102492695061635409733557787603266237837, 422777376073481251630041934107554838056772676, 1370235048667059451088576071088741422493195463]], ![![28184612046268135293420786713489410645780921740, 388592345791418916512663513187347836185910329, 1259440268049268669208892942232922833155828394]]]
  g := ![![![-12127557477961863474983, -27839799385991686433499, 34093147438326821211183], ![-97507934554243435678158, -327686890934421135885692, 387100819465303222169919], ![301484198369325942542133, 724123712660056431363312, -882397186807901829401705]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [27, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 126], [0, 1]]
 g := ![![[89, 16], [75, 115], [100, 73], [94, 41], [27, 122], [10, 1]], ![[122, 111], [82, 12], [68, 54], [123, 86], [104, 5], [20, 126]]]
 h' := ![![[10, 126], [7, 4], [94, 49], [2, 33], [33, 26], [111, 73], [0, 1]], ![[0, 1], [47, 123], [76, 78], [78, 94], [39, 101], [79, 54], [10, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [94, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [27, 117, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![197, 81, 106]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -87, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2378839230333479393670, -614679559553450722679, -146344276606543411133]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![2378839230333479393670, -614679559553450722679, -146344276606543411133]] 
 ![![127, 0, 0], ![48, 1, 0], ![4, 0, 1]] where
  M :=![![![2378839230333479393670, -614679559553450722679, -146344276606543411133], ![-12497868417810744102599, 6066748598624341750142, -5063780753034149192565], ![-49379145958107313402145, 11883860814376661298328, 4837389479517440304784]]]
  hmulB := by decide  
  f := ![![![89524491509439832325596565642435238239810648, 1234309420485476077889331073603297151510712, 4000436457969712133777880574995879450812521]], ![![36280927705179139669963075726447092500208635, 500219438227505930528028614384856188139773, 1621227258302359867545124383965547010251175]], ![![4009022849029267379313032151867221621550730, 55273976830983398522256187194607122677209, 179144733420788993143794700323689643523689]]]
  g := ![![![255660119648230612022, -614679559553450722679, -146344276606543411133], ![-2231863607398760246765, 6066748598624341750142, -5063780753034149192565], ![-5032708842253990684575, 11883860814376661298328, 4837389479517440304784]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-210567049606410634086704, 44125959003372050119842, 34093147438326821211183]] ![![2378839230333479393670, -614679559553450722679, -146344276606543411133]]
  ![![127, 0, 0]] where
 M := ![![![-2735876091181573210145690502616527634072620573, 802290580136298800213144803831308973318479604, -27707066616825874729500800901154979995299626]]]
 hmul := by decide  
 g := ![![![![-21542331426626560709808586634775808142304099, 6317248662490541733961770108907944671799052, -218165878872644682909455125205944724372438]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3080062599812669, -1206056650393568, 653714571962082]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3080062599812669, -1206056650393568, 653714571962082]] 
 ![![131, 0, 0], ![0, 131, 0], ![6, 124, 1]] where
  M :=![![![3080062599812669, -1206056650393568, 653714571962082], ![47923908740293178, -9441886760997485, -8994738631186462], ![-83714358072835588, 29903191661999502, -11854000061784621]]]
  hmulB := by decide  
  f := ![![![2907599385390743561137318365039, 40088217781244242531353795156, 129927200818124358139839777406]], ![![10084570898558064061830370450574, 139039950428887797669329244357, 450632943068078298390670138654]], ![![9716321842092778265058487367726, 133962755665574761679430517670, 434177591842304056732932615971]]]
  g := ![![![-6429197190533, -627989798272456, 653714571962082], ![777804126163450, 8442028271039113, -8994738631186462], ![-96109600779602, 11448848849796126, -11854000061784621]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [24, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 130], [0, 1]]
 g := ![![[130, 59], [23, 1], [41], [35], [46], [52], [1]], ![[105, 72], [47, 130], [41], [35], [46], [52], [1]]]
 h' := ![![[24, 130], [103, 37], [65, 1], [1, 98], [102, 67], [114, 96], [107, 24], [0, 1]], ![[0, 1], [74, 94], [89, 130], [126, 33], [7, 64], [60, 35], [28, 107], [24, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [59, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [24, 107, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32, 4242, -6108]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![280, 5814, -6108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2907599385390743561137318365039, 40088217781244242531353795156, 129927200818124358139839777406]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2907599385390743561137318365039, 40088217781244242531353795156, 129927200818124358139839777406]] 
 ![![131, 0, 0], ![55, 1, 0], ![22, 0, 1]] where
  M :=![![![2907599385390743561137318365039, 40088217781244242531353795156, 129927200818124358139839777406], ![10084570898558064061830370450574, 139039950428887797669329244357, 450632943068078298390670138654], ![4905773580609547688871999110696, 67637832320741413820448743566, 219216385991376282732036834669]]]
  hmulB := by decide  
  f := ![![![3080062599812669, -1206056650393568, 653714571962082]], ![![1658987417786183, -578435133836975, 205798189517008]], ![![-121778479976770, 25724773689626, 19295576499093]]]
  g := ![![![-16455351225774241657737522683, 40088217781244242531353795156, 129927200818124358139839777406], ![-57072909332278529576927336179, 139039950428887797669329244357, 450632943068078298390670138654], ![-27763875487339757949293833192, 67637832320741413820448743566, 219216385991376282732036834669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3080062599812669, -1206056650393568, 653714571962082]] ![![2907599385390743561137318365039, 40088217781244242531353795156, 129927200818124358139839777406]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![556, 8, 25]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![556, 8, 25]] 
 ![![137, 0, 0], ![0, 137, 0], ![88, 88, 1]] where
  M :=![![![556, 8, 25], ![1941, 23, 89], ![966, 7, 39]]]
  hmulB := by decide  
  f := ![![![2, -1, 1]], ![![75, -18, -7]], ![![49, -12, -4]]]
  g := ![![![-12, -16, 25], ![-43, -57, 89], ![-18, -25, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [115, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 136], [0, 1]]
 g := ![![[28, 56], [17], [15], [57, 18], [25], [103], [1]], ![[0, 81], [17], [15], [48, 119], [25], [103], [1]]]
 h' := ![![[68, 136], [98, 59], [86, 90], [21, 17], [102, 93], [10, 132], [22, 68], [0, 1]], ![[0, 1], [0, 78], [41, 47], [81, 120], [124, 44], [81, 5], [125, 69], [68, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [52, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [115, 69, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2945, 1575, -5610]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3625, 3615, -5610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 1]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![2, -1, 1]] 
 ![![137, 0, 0], ![117, 1, 0], ![119, 0, 1]] where
  M :=![![![2, -1, 1], ![75, -18, -7], ![-63, 28, -20]]]
  hmulB := by decide  
  f := ![![![556, 8, 25]], ![![489, 7, 22]], ![![490, 7, 22]]]
  g := ![![![0, -1, 1], ![22, -18, -7], ![-7, 28, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![556, 8, 25]] ![![2, -1, 1]]
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


lemma PB188I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB188I2 : PrimesBelowBoundCertificateInterval O 79 137 188 where
  m := 11
  g := ![2, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB188I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I107N1, I109N0, I109N1, I109N2, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
