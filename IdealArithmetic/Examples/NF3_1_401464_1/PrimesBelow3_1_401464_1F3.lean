
import IdealArithmetic.Examples.NF3_1_401464_1.RI3_1_401464_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368537447730109, -14921439798278, -33821984053864]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![368537447730109, -14921439798278, -33821984053864]] 
 ![![139, 0, 0], ![19, 1, 0], ![98, 0, 1]] where
  M :=![![![368537447730109, -14921439798278, -33821984053864], ![4009894662611538, 605291336107157, -63664863650420], ![3906436331388514, 2235235073981378, 590369896308879]]]
  hmulB := by decide  
  f := ![![![499651719545905997291296425763, -66790916162347121796344634230, 21422125347983618247073881408]], ![![49477401717984289606737378185, -6613888956651616147976753917, 2121299817517828211142362300]], ![![399743839150324656681628824960, -53435735738824144122539685206, 17138663381655166445889748199]]]
  g := ![![![28536685188317, -14921439798278, -33821984053864], ![-9003482630815, 605291336107157, -63664863650420], ![-693663884262790, 2235235073981378, 590369896308879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40704203943240, -5441132226061, 1745156726078]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![40704203943240, -5441132226061, 1745156726078]] 
 ![![139, 0, 0], ![37, 1, 0], ![11, 0, 1]] where
  M :=![![![40704203943240, -5441132226061, 1745156726078], ![-213114782629343, 28488106860694, -9137107726044], ![537549861158345, -71856948160487, 23046974634633]]]
  hmulB := by decide  
  f := ![![![-62808126, -6309373, 2254552]], ![![-18694257, -2244869, 525570]], ![![-590725, -1203412, -432369]]]
  g := ![![![1603089009501, -5441132226061, 1745156726078], ![-8393284543083, 28488106860694, -9137107726044], ![21170792964859, -71856948160487, 23046974634633]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5416907960314620, -724104874021721, 232245135531228]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![5416907960314620, -724104874021721, 232245135531228]] 
 ![![139, 0, 0], ![82, 1, 0], ![44, 0, 1]] where
  M :=![![![5416907960314620, -724104874021721, 232245135531228], ![-28361276002237853, 3791192011596024, -1215964612512214], ![71537036470117435, -9562709420315317, 3067087137574303]]]
  hmulB := by decide  
  f := ![![![-474410566, 13216187, 41162822]], ![![-315013137, 2310626, 24769400]], ![![-180144237, -15138553, 7639065]]]
  g := ![![![392623896882890, -724104874021721, 232245135531228], ![-2055658834550895, 3791192011596024, -1215964612512214], ![5185089027933123, -9562709420315317, 3067087137574303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![368537447730109, -14921439798278, -33821984053864]] ![![40704203943240, -5441132226061, 1745156726078]]
  ![![-474410566, 13216187, 41162822]] where
 M := ![![![-474410566, 13216187, 41162822]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-474410566, 13216187, 41162822]] ![![5416907960314620, -724104874021721, 232245135531228]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2702025, 890818, 148568]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![2702025, 890818, 148568]] 
 ![![149, 0, 0], ![0, 149, 0], ![143, 66, 1]] where
  M :=![![![2702025, 890818, 148568], ![-16788774, 1662049, 1930204], ![-115367126, -15595510, 2552867]]]
  hmulB := by decide  
  f := ![![![-230506750527, 30812977214, -9882772960]], ![![1206862959454, -161327339807, 51743181468]], ![![292928593333, -39157213622, 12559054235]]]
  g := ![![![-124451, -59830, 148568], ![-1965154, -843835, 1930204], ![-3224343, -1235468, 2552867]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [84, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 148], [0, 1]]
 g := ![![[82, 63], [82], [36, 145], [29], [64, 19], [113], [1]], ![[26, 86], [82], [23, 4], [29], [14, 130], [113], [1]]]
 h' := ![![[115, 148], [114, 130], [105, 126], [92, 61], [137, 124], [97, 82], [65, 115], [0, 1]], ![[0, 1], [15, 19], [142, 23], [104, 88], [93, 25], [140, 67], [29, 34], [115, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [81, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [84, 34, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-676, -312, -86]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 36, -86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![230506750527, -30812977214, 9882772960]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![230506750527, -30812977214, 9882772960]] 
 ![![149, 0, 0], ![16, 1, 0], ![96, 0, 1]] where
  M :=![![![230506750527, -30812977214, 9882772960], ![-1206862959454, 161327339807, -51743181468], ![3044129591986, -406923855982, 130514362593]]]
  hmulB := by decide  
  f := ![![![-2702025, -890818, -148568]], ![![-177474, -106813, -28908]], ![![-966626, -469282, -112855]]]
  g := ![![![-1511622941, -30812977214, 9882772960], ![7914396138, 161327339807, -51743181468], ![-19962869270, -406923855982, 130514362593]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![2702025, 890818, 148568]] ![![230506750527, -30812977214, 9882772960]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27639559614320034578608832274542306462080113, 3694716613087999443836148520057577655011270, -1185021661006472191143482183626120818987798]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-27639559614320034578608832274542306462080113, 3694716613087999443836148520057577655011270, -1185021661006472191143482183626120818987798]] 
 ![![151, 0, 0], ![29, 1, 0], ![33, 0, 1]] where
  M :=![![![-27639559614320034578608832274542306462080113, 3694716613087999443836148520057577655011270, -1185021661006472191143482183626120818987798], ![144712294272858190189910528371565955114559232, -19344407987274729240604456989159460729165527, 6204411565169526696528814856489034491034742], ![-365014912314064185774462296318406129350109856, 48793348351791751935186337928042568011152384, -15649691374186729796768308469101883074154257]]]
  hmulB := by decide  
  f := ![![![10984948051431115426489, -5608183059562638865958, -3055196174614636302794]], ![![4480289107358155155859, -862688658632999718985, -681273187798439515336]], ![![8095062442290747822511, 309037082464195209014, -490452553298755412663]]]
  g := ![![![-633646533646744610212729982096358088945759, 3694716613087999443836148520057577655011270, -1185021661006472191143482183626120818987798], ![3317579763266430180013171462205643563286179, -19344407987274729240604456989159460729165527, 6204411565169526696528814856489034491034742], ![-8368094034224257672857694812922373908784361, 48793348351791751935186337928042568011152384, -15649691374186729796768308469101883074154257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11228834216605, -1501013797058, 481426330962]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![11228834216605, -1501013797058, 481426330962]] 
 ![![151, 0, 0], ![46, 1, 0], ![75, 0, 1]] where
  M :=![![![11228834216605, -1501013797058, 481426330962], ![-58790747181536, 7858849899871, -2520601263154], ![148290782999296, -19822762271200, 6357836102813]]]
  hmulB := by decide  
  f := ![![![-3927677, 4029754, 1895030]], ![![-2663258, 1113747, 643218]], ![![-5917241, 1024082, 854067]]]
  g := ![![![292506583173, -1501013797058, 481426330962], ![-1531475151252, 7858849899871, -2520601263154], ![3862914832871, -19822762271200, 6357836102813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13811398601204235129808, -1846237949298275123793, 592151493714171895116]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![13811398601204235129808, -1846237949298275123793, 592151493714171895116]] 
 ![![151, 0, 0], ![75, 1, 0], ![57, 0, 1]] where
  M :=![![![13811398601204235129808, -1846237949298275123793, 592151493714171895116], ![-72312265701284730642597, 9666338145205031863996, -3100324404882378352470], ![182396771862501910339059, -24381878458904903525757, 7820100195906756740203]]]
  hmulB := by decide  
  f := ![![![1931861398, 160156447167, 63348675174]], ![![-47903617839, 76624004455, 34005378858]], ![![-151917004299, 26601694188, 22049815015]]]
  g := ![![![784944434813689214521, -1846237949298275123793, 592151493714171895116], ![-4109729374260705657957, 9666338145205031863996, -3100324404882378352470], ![10366171821944930732313, -24381878458904903525757, 7820100195906756740203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-27639559614320034578608832274542306462080113, 3694716613087999443836148520057577655011270, -1185021661006472191143482183626120818987798]] ![![11228834216605, -1501013797058, 481426330962]]
  ![![-703302973018424114572548484511514855195883492505187377293, 94013986282873662980553933216064243298392253695563071324, -30153492635435623291230202911655224848377529631922580060]] where
 M := ![![![-703302973018424114572548484511514855195883492505187377293, 94013986282873662980553933216064243298392253695563071324, -30153492635435623291230202911655224848377529631922580060]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-703302973018424114572548484511514855195883492505187377293, 94013986282873662980553933216064243298392253695563071324, -30153492635435623291230202911655224848377529631922580060]] ![![13811398601204235129808, -1846237949298275123793, 592151493714171895116]]
  ![![151, 0, 0]] where
 M := ![![![-22011861770576723931363855257924610214323640889505617987356692638985577062801712, 2942434412978515242145635331762490846317240925035455028096447747356827092488473, -943739095745191208243063210152119540737668384623221281170490971713742625723448]]]
 hmul := by decide  
 g := ![![![![-145773919010441880340157981840560332545189674764937867465938361847586603064912, 19486320615751756570500896236837687723955237914142086278784422167926007235023, -6249927786391994756576577550676288349256082017372326365367489878898957786248]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![315378411261945861925165062, -42158191800389758424272657, 13521570313500365118134332]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![315378411261945861925165062, -42158191800389758424272657, 13521570313500365118134332]] 
 ![![157, 0, 0], ![0, 157, 0], ![131, 61, 1]] where
  M :=![![![315378411261945861925165062, -42158191800389758424272657, 13521570313500365118134332], ![-1651225059106933207482258165, 220727419067443306098224738, -70794813287279151730410982], ![4164965894495858250045983267, -556751587147794693472554317, 178569227267053547673952081]]]
  hmulB := by decide  
  f := ![![![-15019217500188, -1658932967911, 479587424294]], ![![-58729836458897, -18376329470246, -2838278511528]], ![![-34285595548194, -8642533716156, -830218465343]]]
  g := ![![![-9273549680296827825161990, -5522127267031286819302337, 13521570313500365118134332], ![48553474404628252670073761, 28912172163003003577409520, -70794813287279151730410982], ![-122468808136867238823195792, -72926588856293382812634594, 178569227267053547673952081]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [67, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 156], [0, 1]]
 g := ![![[133, 75], [120], [124, 113], [106, 148], [43, 121], [31], [1]], ![[0, 82], [120], [22, 44], [78, 9], [88, 36], [31], [1]]]
 h' := ![![[38, 156], [136, 46], [13, 80], [120, 120], [102, 73], [57, 11], [90, 38], [0, 1]], ![[0, 1], [0, 111], [70, 77], [127, 37], [50, 84], [4, 146], [121, 119], [38, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [27, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [67, 119, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1118, -1681, 428]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -177, 428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15019217500188, -1658932967911, 479587424294]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-15019217500188, -1658932967911, 479587424294]] 
 ![![157, 0, 0], ![34, 1, 0], ![129, 0, 1]] where
  M :=![![![-15019217500188, -1658932967911, 479587424294], ![-58729836458897, -18376329470246, -2838278511528], ![167199015450887, -18601476955145, -20035262438157]]]
  hmulB := by decide  
  f := ![![![315378411261945861925165062, -42158191800389758424272657, 13521570313500365118134332]], ![![57781152380886790432951299, -7723892370355468027560800, 2477315779437791479529658]], ![![285661025141954614257275645, -38185721843299831402571510, 12247463679672615591804337]]]
  g := ![![![-130460346020, -1658932967911, 479587424294], ![5937600595647, -18376329470246, -2838278511528], ![21555401824510, -18601476955145, -20035262438157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![315378411261945861925165062, -42158191800389758424272657, 13521570313500365118134332]] ![![-15019217500188, -1658932967911, 479587424294]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3396145714, 163092173, 321820864]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-3396145714, 163092173, 321820864]] 
 ![![163, 0, 0], ![0, 163, 0], ![25, 27, 1]] where
  M :=![![![-3396145714, 163092173, 321820864], ![-38133590643, -5648891762, 648005210], ![-39682683019, -21416359643, -5485799589]]]
  hmulB := by decide  
  f := ![![![-275255219228115496, 36794726309401685, -11801323958917446]], ![![1441152277420577759, -192645951515693374, 61788128659885924]], ![![174200257596599452, -23286209864679090, 7468681899617743]]]
  g := ![![![-70194278, -52307185, 321820864], ![-333335711, -141994064, 648005210], ![597928262, 777302020, -5485799589]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [66, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 162], [0, 1]]
 g := ![![[8, 87], [103, 33], [113], [71], [9], [108, 54], [1]], ![[38, 76], [120, 130], [113], [71], [9], [121, 109], [1]]]
 h' := ![![[124, 162], [48, 139], [38, 14], [18, 73], [38, 76], [44, 3], [97, 124], [0, 1]], ![[0, 1], [6, 24], [144, 149], [105, 90], [8, 87], [90, 160], [151, 39], [124, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [91, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [66, 39, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-256963, -273595, -24616]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2199, 2399, -24616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-275255219228115496, 36794726309401685, -11801323958917446]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-275255219228115496, 36794726309401685, -11801323958917446]] 
 ![![163, 0, 0], ![108, 1, 0], ![118, 0, 1]] where
  M :=![![![-275255219228115496, 36794726309401685, -11801323958917446], ![1441152277420577759, -192645951515693374, 61788128659885924], ![-3635089021407001417, 485920325245987303, -155851225206291689]]]
  hmulB := by decide  
  f := ![![![-3396145714, 163092173, 321820864]], ![![-2484155385, 73405294, 217206494]], ![![-2702011517, -13321983, 199319401]]]
  g := ![![![-17524720450866496, 36794726309401685, -11801323958917446], ![91754085026067013, -192645951515693374, 61788128659885924], ![-231435825605099453, 485920325245987303, -155851225206291689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-3396145714, 163092173, 321820864]] ![![-275255219228115496, 36794726309401685, -11801323958917446]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [127, 125, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 79, 48], [58, 87, 119], [0, 1]]
 g := ![![[163, 64, 32], [21, 119, 84], [25, 66, 137], [122, 24], [120, 14], [92, 65, 1], []], ![[75, 140, 108, 38], [72, 130, 16, 108], [23, 57, 79, 58], [54, 56], [29, 162], [135, 88, 76, 87], [30, 133]], ![[107, 54, 112, 125], [74, 48, 66, 136], [3, 84, 47, 13], [146, 28], [62, 96], [132, 132, 105, 30], [126, 133]]]
 h' := ![![[7, 79, 48], [5, 135, 115], [165, 64, 77], [86, 44, 114], [160, 2, 58], [6, 118, 66], [0, 0, 1], [0, 1]], ![[58, 87, 119], [130, 103, 119], [93, 20, 85], [162, 91, 6], [138, 56, 132], [100, 67, 50], [80, 4, 87], [7, 79, 48]], ![[0, 1], [17, 96, 100], [19, 83, 5], [110, 32, 47], [68, 109, 144], [60, 149, 51], [54, 163, 79], [58, 87, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 136], []]
 b := ![[], [50, 97, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [127, 125, 102, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-969435, -254174, -16366]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5805, -1522, -98]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46939017531120, 17889667012087, 3538159511402]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![46939017531120, 17889667012087, 3538159511402]] 
 ![![173, 0, 0], ![0, 173, 0], ![56, 67, 1]] where
  M :=![![![46939017531120, 17889667012087, 3538159511402], ![-403151314844751, 22171900951306, 39317493535576], ![-2351774423656679, -348131718302935, 40061567963393]]]
  hmulB := by decide  
  f := ![![![-84253801738398700193359866, 11262622318967886314029457, -3612307195749199200015700]], ![![441127178613122591115897757, -58967651368154305793249966, 18912937442186573428043214]], ![![137136597497710447816002780, -18331727137021459590516273, 5879610269452941300571073]]]
  g := ![![![-873976387904, -1266861388739, 3538159511402], ![-15057404351659, -15098844889782, 39317493535576], ![-26561978205819, -17527495791042, 40061567963393]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [153, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 172], [0, 1]]
 g := ![![[158, 49], [25], [100, 51], [127, 41], [89], [47, 40], [1]], ![[163, 124], [25], [24, 122], [110, 132], [89], [157, 133], [1]]]
 h' := ![![[46, 172], [48, 7], [97, 168], [118, 33], [139, 120], [75, 75], [20, 46], [0, 1]], ![[0, 1], [24, 166], [40, 5], [79, 140], [123, 53], [65, 98], [60, 127], [46, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [84, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [153, 127, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-700, -405, -272]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 103, -272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84253801738398700193359866, 11262622318967886314029457, -3612307195749199200015700]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-84253801738398700193359866, 11262622318967886314029457, -3612307195749199200015700]] 
 ![![173, 0, 0], ![38, 1, 0], ![57, 0, 1]] where
  M :=![![![-84253801738398700193359866, 11262622318967886314029457, -3612307195749199200015700], ![441127178613122591115897757, -58967651368154305793249966, 18912937442186573428043214], ![-1112676702624978921768516283, 148736997099424345402782901, -47705029049186419479220509]]]
  hmulB := by decide  
  f := ![![![46939017531120, 17889667012087, 3538159511402]], ![![7979950007733, 4057683511044, 1004436733924]], ![![1871384830157, 3881961279688, 1397321734759]]]
  g := ![![![-1770704853765745813442684, 11262622318967886314029457, -3612307195749199200015700], ![9270869921377754484745279, -58967651368154305793249966, 18912937442186573428043214], ![-23384369575719526802073396, 148736997099424345402782901, -47705029049186419479220509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![46939017531120, 17889667012087, 3538159511402]] ![![-84253801738398700193359866, 11262622318967886314029457, -3612307195749199200015700]]
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
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9737352606354, 1301640074741, -417480376692]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-9737352606354, 1301640074741, -417480376692]] 
 ![![179, 0, 0], ![0, 179, 0], ![145, 105, 1]] where
  M :=![![![-9737352606354, 1301640074741, -417480376692], ![50981804901089, -6814989969510, 2185799772790], ![-128593905162583, 17189783208409, -5513349894769]]]
  hmulB := by decide  
  f := ![![![2228480, 95381, -130930]], ![![15676051, 3144990, 59832]], ![![10983314, 1964442, -52861]]]
  g := ![![![283783810134, 252162456019, -417480376692], ![-1485805375159, -1320245620740, 2185799772790], ![3747719718318, 3330120235526, -5513349894769]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [173, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 178], [0, 1]]
 g := ![![[132, 149], [26, 108], [139], [47], [178, 145], [85, 48], [1]], ![[0, 30], [0, 71], [139], [47], [100, 34], [153, 131], [1]]]
 h' := ![![[76, 178], [156, 111], [107, 114], [139, 153], [173, 91], [152, 161], [6, 76], [0, 1]], ![[0, 1], [0, 68], [0, 65], [132, 26], [108, 88], [37, 18], [54, 103], [76, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [169]]
 b := ![[], [11, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [173, 103, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13389, 668, 1094]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-961, -638, 1094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2228480, -95381, 130930]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-2228480, -95381, 130930]] 
 ![![179, 0, 0], ![147, 1, 0], ![115, 0, 1]] where
  M :=![![![-2228480, -95381, 130930], ![-15676051, -3144990, -59832], ![3101749, -7580923, -3240371]]]
  hmulB := by decide  
  f := ![![![9737352606354, -1301640074741, 417480376692]], ![![7711782280631, -1030872072723, 330635841346]], ![![6974242764767, -932281518456, 299014487231]]]
  g := ![![![-18237, -95381, 130930], ![2533621, -3144990, -59832], ![8324805, -7580923, -3240371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-9737352606354, 1301640074741, -417480376692]] ![![-2228480, -95381, 130930]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)


lemma PB180I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 179 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 179 (by omega)

def PB180I3 : PrimesBelowBoundCertificateInterval O 137 179 180 where
  m := 8
  g := ![3, 2, 3, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB180I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
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
  β := ![I139N0, I139N1, I139N2, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I173N1, I179N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [], [I173N1], [I179N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
