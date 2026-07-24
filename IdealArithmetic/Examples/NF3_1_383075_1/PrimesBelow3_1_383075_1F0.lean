
import IdealArithmetic.Examples.NF3_1_383075_1.RI3_1_383075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257974606, -6539749, 10553256]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![257974606, -6539749, 10553256]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 2]] where
  M :=![![![257974606, -6539749, 10553256], ![-443236752, 11236211, -18131982], ![53051082, -1344864, 2170220]]]
  hmulB := by decide  
  f := ![![![-2014, -1202, -249]], ![![5229, 2582, -3855]], ![![55713, 32583, 1309]]]
  g := ![![![128987303, -6539749, 5276628], ![-221618376, 11236211, -9065991], ![26525541, -1344864, 1085110]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-440, -399, -1156]
  a := ![0, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-220, -399, -578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2014, 1202, 249]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2014, 1202, 249]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2014, 1202, 249], ![-10458, -5164, 7710], ![-55713, -32583, -1309]]]
  hmulB := by decide  
  f := ![![![-257974606, 6539749, -10553256]], ![![92631073, -2348231, 3789363]], ![![-26525541, 672432, -1085110]]]
  g := ![![![406, 1202, 249], ![-2647, -5164, 7710], ![-11565, -32583, -1309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![257974606, -6539749, 10553256]] ![![2014, 1202, 249]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34904350585044, 884837834909, -1427871343421]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-34904350585044, 884837834909, -1427871343421]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-34904350585044, 884837834909, -1427871343421], ![59970596423682, -1520276177849, 2453284322612], ![-7177890854337, 181962113499, -293634016543]]]
  hmulB := by decide  
  f := ![![![-16619, 40492, 419121]], ![![-5867694, -3372005, 360398]], ![![-3500735, -2419541, -3191806]]]
  g := ![![![-11634783528348, 884837834909, -1427871343421], ![19990198807894, -1520276177849, 2453284322612], ![-2392630284779, 181962113499, -293634016543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-336674862599204211541, -196100302035514484762, -1230812055954447598]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-336674862599204211541, -196100302035514484762, -1230812055954447598]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-336674862599204211541, -196100302035514484762, -1230812055954447598], ![51694106350086799116, -111035071220782984427, -1179063436324995803768], ![8262059738666651759562, 4724869429691664348258, -700566789383280886311]]]
  hmulB := by decide  
  f := ![![![5648708269313264790992239419697346851114941, -143196785250987159813613061904464947477266, 231078032678070977289640894573981956626870]], ![![-1352189701055238751724226050803298442404533, 34278495013187112013619316640593297356687, -55315537823903342337585229234947938327662]], ![![4153014277642833257024589551109533469036928, -105280404883115714481708685570500168301066, 169892004190599982760851503278265288998713]]]
  g := ![![![-46037645483926943861, -196100302035514484762, -1230812055954447598], ![840285350073620463693, -111035071220782984427, -1179063436324995803768], ![1646107962580516394642, 4724869429691664348258, -700566789383280886311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153839211046641248515723306339, 3899879302866770797593401984, -6293272823191174665580076801]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-153839211046641248515723306339, 3899879302866770797593401984, -6293272823191174665580076801]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-153839211046641248515723306339, 3899879302866770797593401984, -6293272823191174665580076801], ![264317458574029335954363225642, -6700542592919827339394865099, 10812730170818275454400258302], ![-31636201433389705521741270507, 801989079065120841459504399, -1294177507510689612194735948]]]
  hmulB := by decide  
  f := ![![![86189119391646, 51355918026767, 9956935197131]], ![![-110667386295952, -50925775113166, 112668771250665]], ![![-788681398754655, -460632020199791, -13369518029611]]]
  g := ![![![-52579696783169339771105569441, 3899879302866770797593401984, -6293272823191174665580076801], ![90339333722316387764586030247, -6700542592919827339394865099, 10812730170818275454400258302], ![-10812730170818275454400258302, 801989079065120841459504399, -1294177507510689612194735948]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-34904350585044, 884837834909, -1427871343421]] ![![-336674862599204211541, -196100302035514484762, -1230812055954447598]]
  ![![86189119391646, 51355918026767, 9956935197131]] where
 M := ![![![86189119391646, 51355918026767, 9956935197131]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![86189119391646, 51355918026767, 9956935197131]] ![![-153839211046641248515723306339, 3899879302866770797593401984, -6293272823191174665580076801]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065], ![-542492706671512142296205314174668274480894316730, 13752385131921769542948438567956229259936837279, -22192356450919199025454811507016159595632492648], ![64931044044515702795482794853335071422611729081, -1646025308241894280881639667713407364285748863, 2656206906462170030221032814448149462120590955]]]
  hmulB := by decide  
  f := ![![![164135382535933132352221, 92412690431727656935070, -26051492970770743878111]], ![![317313770476034127987465, 194839318939577259859405, 84843735547302444443973]], ![![-535542023120528688084745, -291496282814598396105947, 168787825968806515981294]]]
  g := ![![![57618138589197622450548150510613645408863577501, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065], ![-98996087252720130964646276770094464775634971595, 13752385131921769542948438567956229259936837279, -22192356450919199025454811507016159595632492648], ![11848858468678541103448716519736539133397322370, -1646025308241894280881639667713407364285748863, 2656206906462170030221032814448149462120590955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065]] ![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065]]
  ![![104875183983195820229321944758237380253370826291292279784485000988388720548204768647356723958631, -2658623614992464549610051923549190312155341885874991395396814348968540083049890087222513047360, 4290246554817017142691115862673519011578665782329221703096767637100860579087478661761243331539]] where
 M := ![![![104875183983195820229321944758237380253370826291292279784485000988388720548204768647356723958631, -2658623614992464549610051923549190312155341885874991395396814348968540083049890087222513047360, 4290246554817017142691115862673519011578665782329221703096767637100860579087478661761243331539]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![104875183983195820229321944758237380253370826291292279784485000988388720548204768647356723958631, -2658623614992464549610051923549190312155341885874991395396814348968540083049890087222513047360, 4290246554817017142691115862673519011578665782329221703096767637100860579087478661761243331539]] ![![315743993768493665761170869240607881137994092376, -8004223747149327951037748855730219253882354463, 12916493015988384340385840813682577963830817065]]
  ![![5, 0, 0]] where
 M := ![![![34834563546990525561723985157164357653913840755911987448097387876286670124815008141553718382172288155998393843402357865512230982509833677615715, -883068708406975711624286502252813118286694025084248670936848805614419368278777970251495586437591426294738236813922482233222759670320432043750, 1425016486931520312378826490154291523540543134913823827301517063639575345256590241735579852379793221135189640696379411014853650115072934277040]]]
 hmul := by decide  
 g := ![![![![6966912709398105112344797031432871530782768151182397489619477575257334024963001628310743676434457631199678768680471573102446196501966735523143, -176613741681395142324857300450562623657338805016849734187369761122883873655755594050299117287518285258947647362784496446644551934064086408750, 285003297386304062475765298030858304708108626982764765460303412727915069051318048347115970475958644227037928139275882202970730023014586855408]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52937014570561009, -36144174358049534, -44561220627098016]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-52937014570561009, -36144174358049534, -44561220627098016]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-52937014570561009, -36144174358049534, -44561220627098016], ![1871571266338116672, 1052676454837840909, -305987487402493236], ![2453840956207138764, 1535878493999659056, 899682711136594291]]]
  hmulB := by decide  
  f := ![![![-1417034408172648326951754326281795735, 35922331649290066232037588454422502, -57968212849037610219773253345488568]], ![![347809277094225661318639520072931408, -8817090206433678272747690634927515, 14228223456809310993239860576508268]], ![![-41629351348627566732905770690069308, 1055319021800366246813811039455496, -1702978478029022776127760346673381]]]
  g := ![![![-7562430652937287, -36144174358049534, -44561220627098016], ![267367323762588096, 1052676454837840909, -305987487402493236], ![350548708029591252, 1535878493999659056, 899682711136594291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30746710747401301306086385, -14602329829166782179429572, 27512753570842892394780412]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-30746710747401301306086385, -14602329829166782179429572, 27512753570842892394780412]] 
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![-30746710747401301306086385, -14602329829166782179429572, 27512753570842892394780412], ![-1155535649975401480580777304, -676450466618463936601386701, -32588471833314908287016608], ![35530027837304111245653372, -62235387662640613615396452, -692744702535121390744895005]]]
  hmulB := by decide  
  f := ![![![466579321099472464143052277838048365488807897420053689, -11827953517973979708308282754176786170363386795986084, 19086882605294060230990961227204002878890712722432588]], ![![85441270553723837532505208853082425079001965416856053, -2165966923361848688192479589028753706470854501471513, 3495241702660917557872158515851328196039034690892348]], ![![413632205662938095393778765276061593090200666111521902, -10485725107982752673616475547553984588117104072677044, 16920915681932211542798481638175249172419858220961075]]]
  g := ![![![-21716606097851187019497163, -14602329829166782179429572, 27512753570842892394780412], ![152763797268554254135068921, -676450466618463936601386701, -32588471833314908287016608], ![625529200862279185223030394, -62235387662640613615396452, -692744702535121390744895005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-52937014570561009, -36144174358049534, -44561220627098016]] ![![-30746710747401301306086385, -14602329829166782179429572, 27512753570842892394780412]]
  ![![41810259675139972613055578460725956516828849, 27996032197420368374200151296747731794244714, 30590989899270686145333065595637240304315044]] where
 M := ![![![41810259675139972613055578460725956516828849, 27996032197420368374200151296747731794244714, 30590989899270686145333065595637240304315044]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![41810259675139972613055578460725956516828849, 27996032197420368374200151296747731794244714, 30590989899270686145333065595637240304315044]] ![![-30746710747401301306086385, -14602329829166782179429572, 27512753570842892394780412]]
  ![![7, 0, 0]] where
 M := ![![![-32549042499791901818552141516574099515713597394198017850313950058363553, -21452298360795088432689590928047149906443129804050425841435922880295030, -20953778733560309631147188716599235492555574100567002860535214014459544]]]
 hmul := by decide  
 g := ![![![![-4649863214255985974078877359510585645101942484885431121473421436909079, -3064614051542155490384227275435307129491875686292917977347988982899290, -2993396961937187090163884102371319356079367728652428980076459144922792]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3215, 1380, -4104]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![3215, 1380, -4104]] 
 ![![11, 0, 0], ![2, 1, 0], ![7, 0, 1]] where
  M :=![![![3215, 1380, -4104], ![172368, 100331, 72], ![28224, 28440, 100367]]]
  hmulB := by decide  
  f := ![![![10067873797, -255224220, 411857784]], ![![257974606, -6539749, 10553256]], ![![6595047305, -167186820, 269790983]]]
  g := ![![![2653, 1380, -4104], ![-2618, 100331, 72], ![-66475, 28440, 100367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-97829, 2480, -4002]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-97829, 2480, -4002]] 
 ![![11, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![-97829, 2480, -4002], ![168084, -4261, 6876], ![-20118, 510, -823]]]
  hmulB := by decide  
  f := ![![![-43, -20, 42]], ![![-176, -101, 12]], ![![-39, -30, -61]]]
  g := ![![![-6521, 2480, -4002], ![11204, -4261, 6876], ![-1341, 510, -823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![3215, 1380, -4104]] ![![-97829, 2480, -4002]]
  ![![-43, -20, 42]] where
 M := ![![![-43, -20, 42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-43, -20, 42]] ![![-97829, 2480, -4002]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [3, 10, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 11, 11], [7, 1, 2], [0, 1]]
 g := ![![[8, 0, 3], [3, 3], [1]], ![[9, 11, 7, 11], [9, 9], [0, 9, 8, 5]], ![[6, 0, 6, 11], [1, 1], [5, 12, 6, 8]]]
 h' := ![![[2, 11, 11], [0, 8, 4], [10, 3, 9], [0, 1]], ![[7, 1, 2], [11, 3, 1], [8, 1, 3], [2, 11, 11]], ![[0, 1], [6, 2, 8], [3, 9, 1], [7, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 12], []]
 b := ![[], [8, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [3, 10, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2302352, 1603485, 2204644]
  a := ![-1, -3, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177104, 123345, 169588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5966936540882557598939603, 151263986333446473276570, -244096152827107296748541]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-5966936540882557598939603, 151263986333446473276570, -244096152827107296748541]] 
 ![![17, 0, 0], ![0, 17, 0], ![16, 1, 1]] where
  M :=![![![-5966936540882557598939603, 151263986333446473276570, -244096152827107296748541], ![10252038418738506463438722, -259892859365428950251189, 419391612346464246162338], ![-1227068216635498645896579, 31106620403894092590435, -50197053192196827170020]]]
  hmulB := by decide  
  f := ![![![-35826712750, -32610330945, -98239562083]], ![![4126061607486, 2354533108187, -392141109836]], ![![410911700407, 240529952176, 11440497065]]]
  g := ![![![-121258711508755344174291, 23256478774150221766183, -244096152827107296748541], ![208339565952651677931842, -39957910100699599789031, 419391612346464246162338], ![-24936197974138200657427, 4782569035064171750615, -50197053192196827170020]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16], [0, 1]]
 g := ![![[8, 8], [2], [15], [1]], ![[13, 9], [2], [15], [1]]]
 h' := ![![[7, 16], [15, 12], [3, 11], [3, 7], [0, 1]], ![[0, 1], [14, 5], [12, 6], [1, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [16, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3365, -254, 1]
  a := ![-64, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![197, -15, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35826712750, 32610330945, 98239562083]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![35826712750, 32610330945, 98239562083]] 
 ![![17, 0, 0], ![9, 1, 0], ![5, 0, 1]] where
  M :=![![![35826712750, 32610330945, 98239562083], ![-4126061607486, -2354533108187, 392141109836], ![-3432664703433, -2256241373925, -2158462553269]]]
  hmulB := by decide  
  f := ![![![5966936540882557598939603, -151263986333446473276570, 244096152827107296748541]], ![![2555905320541441878059865, -64793118684446429955173, 104557280182205966151443]], ![![1827161818885193331799682, -46319208945360379939605, 74745753960454900641925]]]
  g := ![![![-44050828010, 32610330945, 98239562083], ![888472401001, -2354533108187, 392141109836], ![1627401201661, -2256241373925, -2158462553269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-5966936540882557598939603, 151263986333446473276570, -244096152827107296748541]] ![![35826712750, 32610330945, 98239562083]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235529600334285254147, -135823334739479615538, 10532529983722174209]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-235529600334285254147, -135823334739479615538, 10532529983722174209]] 
 ![![19, 0, 0], ![0, 19, 0], ![16, 2, 1]] where
  M :=![![![-235529600334285254147, -135823334739479615538, 10532529983722174209], ![-442366259316331316778, -352486985204137819625, -793874948469433344810], ![5483396929399978194207, 3101772083991678159777, -749424459438854492030]]]
  hmulB := by decide  
  f := ![![![143504290615192782243423817784514939673480, -3637885354684333318285059693371481819513, 5870490663567652191204162060768729300495]], ![![-246560607869841392030574806552286630620790, 6250400044253462972808988019436918281113, -10086330800970695527302034038691432316088]], ![![96445174477117001851911398699638141823329, -2444919843554378440850735648720276231005, 3945390718889955748095815573421474015727]]]
  g := ![![![-21265793688096844289, -8257283931943366524, 10532529983722174209], ![645243837694452747378, 65013837459722572105, -793874948469433344810], ![919694120022192108773, 242137947519441428623, -749424459438854492030]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[18, 5], [2, 16], [7], [1]], ![[1, 14], [16, 3], [7], [1]]]
 h' := ![![[8, 18], [3, 9], [8, 4], [11, 8], [0, 1]], ![[0, 1], [18, 10], [2, 15], [18, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [5, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [8, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1765, -1857, -7018]
  a := ![1, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5817, 641, -7018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143504290615192782243423817784514939673480, 3637885354684333318285059693371481819513, -5870490663567652191204162060768729300495]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-143504290615192782243423817784514939673480, 3637885354684333318285059693371481819513, -5870490663567652191204162060768729300495]] 
 ![![19, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![-143504290615192782243423817784514939673480, 3637885354684333318285059693371481819513, -5870490663567652191204162060768729300495], ![246560607869841392030574806552286630620790, -6250400044253462972808988019436918281113, 10086330800970695527302034038691432316088], ![-29510880961821303352685103845458921109151, 748111441090783229220998270615375839113, -1207234643768115209157971000091202123069]]]
  hmulB := by decide  
  f := ![![![235529600334285254147, 135823334739479615538, -10532529983722174209]], ![![85263908473039873027, 54294929415870310385, 39011173607938024935]], ![![-251410954126164338514, -141805372619644174377, 37780361551983577337]]]
  g := ![![![-7583276073574289066380875266792955835240, 3637885354684333318285059693371481819513, -5870490663567652191204162060768729300495], ![13029137667799822121721770764915627635689, -6250400044253462972808988019436918281113, 10086330800970695527302034038691432316088], ![-1559459696630045993227167484119062838711, 748111441090783229220998270615375839113, -1207234643768115209157971000091202123069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-235529600334285254147, -135823334739479615538, 10532529983722174209]] ![![-143504290615192782243423817784514939673480, 3637885354684333318285059693371481819513, -5870490663567652191204162060768729300495]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [2, 20, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 14, 22], [4, 8, 1], [0, 1]]
 g := ![![[21, 22, 13], [4, 1, 13], [21, 8, 1], []], ![[14, 20, 8, 21], [7, 6, 22, 22], [5, 9, 21, 5], [3, 1]], ![[12, 11, 2, 6], [17, 13, 19, 3], [1, 6, 11, 12], [1, 1]]]
 h' := ![![[4, 14, 22], [15, 3, 17], [4, 1, 6], [0, 0, 1], [0, 1]], ![[4, 8, 1], [13, 18, 18], [22, 15, 1], [10, 4, 8], [4, 14, 22]], ![[0, 1], [12, 2, 11], [0, 7, 16], [14, 19, 14], [4, 8, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 18], []]
 b := ![[], [11, 11, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [2, 20, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-244858, -166290, -198375]
  a := ![0, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10646, -7230, -8625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-354136, -196703, 78643]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-354136, -196703, 78643]] 
 ![![29, 0, 0], ![0, 29, 0], ![15, 5, 1]] where
  M :=![![![-354136, -196703, 78643], ![-3303006, -2044865, -1022932], ![6610023, 3541227, -2556331]]]
  hmulB := by decide  
  f := ![![![305165041651, -7736043508, 12483727979]], ![![-524316575118, 13291613663, -21448805090]], ![![69608561688, -1764602062, 2847555357]]]
  g := ![![![-52889, -20342, 78643], ![415206, 105855, -1022932], ![1550172, 562858, -2556331]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [21, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[25, 28], [23], [28, 28], [26, 1]], ![[28, 1], [23], [2, 1], [23, 28]]]
 h' := ![![[26, 28], [16, 17], [21, 20], [5, 17], [0, 1]], ![[0, 1], [23, 12], [19, 9], [12, 12], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [7, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [21, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11000, -8181, -14344]
  a := ![1, -1, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7040, 2191, -14344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-305165041651, 7736043508, -12483727979]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-305165041651, 7736043508, -12483727979]] 
 ![![29, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![-305165041651, 7736043508, -12483727979], ![524316575118, -13291613663, 21448805090], ![-62755539777, 1590875493, -2567211118]]]
  hmulB := by decide  
  f := ![![![354136, 196703, -78643]], ![![431398, 246867, -35234]], ![![101781, 61026, 14930]]]
  g := ![![![-5835914394, 7736043508, -12483727979], ![10026923894, -13291613663, 21448805090], ![-1200124221, 1590875493, -2567211118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-354136, -196703, 78643]] ![![-305165041651, 7736043508, -12483727979]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![924219693850959024826, 1555492646407766592047, 8501736062074184292989]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![924219693850959024826, 1555492646407766592047, 8501736062074184292989]] 
 ![![31, 0, 0], ![0, 31, 0], ![5, 21, 1]] where
  M :=![![![924219693850959024826, 1555492646407766592047, 8501736062074184292989], ![-357072914607115740305538, -204672938442337230598957, 26336428002594968138260], ![-243867148452684067018743, -164857864444899162603963, -191504724441039746529827]]]
  hmulB := by decide  
  f := ![![![-1404438772727494510376018556489144190363984349, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603]], ![![2413023861761834479104708182874462769143409326, -61171022340692668405121435803793475516903475, 98712268397772187052440179892031739926184382]], ![![1398790064458181245585026317069446843512869408, -35459830977566873214836799323866402573104332, 57221871056889416620441506316722750642025733]]]
  g := ![![![-1341434213436127820649, -5709063376037100114862, 8501736062074184292989], ![-15766292084519050999898, -24443158919252631016207, 26336428002594968138260], ![23021176572661763407432, 124411011252159210145884, -191504724441039746529827]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [15, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30], [0, 1]]
 g := ![![[13, 10], [14, 14], [6, 16], [22, 1]], ![[16, 21], [12, 17], [17, 15], [13, 30]]]
 h' := ![![[22, 30], [7, 14], [3, 13], [11, 4], [0, 1]], ![[0, 1], [5, 17], [10, 18], [6, 27], [22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [4, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [15, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70, 15, -234]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 159, -234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1404438772727494510376018556489144190363984349, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1404438772727494510376018556489144190363984349, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603]] 
 ![![31, 0, 0], ![27, 1, 0], ![7, 0, 1]] where
  M :=![![![-1404438772727494510376018556489144190363984349, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603], ![2413023861761834479104708182874462769143409326, -61171022340692668405121435803793475516903475, 98712268397772187052440179892031739926184382], ![-288815235157432896182963228765145051292722453, 7321570035883664974357310910950168485830693, -11814888141806574878901345857777605553811284]]]
  hmulB := by decide  
  f := ![![![924219693850959024826, 1555492646407766592047, 8501736062074184292989]], ![![-10713515576552898278556, -5247568935139597826248, 8254300054148320775773]], ![![-7657987438571850124031, -4966755352259509563214, -4257824903436143757384]]]
  g := ![![![-63340318667632397655079408400834854362229654, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603], ![108827599554068748925029215817182723503758467, -61171022340692668405121435803793475516903475, 98712268397772187052440179892031739926184382], ![-13025593843020833107687135559882463275273296, 7321570035883664974357310910950168485830693, -11814888141806574878901345857777605553811284]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![924219693850959024826, 1555492646407766592047, 8501736062074184292989]] ![![-1404438772727494510376018556489144190363984349, 35603027762817860374650412385770867520581598, -57452949089567487597731147211296732598652603]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB176I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB176I0 : PrimesBelowBoundCertificateInterval O 1 31 176 where
  m := 11
  g := ![2, 3, 3, 3, 3, 1, 2, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB176I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I11N0, I11N1, I17N1, I19N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0], [I7N0, I7N1, I7N1], [I11N0, I11N1, I11N1], [], [I17N1], [I19N1], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
