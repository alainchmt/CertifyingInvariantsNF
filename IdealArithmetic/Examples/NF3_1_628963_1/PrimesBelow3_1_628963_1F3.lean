
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-208744204894, 10120900447, 12275167492]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-208744204894, 10120900447, 12275167492]] 
 ![![139, 0, 0], ![0, 139, 0], ![67, 19, 1]] where
  M :=![![![-208744204894, 10120900447, 12275167492], ![1857858825382, -262153408952, 26054167251], ![75477669351, 344355124554, -278086675756]]]
  hmulB := by decide  
  f := ![![![-459924345501410352422, -50658304975485728500, -25047975801880797479]], ![![-3731023687736790557287, -410953100641097024548, -203195573273667047542]], ![![-765822624320986582473, -84351429619766469221, -41707525922795705323]]]
  g := ![![![-7418564222, -1605088359, 12275167492], ![807407335, -5447356739, 26054167251], ![134584783777, 40489222762, -278086675756]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [138, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[41, 81], [105, 89], [31], [12, 80], [6], [13], [1]], ![[26, 58], [1, 50], [31], [95, 59], [6], [13], [1]]]
 h' := ![![[41, 138], [105, 130], [36, 28], [12, 93], [63, 91], [14, 59], [1, 41], [0, 1]], ![[0, 1], [14, 9], [72, 111], [72, 46], [41, 48], [70, 80], [14, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [76, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [138, 98, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1910, 357, -625]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![315, 88, -625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-459924345501410352422, -50658304975485728500, -25047975801880797479]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-459924345501410352422, -50658304975485728500, -25047975801880797479]] 
 ![![139, 0, 0], ![46, 1, 0], ![114, 0, 1]] where
  M :=![![![-459924345501410352422, -50658304975485728500, -25047975801880797479], ![-3731023687736790557287, -410953100641097024548, -203195573273667047542], ![-4744963565023620763020, -522633371609151945807, -258415832342915705506]]]
  hmulB := by decide  
  f := ![![![-208744204894, 10120900447, 12275167492]], ![![-55714925178, 1463366990, 4249725697]], ![![-170657278335, 10777969608, 8066779988]]]
  g := ![![![33998754854570820656, -50658304975485728500, -25047975801880797479], ![275806577661523136631, -410953100641097024548, -203195573273667047542], ![350759542561796828574, -522633371609151945807, -258415832342915705506]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-208744204894, 10120900447, 12275167492]] ![![-459924345501410352422, -50658304975485728500, -25047975801880797479]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29552931901468615526947, 22420597649905501761588, -14765059225957150109798]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-29552931901468615526947, 22420597649905501761588, -14765059225957150109798]] 
 ![![149, 0, 0], ![0, 149, 0], ![26, 23, 1]] where
  M :=![![![-29552931901468615526947, 22420597649905501761588, -14765059225957150109798], ![-2303895256871254970322270, 103878618754085288655017, 141633106701441809027536], ![5202158547550399782698724, -621770540356018964192862, -15333890297451018610931]]]
  hmulB := by decide  
  f := ![![![580338455985444848951267383496120452515224545, 63921300926704291380798127226838121389534096, 31605858103851367953349672874468472312031166]], ![![4707853688035850714100903695340000020961700206, 518545909215745223992765600702985861422105741, 256394788425818720997291290385253662323608148]], ![![868165709729998153851771071707980860017918924, 95623994952505510885302755473576488770443909, 47281240712822798282557473900279092845931741]]]
  g := ![![![2378111462908840854549, 2429644025818254726758, -14765059225957150109798], ![-40176886114823771845894, -21165656613282391402539, 141633106701441809027536], ![37589528156269303802570, -1805980292044600913701, -15333890297451018610931]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [79, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 148], [0, 1]]
 g := ![![[131, 140], [25], [111, 26], [47], [41, 80], [5], [1]], ![[147, 9], [25], [131, 123], [47], [114, 69], [5], [1]]]
 h' := ![![[81, 148], [148, 17], [22, 144], [43, 131], [39, 14], [35, 123], [70, 81], [0, 1]], ![[0, 1], [35, 132], [64, 5], [75, 18], [130, 135], [15, 26], [75, 68], [81, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [74, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [79, 68, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10180, 4588, 44]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, 24, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1425351719234417515403, 276763524055809642978, -79464742438683053638]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-1425351719234417515403, 276763524055809642978, -79464742438683053638]] 
 ![![149, 0, 0], ![36, 1, 0], ![24, 0, 1]] where
  M :=![![![-1425351719234417515403, 276763524055809642978, -79464742438683053638], ![-12711632641230126492570, -395036216490699907619, 1542747105156414322166], ![51880588273180841812194, -4282917644811398627922, -1661019797591304586807]]]
  hmulB := by decide  
  f := ![![![7263621774512730304240677770882727937301585, 800050640238865912617940904025458809471482, 395584674352602656844746022150542909782426]], ![![2150434481731065541105199055924566129668626, 236859315821973282165462791885549699587405, 117114980732770603327591068947958073691006]], ![![1672916171963353645039944309792050464231434, 184263126026412577872480234922323319418166, 91108818665013769234226284602970929624209]]]
  g := ![![![-63635468232987727351, 276763524055809642978, -79464742438683053638], ![-238364156854489084230, -395036216490699907619, 1542747105156414322166], ![1650537574688473171146, -4282917644811398627922, -1661019797591304586807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-29552931901468615526947, 22420597649905501761588, -14765059225957150109798]] ![![-1425351719234417515403, 276763524055809642978, -79464742438683053638]]
  ![![149, 0, 0]] where
 M := ![![![-1008899037159263404875941243324647575854613331, 46201411039226449034275555765009556077512618, 61462783929049532165527701799355577463377780]]]
 hmul := by decide  
 g := ![![![![-6771134477578949026013028478688909905064519, 310076584155882208283728562181272188439682, 412501905564090819902870481874869647405220]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![313722689866696097, -150426318547808738, 87873267990616648]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![313722689866696097, -150426318547808738, 87873267990616648]] 
 ![![151, 0, 0], ![13, 1, 0], ![21, 0, 1]] where
  M :=![![![313722689866696097, -150426318547808738, 87873267990616648], ![13745462639659964620, -514369555172621267, -927878128720276986], ![-33560018896688734674, 3802375754977201812, 263082254999846981]]]
  hmulB := by decide  
  f := ![![![-3392819797741515039562867230194753705, -373701678813017788587651102277686154, -184776624732319089919496468600156684]], ![![-474371374814956825793542592607949659, -52249571069820313436163277832841761, -25834776596825158490415342158875194]], ![![-703658130086657262876763273182496737, -77504329790475475471246026476625582, -38321980533542410536549701932728775]]]
  g := ![![![2807458299240133, -150426318547808738, 87873267990616648], ![264355679205495747, -514369555172621267, -927878128720276986], ![-586196232227742681, 3802375754977201812, 263082254999846981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51577773317426, 5681026882415, 2808981152240]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![51577773317426, 5681026882415, 2808981152240]] 
 ![![151, 0, 0], ![18, 1, 0], ![139, 0, 1]] where
  M :=![![![51577773317426, 5681026882415, 2808981152240], ![418412062527890, 46085940168816, 22787172107595], ![532119374740695, 58610216729430, 28979794943636]]]
  hmulB := by decide  
  f := ![![![81834126, -6137740, -3105915]], ![![6689303, -147584, -532340]], ![![71579994, -6084865, -2153569]]]
  g := ![![![-2921384706804, 5681026882415, 2808981152240], ![-23699018433553, 46085940168816, 22787172107595], ![-30139443864599, 58610216729430, 28979794943636]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26790317480979340382240, -2950815903998229024224, -1459029578564061671039]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-26790317480979340382240, -2950815903998229024224, -1459029578564061671039]] 
 ![![151, 0, 0], ![120, 1, 0], ![1, 0, 1]] where
  M :=![![![-26790317480979340382240, -2950815903998229024224, -1459029578564061671039], ![-217329893712304977620519, -23937771817591428404454, -11836020362863021779042], ![-276391283884041640181592, -30443080668624660998943, -15052567358726635649636]]]
  hmulB := by decide  
  f := ![![![325495673862, -162971929313, 96596894298]], ![![358706950660, -133355371312, 70089893249]], ![![-239740641237, 26507001049, 2395025494]]]
  g := ![![![2177262387929617246329, -2950815903998229024224, -1459029578564061671039], ![17662508243453837435053, -23937771817591428404454, -11836020362863021779042], ![22462456713308902750604, -30443080668624660998943, -15052567358726635649636]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![313722689866696097, -150426318547808738, 87873267990616648]] ![![51577773317426, 5681026882415, 2808981152240]]
  ![![325495673862, -162971929313, 96596894298]] where
 M := ![![![325495673862, -162971929313, 96596894298]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![325495673862, -162971929313, 96596894298]] ![![-26790317480979340382240, -2950815903998229024224, -1459029578564061671039]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9395646624746034026114036242851499605412, 1034882229683616864111101652411699730230, 511697046702521157902764248939761849709]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![9395646624746034026114036242851499605412, 1034882229683616864111101652411699730230, 511697046702521157902764248939761849709]] 
 ![![157, 0, 0], ![0, 157, 0], ![88, 124, 1]] where
  M :=![![![9395646624746034026114036242851499605412, 1034882229683616864111101652411699730230, 511697046702521157902764248939761849709], ![76219883686118503430900726782960163545017, 8395228803898140806919654054036327967618, 4151017055013042004749979764178974951732], ![96933335537290841260666842946218636760110, 10676709163081497026124610300541942659017, 5279093978568715666280775942269052746116]]]
  hmulB := by decide  
  f := ![![![-49876388271613288508, -1110768761580207711, 5707877293830169014]], ![![875526763479176274564, -86345189557754718014, -16969598395561376583]], ![![658097475208499978317, -67576602502641824768, -10652378083543499186]]]
  g := ![![![-226966200541884253944772087030876071140, -397551283830758004559437358064450761998, 511697046702521157902764248939761849709], ![-1841207752579803776987882117610125045907, -3225037490558720176955909787924564114950, 4151017055013042004749979764178974951732], ![-2341572831699083677528926369257694298714, -4101470982034644876386570742298220368531, 5279093978568715666280775942269052746116]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [144, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 156], [0, 1]]
 g := ![![[53, 12], [64], [151, 113], [24, 67], [94, 154], [110], [1]], ![[0, 145], [64], [136, 44], [29, 90], [68, 3], [110], [1]]]
 h' := ![![[61, 156], [8, 144], [79, 8], [155, 37], [123, 99], [29, 132], [13, 61], [0, 1]], ![[0, 1], [0, 13], [96, 149], [57, 120], [39, 58], [74, 25], [123, 96], [61, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [75, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [144, 96, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3096852, 979611, -218599]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![142252, 178891, -218599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-472738835901576220369450325581559844776652378124, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-472738835901576220369450325581559844776652378124, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772]] 
 ![![157, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![-472738835901576220369450325581559844776652378124, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772], ![-3834978104798950501590833644487854992377087595234, -422403145881347493121649357642643871406012075374, -208857042923056638114915435901935966213425194161], ![-4877168547534044416579199267979664958528232024333, -537195071568719015860038891219700881235027774830, -265615858249783058206160635251840510731888103154]]]
  hmulB := by decide  
  f := ![![![-7779180737479775196361966, 852652263666460116623154, 83576788450773249820227]], ![![-424903587701671114486441, 12427934368236348434360, 31413220547378895424698]], ![![420205837990555296117080, 22998001799630429048985, -58813725474269908790749]]]
  g := ![![![1453374422826504039570574970177139654822567170, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772], ![11790144296024973862611897982497678249535092469, -422403145881347493121649357642643871406012075374, -208857042923056638114915435901935966213425194161], ![14994224050328835346906459178218009101562181185, -537195071568719015860038891219700881235027774830, -265615858249783058206160635251840510731888103154]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![9395646624746034026114036242851499605412, 1034882229683616864111101652411699730230, 511697046702521157902764248939761849709]] ![![-472738835901576220369450325581559844776652378124, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772]]
  ![![157, 0, 0]] where
 M := ![![![-10906070481850798273822335328843131614146173886226302526043186443166698383278504231500005, -1201247661615786651392989646354452734931123893435492260431481501816545229618800316125182, -593956358681533540286173270009771984312654244623251951012471107535808472768275356731280]]]
 hmul := by decide  
 g := ![![![![-69465417081852218304600861967153704548701744498256703987536219383227378237442702111465, -7651258991183354467471271632830909139688687219334345607843831221761434583559237682326, -3783161520264544842587090891781987161227097099511158923646312786852283266039970425040]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [128, 16, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 128, 143], [76, 34, 20], [0, 1]]
 g := ![![[11, 159, 60], [54, 52, 131], [100, 133], [16, 34], [5, 36], [116, 135, 1], []], ![[121, 116, 96, 36], [46, 151, 161, 38], [73, 53], [34, 39], [76, 65], [119, 75, 74, 26], [143, 74]], ![[58, 45, 126, 142], [152, 114, 22, 2], [46, 69], [108, 140], [50, 56], [29, 30, 66, 50], [103, 74]]]
 h' := ![![[59, 128, 143], [97, 113, 68], [102, 110, 91], [5, 113, 40], [74, 33, 69], [148, 98, 6], [0, 0, 1], [0, 1]], ![[76, 34, 20], [109, 127, 52], [4, 45, 79], [63, 57, 78], [103, 77, 56], [122, 8, 37], [10, 84, 34], [59, 128, 143]], ![[0, 1], [135, 86, 43], [26, 8, 156], [131, 156, 45], [153, 53, 38], [149, 57, 120], [90, 79, 128], [76, 34, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 52], []]
 b := ![[], [150, 13, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [128, 16, 28, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8869808, 745725, 44499]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54416, 4575, 273]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [157, 32, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 4, 164], [46, 162, 3], [0, 1]]
 g := ![![[1, 149, 42], [151, 148, 8], [75, 45, 157], [80, 144], [28, 22], [98, 56, 1], []], ![[72, 65, 88, 34], [83, 70, 108, 5], [112, 113, 10, 131], [62, 88], [143, 137], [100, 20, 118, 92], [146, 9]], ![[113, 135, 137, 122], [142, 17, 11, 141], [88, 153, 36, 38], [156, 32], [67, 44], [129, 44, 102, 48], [140, 9]]]
 h' := ![![[10, 4, 164], [7, 32, 83], [82, 70, 141], [163, 127, 149], [96, 110, 155], [145, 96, 32], [0, 0, 1], [0, 1]], ![[46, 162, 3], [48, 41, 157], [135, 98, 87], [73, 48, 43], [11, 22, 64], [90, 107, 53], [57, 7, 162], [10, 4, 164]], ![[0, 1], [55, 94, 94], [62, 166, 106], [165, 159, 142], [38, 35, 115], [6, 131, 82], [9, 160, 4], [46, 162, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 150], []]
 b := ![[], [86, 23, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [157, 32, 111, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-334835, 104208, -30060]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2005, 624, -180]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8424807250462570, -927949257803113, -458824087502994]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-8424807250462570, -927949257803113, -458824087502994]] 
 ![![173, 0, 0], ![0, 173, 0], ![129, 37, 1]] where
  M :=![![![-8424807250462570, -927949257803113, -458824087502994], ![-68344186872351856, -7527761241050832, -3722098114009577], ![-86917345943517009, -9573499340780124, -4733612384844368]]]
  hmulB := by decide  
  f := ![![![-82714836, 5463736, 3721259]], ![![558425155, -94114918, 19876162]], ![![60005303, -15534167, 6398457]]]
  g := ![![![293430636054472, 92766138611605, -458824087502994], ![2380384218698749, 752542595244529, -3722098114009577], ![3027275443360731, 957052941609604, -4733612384844368]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [41, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 172], [0, 1]]
 g := ![![[5, 38], [85], [163, 21], [168, 84], [118], [131, 159], [1]], ![[0, 135], [85], [10, 152], [75, 89], [118], [60, 14], [1]]]
 h' := ![![[141, 172], [92, 111], [64, 137], [32, 59], [70, 55], [165, 139], [132, 141], [0, 1]], ![[0, 1], [0, 62], [5, 36], [47, 114], [40, 118], [42, 34], [118, 32], [141, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [41, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [41, 32, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47520, 1560, 1861]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1113, -389, 1861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![82714836, -5463736, -3721259]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![82714836, -5463736, -3721259]] 
 ![![173, 0, 0], ![163, 1, 0], ![122, 0, 1]] where
  M :=![![![82714836, -5463736, -3721259], ![-558425155, 94114918, -19876162], ![-389400528, -90019131, 108527344]]]
  hmulB := by decide  
  f := ![![![8424807250462570, 927949257803113, 458824087502994]], ![![8332877275709542, 917823643138487, 453817481947963]], ![![6443605956647113, 709730108628670, 350925728671732]]]
  g := ![![![8250274, -5463736, -3721259], ![-77885925, 94114918, -19876162], ![6031109, -90019131, 108527344]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-8424807250462570, -927949257803113, -458824087502994]] ![![82714836, -5463736, -3721259]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [89, 119, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 101, 58], [100, 77, 121], [0, 1]]
 g := ![![[157, 161, 66], [156, 20, 125], [30, 83], [119, 31], [22, 68, 101], [105, 89, 1], []], ![[82, 176, 30, 32], [99, 52, 119, 63], [124, 67], [106, 12], [34, 91, 139, 94], [110, 70, 146, 23], [10, 142]], ![[51, 123, 71, 31], [25, 40, 90, 48], [160, 74], [168, 88], [105, 162, 131, 161], [43, 4, 173, 116], [126, 142]]]
 h' := ![![[168, 101, 58], [78, 147, 148], [62, 40, 29], [91, 26, 158], [11, 38, 116], [142, 169, 97], [0, 0, 1], [0, 1]], ![[100, 77, 121], [104, 99, 53], [54, 52, 78], [23, 113, 70], [68, 58, 38], [123, 156, 87], [126, 60, 77], [168, 101, 58]], ![[0, 1], [144, 112, 157], [2, 87, 72], [82, 40, 130], [101, 83, 25], [61, 33, 174], [39, 119, 101], [100, 77, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 87], []]
 b := ![[], [90, 161, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [89, 119, 90, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3211260, 370172, 20943]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17940, 2068, 117]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [71, 46, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 139, 72], [2, 41, 109], [0, 1]]
 g := ![![[22, 67, 161], [16, 70], [145, 22, 15], [176, 100], [84, 89, 136], [9, 69, 1], []], ![[103, 59, 10, 153], [8, 4], [52, 159, 79, 175], [165, 169], [117, 102, 168, 157], [103, 54, 112, 124], [146, 116]], ![[121, 24, 120, 23], [129, 29], [175, 128], [144, 9], [16, 117, 115, 162], [134, 128, 143, 54], [109, 116]]]
 h' := ![![[67, 139, 72], [72, 92, 60], [22, 140, 147], [74, 159, 167], [9, 119, 171], [85, 117, 91], [0, 0, 1], [0, 1]], ![[2, 41, 109], [50, 100, 34], [165, 67, 179], [152, 168, 14], [144, 73, 13], [8, 0, 28], [96, 54, 41], [67, 139, 72]], ![[0, 1], [59, 170, 87], [118, 155, 36], [82, 35], [129, 170, 178], [162, 64, 62], [48, 127, 139], [2, 41, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 50], []]
 b := ![[], [174, 124, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [71, 46, 112, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4713240, 7240, 14480]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26040, 40, 80]
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


def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383079532876108068049608960550505250498535, 42194243457905807457945149590287228539660, 20862924442966088278888684951315096848004]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![383079532876108068049608960550505250498535, 42194243457905807457945149590287228539660, 20862924442966088278888684951315096848004]] 
 ![![191, 0, 0], ![102, 1, 0], ![170, 0, 1]] where
  M :=![![![383079532876108068049608960550505250498535, 42194243457905807457945149590287228539660, 20862924442966088278888684951315096848004], ![3107638952857999891754078498370635360665292, 342290473134123153292167150023189126489831, 169245368403596860731948378048805949002292], ![3952168315903657947598965693156134344807500, 435311045870446068455655705851674824746172, 215239348188432100018163921564670406027199]]]
  hmulB := by decide  
  f := ![![![2322656299417236687145, -759791371734445371652, 372300735956494253396]], ![![1546557789975762584302, -413243197783790824529, 175032024800927740740]], ![![1224750799532883688714, -588062097789972411460, 343686707914472112535]]]
  g := ![![![-39096494529500101047496715912996641490615, 42194243457905807457945149590287228539660, 20862924442966088278888684951315096848004], ![-317160743117455644337582173153359512417210, 342290473134123153292167150023189126489831, 169245368403596860731948378048805949002292], ![-403352081439347110146417711883291449235214, 435311045870446068455655705851674824746172, 215239348188432100018163921564670406027199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59227427979, -7851235628, 432671406]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![59227427979, -7851235628, 432671406]] 
 ![![191, 0, 0], ![140, 1, 0], ![111, 0, 1]] where
  M :=![![![59227427979, -7851235628, 432671406], ![81901196374, 40928928287, -40121520952], ![-1253159619804, 61385570166, 73199213611]]]
  hmulB := by decide  
  f := ![![![5458847804115048432389, 601264054796100606104, 297294737799881416334]], ![![4233100834292651497494, 466254320200848408383, 230539236075204913532]], ![![3467278209971664915021, 381902890581081939162, 188831710152409208209]]]
  g := ![![![5813475863, -7851235628, 432671406], ![-6254764074, 40928928287, -40121520952], ![-94095561015, 61385570166, 73199213611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![383079532876108068049608960550505250498535, 42194243457905807457945149590287228539660, 20862924442966088278888684951315096848004]] ![![59227427979, -7851235628, 432671406]]
  ![![5458847804115048432389, 601264054796100606104, 297294737799881416334]] where
 M := ![![![5458847804115048432389, 601264054796100606104, 297294737799881416334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![5458847804115048432389, 601264054796100606104, 297294737799881416334]] ![![59227427979, -7851235628, 432671406]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [173, 40, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [160, 95, 150], [5, 97, 43], [0, 1]]
 g := ![![[8, 17, 126], [32, 168], [161, 81], [69, 25], [7, 6], [167, 12], [1]], ![[124, 10, 101, 75], [191, 59], [138, 92], [14, 21], [5, 67], [188, 189], [146, 21, 16, 9]], ![[67, 104, 116, 107], [63, 169], [17, 27], [159, 7], [185, 81], [74, 7], [138, 107, 34, 184]]]
 h' := ![![[160, 95, 150], [70, 75, 133], [3, 84, 19], [8, 17, 9], [65, 19, 5], [73, 66, 149], [20, 153, 165], [0, 1]], ![[5, 97, 43], [70, 4, 26], [66, 125, 161], [89, 68, 142], [52, 2, 54], [96, 173, 35], [179, 5, 162], [160, 95, 150]], ![[0, 1], [120, 114, 34], [156, 177, 13], [190, 108, 42], [171, 172, 134], [36, 147, 9], [183, 35, 59], [5, 97, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 138], []]
 b := ![[], [14, 51, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [173, 40, 28, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12716577, 902275, -525925]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65889, 4675, -2725]
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



lemma PB225I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB225I3 : PrimesBelowBoundCertificateInterval O 137 193 225 where
  m := 11
  g := ![2, 2, 3, 2, 1, 1, 2, 1, 1, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB225I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N1]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![191, 191, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I173N1, I191N0, I191N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [], [], [I173N1], [], [], [I191N0, I191N1, I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
