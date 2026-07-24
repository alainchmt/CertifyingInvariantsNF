
import IdealArithmetic.Examples.NF3_1_371640_1.RI3_1_371640_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 3, 3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![5, 3, 3]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 3, 3], ![-204, -58, 21], ![-252, -108, -55]]]
  hmulB := by decide  
  f := ![![![5458, -159, 237]], ![![-5527, 161, -240]], ![![3708, -108, 161]]]
  g := ![![![1, 3, 3], ![-73, -58, 21], ![-72, -108, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, 2, -3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-69, 2, -3]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-69, 2, -3], ![209, -6, 9], ![-93, 3, -4]]]
  hmulB := by decide  
  f := ![![![3, 1, 0]], ![![2, 2, 3]], ![![-33, -10, 2]]]
  g := ![![![-34, 2, -3], ![103, -6, 9], ![-46, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![5, 3, 3]] ![![-69, 2, -3]]
  ![![3, 1, 0]] where
 M := ![![![3, 1, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![-69, 2, -3]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62408666907817320244059014870, 21574771070952958648032913763, 2105641671080650354432777608]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![62408666907817320244059014870, 21574771070952958648032913763, 2105641671080650354432777608]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![62408666907817320244059014870, 21574771070952958648032913763, 2105641671080650354432777608], ![-123714504233611915807828741189, 18190191815123662800970685102, 131554268096798402242630260186], ![-1520243828961963902030762713767, -484654817556221886925182853143, 39764962886076621449003598865]]]
  hmulB := by decide  
  f := ![![![-64481742105615138342292455584283422805739828827874557473828, 1878429350848414736757676432486369432304178028327032500939, -2799951191704321347966040555237283803650629890123825543902]], ![![43531106490943816468040673053191843026152603872998812518783, -1268112576325325099415975830604697832257474368982396183649, 1890224573893948574871325828147882995507936129904847972610]], ![![-29204119110991932205596355171000077924742945200902619802087, 850750502582703582526467748781832992123903252329900212937, -1268112576325325099415975830604697832257474368982396183649]]]
  g := ![![![13611298612288120532008700369, 21574771070952958648032913763, 2105641671080650354432777608], ![-47301565349578526202933142097, 18190191815123662800970685102, 131554268096798402242630260186], ![-345196337135247338368526620208, -484654817556221886925182853143, 39764962886076621449003598865]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12112894920575701, 15822342987178376, 26314598035024010]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![12112894920575701, 15822342987178376, 26314598035024010]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![12112894920575701, 15822342987178376, 26314598035024010], ![-1799884921429478314, -540493663814928509, 121248655958094266], ![-1486460636640668094, -726988173256106046, -524671320827750133]]]
  hmulB := by decide  
  f := ![![![-371727863397541507492484122870773933, 10828871961778254572478260687440452, -16141311325070602025250269813293106]], ![![127041208865522259776592877354372300, -3700860549167451939090645138912601, 5516432598485907119706251561587798]], ![![-168357498495546845040748646744664866, 4904452892905228118903524254382366, -7310484536426870129916732034726085]]]
  g := ![![![-6510597017927017, 15822342987178376, 26314598035024010], ![-239632531266540432, -540493663814928509, 121248655958094266], ![-10828096709485334, -726988173256106046, -524671320827750133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![62408666907817320244059014870, 21574771070952958648032913763, 2105641671080650354432777608]] ![![12112894920575701, 15822342987178376, 26314598035024010]]
  ![![-41206108968445210186002053111994221232364200864, -12204352320910495479915981353786282007262936215, 3153401181781702050006991929427351893418389794]] where
 M := ![![![-41206108968445210186002053111994221232364200864, -12204352320910495479915981353786282007262936215, 3153401181781702050006991929427351893418389794]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-41206108968445210186002053111994221232364200864, -12204352320910495479915981353786282007262936215, 3153401181781702050006991929427351893418389794]] ![![12112894920575701, 15822342987178376, 26314598035024010]]
  ![![3, 0, 0]] where
 M := ![![![16779897721944425671121132724699574396206144678669237183755103210, 3651912546464227214418648717432994552419187949020199792362642047, -4218582672986673308919629365203156208462373716856461190247330432]]]
 hmul := by decide  
 g := ![![![![5593299240648141890373710908233191465402048226223079061251701070, 1217304182154742404806216239144331517473062649673399930787547349, -1406194224328891102973209788401052069487457905618820396749110144]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796]] 
 ![![5, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796], ![-2613731618704177579106032828, -659489248161137631093706065, 455278954812510526869538372], ![-5371808800427320495156968564, -2040664750689406419988723956, -590090413791597754527700969]]]
  hmulB := by decide  
  f := ![![![-1318229998155120728781540660282316301302395373359316617, 38401597705713972993369858611714225784307611639822952, -57240693780098742123570740384437766517901701029526452]], ![![797601893706505435903950189027584023103904996535429628, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252]], ![![-621865966629580746694099959744806276530219012212840705, 18115690517440334397232786706456396416474656529287548, -27002904969486382663351198796369349032010748225792925]]]
  g := ![![![23645944748857543675289971, 69398834369539876566005096, 38885948595271267473507796], ![-613802114703337621195114240, -659489248161137631093706065, 455278954812510526869538372], ![-956343677327144548125853519, -2040664750689406419988723956, -590090413791597754527700969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8645305150, 5015942265, 4805496872]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![8645305150, 5015942265, 4805496872]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![8645305150, 5015942265, 4805496872], ![-326563341903, -92270129162, 34901150462], ![-418182469365, -177417240645, -87254186897]]]
  hmulB := by decide  
  f := ![![![-14243020905215484918304, 414916031103547260735, -618465972766497057694]], ![![-2776603093774019086319, 80885729459028467242, -120566735442240344812]], ![![-3870443310929461025061, 112750587664592677995, -168063889203099889199]]]
  g := ![![![-2283692782, 5015942265, 4805496872], ![8503434949, -92270129162, 34901150462], ![58297298643, -177417240645, -87254186897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796]] ![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796]]
  ![![-365592474075211509875021129376613954937346001278778631, -114217325175565534048284992337150392135977705723878720, 14759195237815800761030376474916448258129538959636584]] where
 M := ![![![-365592474075211509875021129376613954937346001278778631, -114217325175565534048284992337150392135977705723878720, 14759195237815800761030376474916448258129538959636584]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-365592474075211509875021129376613954937346001278778631, -114217325175565534048284992337150392135977705723878720, 14759195237815800761030376474916448258129538959636584]] ![![8645305150, 5015942265, 4805496872]]
  ![![5, 0, 0]] where
 M := ![![![27966496203240709451868554541165957327010241131115395306258505350, 6086520910773712024031081195721657587365313248366999653937736745, -7030971121644455514866048942005260347437289528094101983745550720]]]
 hmul := by decide  
 g := ![![![![5593299240648141890373710908233191465402048226223079061251701070, 1217304182154742404806216239144331517473062649673399930787547349, -1406194224328891102973209788401052069487457905618820396749110144]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 2, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 3], [6, 0, 4], [0, 1]]
 g := ![![[5, 1, 2], [1]], ![[1, 3, 0, 3], [6, 1, 5, 6]], ![[5, 3, 6, 1], [2, 1, 3, 1]]]
 h' := ![![[4, 6, 3], [5, 5, 3], [0, 1]], ![[6, 0, 4], [3, 1, 1], [4, 6, 3]], ![[0, 1], [2, 1, 3], [6, 0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [4, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 2, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-445802, -181132, -75264]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63686, -25876, -10752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-182476884806403296347238507799144049007338187085535, 5315767302166054989163963088997023193516274023234, -7923581999930009186540897641085691515010362358716]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-182476884806403296347238507799144049007338187085535, 5315767302166054989163963088997023193516274023234, -7923581999930009186540897641085691515010362358716]] 
 ![![11, 0, 0], ![0, 11, 0], ![6, 1, 1]] where
  M :=![![![-182476884806403296347238507799144049007338187085535, 5315767302166054989163963088997023193516274023234, -7923581999930009186540897641085691515010362358716], ![552042925297336688860485900323909737729231276774638, -16081662807873103429879657336344527192120577552499, 23971021813066320748442880892896447646087281780688], ![-247934213850507656454199988524509227627467472222406, 7222616653462983025670239747347885661313680892826, -10765895505707048440715694247347503998604303529265]]]
  hmulB := by decide  
  f := ![![![-3299032416013602414167177, -962800684580484422361054, 284308690844570050520572]], ![![-20580100352855817908280522, -9269514923749573475099189, -5492495416638336483645752]], ![![1981302002222494726529142, 82533180208103827500731, -1274450807263724916180233]]]
  g := ![![![-12266853891529385566181192904784536356116001175749, 1203577209281460379609532793643883155320603307450, -7923581999930009186540897641085691515010362358716], ![37110617674448978579075328633321004713882507826410, -3641153147358129470756594384476452258018896303017, 23971021813066320748442880892896447646087281780688], ![-16667167346933215073627802094584018512349241004256, 1635319287197275587853266726790489969083453129281, -10765895505707048440715694247347503998604303529265]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[9, 1], [4, 5], [1]], ![[2, 10], [2, 6], [1]]]
 h' := ![![[4, 10], [3, 10], [9, 4], [0, 1]], ![[0, 1], [10, 1], [3, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [6, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1077, -1465, -3434]
  a := ![2, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1971, 179, -3434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3299032416013602414167177, -962800684580484422361054, 284308690844570050520572]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-3299032416013602414167177, -962800684580484422361054, 284308690844570050520572]] 
 ![![11, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![-3299032416013602414167177, -962800684580484422361054, 284308690844570050520572], ![-20580100352855817908280522, -9269514923749573475099189, -5492495416638336483645752], ![62168616873384874385104146, 15954184013521622111773554, -10232315608330057897460243]]]
  hmulB := by decide  
  f := ![![![-182476884806403296347238507799144049007338187085535, 5315767302166054989163963088997023193516274023234, -7923581999930009186540897641085691515010362358716]], ![![-16169510357116045138951648261151496209101951960682, 471036945526465138797835910876687780176774412767, -702118744241246908883700879222392583086742514016]], ![![-72305897115428867772355955629267397695407457589001, 2106356232723740726651102637667177749260227542048, -3139694682317916000030762470054961685785035509583]]]
  g := ![![![-27341431838670443298607, -962800684580484422361054, 284308690844570050520572], ![2997767781096135040277590, -9269514923749573475099189, -5492495416638336483645752], ![2640802513117141784580969, 15954184013521622111773554, -10232315608330057897460243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-182476884806403296347238507799144049007338187085535, 5315767302166054989163963088997023193516274023234, -7923581999930009186540897641085691515010362358716]] ![![-3299032416013602414167177, -962800684580484422361054, 284308690844570050520572]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 4, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 8, 8], [0, 4, 5], [0, 1]]
 g := ![![[11, 6, 1], [6, 3], [1]], ![[2, 0, 6, 8], [5, 9], [11, 6, 9, 5]], ![[0, 8], [2, 1], [2, 2, 7, 8]]]
 h' := ![![[4, 8, 8], [5, 12, 12], [11, 9, 4], [0, 1]], ![[0, 4, 5], [12, 6, 1], [3, 3, 10], [4, 8, 8]], ![[0, 1], [12, 8], [9, 1, 12], [0, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [8, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 4, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46026875414, -21397081420, -13863281510]
  a := ![-65, 1, -326]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3540528878, -1645929340, -1066406270]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1069165476297154756013620217159443340961735926692922414230377, 31146053844216953315834057815463905301067951298547684123608, -46425717602109418993193885817916535714782333219727023498438]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1069165476297154756013620217159443340961735926692922414230377, 31146053844216953315834057815463905301067951298547684123608, -46425717602109418993193885817916535714782333219727023498438]] 
 ![![17, 0, 0], ![0, 17, 0], ![5, 8, 1]] where
  M :=![![![-1069165476297154756013620217159443340961735926692922414230377, 31146053844216953315834057815463905301067951298547684123608, -46425717602109418993193885817916535714782333219727023498438], ![3234520568389766863846212179251704869621048943459712305515830, -94225406652856957156548614983196090951306929078654920763179, 140450605463192300901810461074866896091625374571559081243210], ![-1452691951219328493894641701998261430051953641303884852052382, 42318633303085265265393073144006024399308021026403985880802, -63079352808640003840714557167732185650238977780107236639571]]]
  hmulB := by decide  
  f := ![![![-367609860674241560096429517, -20446577985676526699012170876, -45255183812986567650498605134]], ![![3102161105110396641185391583370, 949991250212043679100374278297, -167934651727045727844571630390]], ![![1582652495869781222274821728637, 506229588627174845573215766906, -37659321214995971094570821257]]]
  g := ![![![-49237464016859274179273575768815333081636721211428664514011, 23679517333005429721257949668164481824666271591550816006536, -46425717602109418993193885817916535714782333219727023498438], ![148956914180812079961009404345727669950760121800112758782340, -71637073550493844963001900210713603510841760332419268865227, 140450605463192300901810461074866896091625374571559081243210], ![-66899716892713439687709936244682382458868161906079333462031, 32173732692482664470065266499168441741248226074544816411610, -63079352808640003840714557167732185650238977780107236639571]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[6, 1], [8], [1], [1]], ![[5, 16], [8], [1], [1]]]
 h' := ![![[16, 16], [12, 1], [6, 5], [14, 16], [0, 1]], ![[0, 1], [11, 16], [1, 12], [15, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [14, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-735, -1992, -3530]
  a := ![-2, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![995, 1544, -3530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-367609860674241560096429517, -20446577985676526699012170876, -45255183812986567650498605134]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-367609860674241560096429517, -20446577985676526699012170876, -45255183812986567650498605134]] 
 ![![17, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![-367609860674241560096429517, -20446577985676526699012170876, -45255183812986567650498605134], ![3102161105110396641185391583370, 949991250212043679100374278297, -167934651727045727844571630390], ![2089641638206478856989318867454, 1108205894894005575436734665406, 929544672226367152401362107421]]]
  hmulB := by decide  
  f := ![![![-1069165476297154756013620217159443340961735926692922414230377, 31146053844216953315834057815463905301067951298547684123608, -46425717602109418993193885817916535714782333219727023498438]], ![![64481742105615138342292455584283422805739828827874557473828, -1878429350848414736757676432486369432304178028327032500939, 2799951191704321347966040555237283803650629890123825543902]], ![![-588589162446856855411976672898459303396814179696897892111494, 17146297885695346576003855039277486282814801847928556404098, -25557946683853844458015626100650851256970449619877848507475]]]
  g := ![![![23680412742033609002465691371, -20446577985676526699012170876, -45255183812986567650498605134], ![149744459911922065043600945288, 949991250212043679100374278297, -167934651727045727844571630390], ![-444889854670145265476179254278, 1108205894894005575436734665406, 929544672226367152401362107421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1069165476297154756013620217159443340961735926692922414230377, 31146053844216953315834057815463905301067951298547684123608, -46425717602109418993193885817916535714782333219727023498438]] ![![-367609860674241560096429517, -20446577985676526699012170876, -45255183812986567650498605134]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6598955753294214782553638223283, -192235379615440558797115405464, 286542413745227410210361703424]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![6598955753294214782553638223283, -192235379615440558797115405464, 286542413745227410210361703424]] 
 ![![19, 0, 0], ![9, 1, 0], ![12, 0, 1]] where
  M :=![![![6598955753294214782553638223283, -192235379615440558797115405464, 286542413745227410210361703424], ![-19963661928036131863312072941720, 581565064644439168136042451379, -866869863947415942572330729360], ![8966104987286987403845537425656, -261193234254159418416002036616, 389329685028998609338927045915]]]
  hmulB := by decide  
  f := ![![![2912238781821025, 930855989306376, -70759888598656]], ![![1685444070473835, 672415807692115, 256712476307984]], ![![-1485305239542516, -385068714461976, 235785987816595]]]
  g := ![![![257398168678444783642280864809, -192235379615440558797115405464, 286542413745227410210361703424], ![-778700481182478582403604539569, 581565064644439168136042451379, -866869863947415942572330729360], ![349730940801391518816970063380, -261193234254159418416002036616, 389329685028998609338927045915]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23254711, 6455388, -2741840]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![23254711, 6455388, -2741840]] 
 ![![19, 0, 0], ![14, 1, 0], ![15, 0, 1]] where
  M :=![![![23254711, 6455388, -2741840], ![195642348, 80833351, 35990488], ![-404294172, -94435548, 87288739]]]
  hmulB := by decide  
  f := ![![![10454622735001813, -304555515347412, 453964679455184]], ![![6038768415382646, -175916460443201, 262217742091752]], ![![9001273757482677, -262217742091752, 390856796995963]]]
  g := ![![![-1368059, 6455388, -2741840], ![-77677994, 80833351, 35990488], ![-20606715, -94435548, 87288739]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![6598955753294214782553638223283, -192235379615440558797115405464, 286542413745227410210361703424]] ![![23254711, 6455388, -2741840]]
  ![![10454622735001813, -304555515347412, 453964679455184]] where
 M := ![![![10454622735001813, -304555515347412, 453964679455184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![10454622735001813, -304555515347412, 453964679455184]] ![![23254711, 6455388, -2741840]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10989486320022676612845948, -320136723670809734009539, 477189733297952320359672]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![10989486320022676612845948, -320136723670809734009539, 477189733297952320359672]] 
 ![![23, 0, 0], ![0, 23, 0], ![15, 5, 1]] where
  M :=![![![10989486320022676612845948, -320136723670809734009539, 477189733297952320359672], ![-33246228321229519838826907, 968501920765677885292836, -1443630608726906083697562], ![14931587933816586841263111, -434974802382280391194761, 648365197094868151283297]]]
  hmulB := by decide  
  f := ![![![428794682070, 80468143117, -136420255038]], ![![9493465740739, 3293620037868, 346388603664]], ![![2191010908054, 783982398096, 133031624945]]]
  g := ![![![166593057415364861193516, -117655886528720492861213, 477189733297952320359672], ![-503989964796779503624499, 355941520191313404512202, -1443630608726906083697562], ![226352607712763677044072, -159860903819853093374402, 648365197094868151283297]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22], [0, 1]]
 g := ![![[12, 6], [6, 3], [8, 4], [1]], ![[0, 17], [0, 20], [0, 19], [1]]]
 h' := ![![[21, 22], [22, 11], [14, 7], [19, 21], [0, 1]], ![[0, 1], [0, 12], [0, 16], [0, 2], [21, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [4, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1364, -792, -738]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![422, 126, -738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-428794682070, -80468143117, 136420255038]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-428794682070, -80468143117, 136420255038]] 
 ![![23, 0, 0], ![15, 1, 0], ![1, 0, 1]] where
  M :=![![![-428794682070, -80468143117, 136420255038], ![-9493465740739, -3293620037868, -346388603664], ![3505998049503, -356472820113, -3374088180985]]]
  hmulB := by decide  
  f := ![![![-10989486320022676612845948, 320136723670809734009539, -477189733297952320359672]], ![![-5721568107787418667559231, 166676040621585570645663, -248444147423581683552066]], ![![-1127003228427794063222133, 32830935915351744574100, -48937170886644368332303]]]
  g := ![![![27904661289, -80468143117, 136420255038], ![1750314062215, -3293620037868, -346388603664], ![531616457921, -356472820113, -3374088180985]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![10989486320022676612845948, -320136723670809734009539, 477189733297952320359672]] ![![-428794682070, -80468143117, 136420255038]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 21, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 24, 13], [21, 4, 16], [0, 1]]
 g := ![![[3, 27, 24], [14, 20], [23, 18, 4], [1]], ![[11, 26, 5, 16], [10, 24], [25, 7, 21, 9], [5, 13, 2, 22]], ![[20, 20, 6, 16], [6, 7], [21, 27, 7, 1], [1, 19, 13, 7]]]
 h' := ![![[6, 24, 13], [27, 25, 16], [17, 21, 22], [2, 8, 27], [0, 1]], ![[21, 4, 16], [16, 12, 12], [5, 0, 13], [23, 19, 9], [6, 24, 13]], ![[0, 1], [18, 21, 1], [21, 8, 23], [12, 2, 22], [21, 4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 13], []]
 b := ![[], [9, 10, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 21, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7533069, 1763142, -1665702]
  a := ![2, 19, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![259761, 60798, -57438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [14, 12, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 25], [8, 5], [0, 1]]
 g := ![![[1, 29, 20], [2, 15, 4], [2, 21, 5], [1]], ![[12, 24, 7], [18, 24, 20], [6, 1, 25], [1]], ![[25, 9, 4], [6, 23, 7], [25, 9, 1], [1]]]
 h' := ![![[17, 25], [3, 23, 12], [3, 2, 2], [17, 19, 25], [0, 1]], ![[8, 5], [18, 18, 29], [26, 14, 10], [1, 25, 1], [17, 25]], ![[0, 1], [25, 21, 21], [23, 15, 19], [2, 18, 5], [8, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26], []]
 b := ![[], [6, 6, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [14, 12, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219666, -351261, -630633]
  a := ![-2, 3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7086, -11331, -20343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB173I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB173I0 : PrimesBelowBoundCertificateInterval O 1 31 173 where
  m := 11
  g := ![3, 3, 3, 1, 2, 1, 2, 3, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB173I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0]
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
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I17N1, I19N0, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1, I3N1], [I5N0, I5N0, I5N1], [], [I11N0, I11N1], [], [I17N1], [I19N0, I19N1, I19N1], [I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
