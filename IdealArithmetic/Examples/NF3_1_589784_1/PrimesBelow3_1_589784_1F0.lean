
import IdealArithmetic.Examples.NF3_1_589784_1.RI3_1_589784_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![0, 1, 0], ![1, 0, 3], ![1, -37, 1]]]
  hmulB := by decide  
  f := ![![![111, -1, 3]], ![![1, 0, 0]], ![![37, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 0, 3], ![0, -37, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6104, -54, 165]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![6104, -54, 165]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![6104, -54, 165], ![111, -1, 3], ![-2034, 18, -55]]]
  hmulB := by decide  
  f := ![![![1, 0, 3]], ![![2, -55, 3]], ![![-18, -18, -55]]]
  g := ![![![3079, -54, 165], ![56, -1, 3], ![-1026, 18, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![0, 1, 0]]
  ![![1, 0, 3]] where
 M := ![![![1, 0, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1, 0, 3]] ![![6104, -54, 165]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32673943851719890764, 5044302130583491023853, 373333706098589052803]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![32673943851719890764, 5044302130583491023853, 373333706098589052803]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![32673943851719890764, 5044302130583491023853, 373333706098589052803], ![5417635836682080076656, -13780673181796075062947, 15506240097849062124362], ![564297657400422390217, -191119183304772236516197, -8736371051212584039094]]]
  hmulB := by decide  
  f := ![![![3083933017880289126634675657917723418400141332, -27282337902506634958363173075516986559241009, 83362949754412548358711119707400819926197227]], ![![1046671209910731680011674534849869083922365850, -9259486978493932531999648110541301809465692, 28292961933768397280777573396083560058223809]], ![![685431760974943970457259682784465530908844533, -6063744187570573934486401923399440993896800, 18528162939643583587570725125258971499266717]]]
  g := ![![![-1794987297610120061964, 5044302130583491023853, 373333706098589052803], ![1230689640209697671747, -13780673181796075062947, 15506240097849062124362], ![66806617337795080981836, -191119183304772236516197, -8736371051212584039094]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4105177223854097181510148060501437, -21556410748718786495423640890425954, 11143221478988402926939090833587294]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![4105177223854097181510148060501437, -21556410748718786495423640890425954, 11143221478988402926939090833587294]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![4105177223854097181510148060501437, -21556410748718786495423640890425954, 11143221478988402926939090833587294], ![-10413189269730383568484550056838660, -408194017498716811115236212782228441, -53526010767167956559331831837690568], ![-155275068496579621618692730893473482, 663868539954734265207405622942712770, -429750428247435597610659853672654395]]]
  hmulB := by decide  
  f := ![![![210955788445715946736393930414625535825715338511030623625057073494801555, -1866242577091256704163263691014652305083442324355760464491938416623450, 5702425017223686006703845979786679513011534025885960415475424591230526]], ![![141915919777188107591776147706007699619786256241197149067032544388070062, -1255474115247649639991632739836970255292768365153810892172504404658269, 3836182440132429302540582288772027207928091701530199950983486174607076]], ![![46886815220646819317261504988723576454831162625347779391620013327803931, -414789143799663576856219626970890391044828211274716087998437365440704, 1267415082857331263630737150430140350738890418260096067816616597959723]]]
  g := ![![![12024925747434422415139446335922017, -21556410748718786495423640890425954, 11143221478988402926939090833587294], ![286500285498290398407106569115102930, -408194017498716811115236212782228441, -53526010767167956559331831837690568], ![-351087240052870851474281374368748209, 663868539954734265207405622942712770, -429750428247435597610659853672654395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5446653677439338995744725, 8873171767318140723852888, -15861136329080515977010606]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-5446653677439338995744725, 8873171767318140723852888, -15861136329080515977010606]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-5446653677439338995744725, 8873171767318140723852888, -15861136329080515977010606], ![-6987964561762375253157718, 581415390498539752153647697, 10758378972873906194548058], ![199206807716284332447980160, -137973719441805015058429584, 590288562265857892877500585]]]
  hmulB := by decide  
  f := ![![![344687228498677282742937836406762994301968924098350617, -3049311831371450419095795452727005198054155401771576, 9317369717087137394320254445403763287985918194565886]], ![![231880838294356750820366710602067582231289870329831848, -2051358232096567228367722992876752583206119968043439, 6268057885715686975224458992676758089931762792794310]], ![![-38285916145472366383646282932524054884628391245520736, 338700385232672258233792802018010957390910510252560, -1034920954972750422002457841967750850521401500786247]]]
  g := ![![![-7730999070691873481150167, 8873171767318140723852888, -15861136329080515977010606], ![-389939581852947293186817704, 581415390498539752153647697, 10758378972873906194548058], ![158384748866631454188279776, -137973719441805015058429584, 590288562265857892877500585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![32673943851719890764, 5044302130583491023853, 373333706098589052803]] ![![4105177223854097181510148060501437, -21556410748718786495423640890425954, 11143221478988402926939090833587294]]
  ![![-110362557275896893110483682195660487695691996168105799158, -1811913782731100090522617284351195745494373510470744097719, -430077597236599362324458340764367851188456693915207785073]] where
 M := ![![![-110362557275896893110483682195660487695691996168105799158, -1811913782731100090522617284351195745494373510470744097719, -430077597236599362324458340764367851188456693915207785073]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-110362557275896893110483682195660487695691996168105799158, -1811913782731100090522617284351195745494373510470744097719, -430077597236599362324458340764367851188456693915207785073]] ![![-5446653677439338995744725, 8873171767318140723852888, -15861136329080515977010606]]
  ![![3, 0, 0]] where
 M := ![![![-72411689284660714199000268503288538161628108985899110499074720679470941903249164888, -995114419724350215735849707315845787669775742614925435248738342293053221258556771815, -271612666109762664318286320672567279878913029128683330718487975695360837276833577659]]]
 hmul := by decide  
 g := ![![![![-24137229761553571399666756167762846053876036328633036833024906893156980634416388296, -331704806574783405245283235771948595889925247538308478416246114097684407086185590605, -90537555369920888106095440224189093292971009709561110239495991898453612425611192553]]]]
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
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 4], [0, 3, 1], [0, 1]]
 g := ![![[4, 3, 1], []], ![[1, 2, 4, 1], [1, 1]], ![[0, 2, 0, 1], [4, 1]]]
 h' := ![![[3, 1, 4], [0, 0, 1], [0, 1]], ![[0, 3, 1], [1, 3, 3], [3, 1, 4]], ![[0, 1], [3, 2, 1], [0, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 3], []]
 b := ![[], [1, 2, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 0, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9915, -59850, -33030]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1983, -11970, -6606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [3, 4], [0, 1]]
 g := ![![[5, 5, 2], [1]], ![[5, 4, 1], [1]], ![[3, 5, 4], [1]]]
 h' := ![![[1, 2], [3, 4, 4], [0, 1]], ![[3, 4], [4, 3, 2], [1, 2]], ![[0, 1], [2, 0, 1], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [2, 4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154056, -92540, 457261]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22008, -13220, 65323]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 8, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6, 5], [4, 4, 6], [0, 1]]
 g := ![![[4, 10, 4], [8, 7, 1], []], ![[5, 8, 6, 9], [1, 5, 4, 3], [4, 3]], ![[10, 1, 0, 8], [0, 9, 7, 7], [3, 3]]]
 h' := ![![[3, 6, 5], [6, 10, 9], [0, 0, 1], [0, 1]], ![[4, 4, 6], [1, 9, 9], [1, 9, 4], [3, 6, 5]], ![[0, 1], [4, 3, 4], [10, 2, 6], [4, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [8, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 8, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-934559208, -1888934718, -2907664518]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84959928, -171721338, -264333138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21753717696061713479, 1794987297610120061964, 32673943851719890764]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-21753717696061713479, 1794987297610120061964, 32673943851719890764]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![-21753717696061713479, 1794987297610120061964, 32673943851719890764], ![1827661241461839952728, -1230689640209697671747, 5417635836682080076656], ![1402899971389481372796, -66806617337795080981836, 564297657400422390217]]]
  hmulB := by decide  
  f := ![![![361239448935787709554414852065403553013521317, -3195742790923358597513246187141860815568892, 9764798994124813693206848270824588558957092]], ![![56080611851905913400347946631883833366956218, -496123032975162637635771256106918869156067, 1515936046892643483621600480849860248474200]], ![![324192312039156260902844830719061977895323216, -2868001396647215336973155736257580178327908, 8763363945518769894363876854434382940309625]]]
  g := ![![![-307985818395149271275, 1794987297610120061964, 32673943851719890764], ![-4670968424484901971050, -1230689640209697671747, 5417635836682080076656], ![9864966366013428819528, -66806617337795080981836, 564297657400422390217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19094032201400021042683, -168917364748081970510, 516137943913097174254]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![19094032201400021042683, -168917364748081970510, 516137943913097174254]] 
 ![![13, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![19094032201400021042683, -168917364748081970510, 516137943913097174254], ![347220579165015203744, -3071723384574404715, 9385849668851262724], ![-6362572691705248061558, 56287168721866817822, -171989088132656375225]]]
  hmulB := by decide  
  f := ![![![3681718747, -36737859962, 9043938370]], ![![-714255989, -39587176981, -4303842282]], ![![-9758194359, 82083404488, -24804782235]]]
  g := ![![![1335225331198072694151, -168917364748081970510, 516137943913097174254], ![24280765211048531823, -3071723384574404715, 9385849668851262724], ![-444927930357792328811, 56287168721866817822, -171989088132656375225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-21753717696061713479, 1794987297610120061964, 32673943851719890764]] ![![19094032201400021042683, -168917364748081970510, 516137943913097174254]]
  ![![3681718747, -36737859962, 9043938370]] where
 M := ![![![3681718747, -36737859962, 9043938370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![3681718747, -36737859962, 9043938370]] ![![19094032201400021042683, -168917364748081970510, 516137943913097174254]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![184608015422, -755782215249, 512762432853]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![184608015422, -755782215249, 512762432853]] 
 ![![17, 0, 0], ![0, 17, 0], ![16, 8, 1]] where
  M :=![![![184608015422, -755782215249, 512762432853], ![-243019782396, -18787602000139, -1754584212894], ![-6908931409485, 21810792769977, -19543384215388]]]
  hmulB := by decide  
  f := ![![![-23849541002318399442436610, 210987473681309003364543, -644685885431006637258069]], ![![-433698411749697633893526, 3836758628846136111943, -11723464387079627164440]], ![![-22183236778366975499980741, 196246338052668215608057, -599643391157799298468714]]]
  g := ![![![-471740641778, -285757745769, 512762432853], ![1637078095524, -279466370411, -1754584212894], ![17987365649219, 10479874499593, -19543384215388]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16], [0, 1]]
 g := ![![[1, 2], [2], [13], [1]], ![[0, 15], [2], [13], [1]]]
 h' := ![![[8, 16], [3, 6], [15, 11], [8, 8], [0, 1]], ![[0, 1], [0, 11], [1, 6], [4, 9], [8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [9, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-606, -65, -1859]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1714, 871, -1859]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23849541002318399442436610, 210987473681309003364543, -644685885431006637258069]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-23849541002318399442436610, 210987473681309003364543, -644685885431006637258069]] 
 ![![17, 0, 0], ![9, 1, 0], ![13, 0, 1]] where
  M :=![![![-23849541002318399442436610, 210987473681309003364543, -644685885431006637258069], ![-433698411749697633893526, 3836758628846136111943, -11723464387079627164440], ![7947218098853388650461371, -70305901036353477391263, 214824232310155139476486]]]
  hmulB := by decide  
  f := ![![![184608015422, -755782215249, 512762432853]], ![![83438373906, -1505273055140, 168251628399]], ![![-265236894647, 705036704220, -757498387547]]]
  g := ![![![-1021618338520417305197800, 210987473681309003364543, -644685885431006637258069], ![-18577894257486923868429, 3836758628846136111943, -11723464387079627164440], ![340426834596973713752260, -70305901036353477391263, 214824232310155139476486]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![184608015422, -755782215249, 512762432853]] ![![-23849541002318399442436610, 210987473681309003364543, -644685885431006637258069]]
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
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16125488128099744279, -87635801520686639622, 43609974968672822246]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![16125488128099744279, -87635801520686639622, 43609974968672822246]] 
 ![![19, 0, 0], ![0, 19, 0], ![6, 12, 1]] where
  M :=![![![16125488128099744279, -87635801520686639622, 43609974968672822246], ![-44025826552013817376, -1597443585712794678823, -219297429593387096620], ![-610955501144760506574, 2719204956641331799062, -1685079387233481318445]]]
  hmulB := by decide  
  f := ![![![173059679793790153841474129618508198955825, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742]], ![![3147050429908982730118274663388439625240, -27840712728585752878873028680581551629, 85069100185394698768175198425384794236]], ![![53602905269449347412898375325725754596496, -474203741014565026217885651983117538310, 1448960231224158794285480315534858463587]]]
  g := ![![![-12922861141259852063, -32155552691829500346, 43609974968672822246], ![66934671105700461176, 54427661547781604243, -219297429593387096620], ![499974780118743547584, 1207376715970689874758, -1685079387233481318445]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 18], [0, 1]]
 g := ![![[14, 9], [4, 6], [5], [1]], ![[0, 10], [1, 13], [5], [1]]]
 h' := ![![[9, 18], [8, 16], [14, 5], [2, 9], [0, 1]], ![[0, 1], [0, 3], [2, 14], [7, 10], [9, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [8, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [17, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93, -338, -348]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![105, 202, -348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173059679793790153841474129618508198955825, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![173059679793790153841474129618508198955825, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742]] 
 ![![19, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![173059679793790153841474129618508198955825, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742], ![3147050429908982730118274663388439625240, -27840712728585752878873028680581551629, 85069100185394698768175198425384794236], ![-57667483802111114965194942482921131904406, 510161462637057630456947351376909884670, -1558831377590379768553922761162108967131]]]
  hmulB := by decide  
  f := ![![![16125488128099744279, -87635801520686639622, 43609974968672822246]], ![![-1468438864416530163, -88688388801762174655, -9246708138142856546]], ![![-32155552691829500346, 143116050349543778898, -88688388801762174655]]]
  g := ![![![9188982655718523571428904176367880335333, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742], ![167099533823029920157744615372053746151, -27840712728585752878873028680581551629, 85069100185394698768175198425384794236], ![-3061981329723588031350099464963054831004, 510161462637057630456947351376909884670, -1558831377590379768553922761162108967131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![16125488128099744279, -87635801520686639622, 43609974968672822246]] ![![173059679793790153841474129618508198955825, -1530990664861794015675049732481527415502, 4678041094770776745793324395869967040742]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10290575743479216, -91036660983613, 278168411464809]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![10290575743479216, -91036660983613, 278168411464809]] 
 ![![23, 0, 0], ![0, 23, 0], ![18, 14, 1]] where
  M :=![![![10290575743479216, -91036660983613, 278168411464809], ![187131750481196, -1655480718717, 5058428513970], ![-3429057598561321, 30335518815973, -92692141702330]]]
  hmulB := by decide  
  f := ![![![-701400, 7942429, -1671459]], ![![6270970, 61142583, 22155828]], ![![4485579, 31528153, 15181754]]]
  g := ![![![229719319004898, -173278018325693, 278168411464809], ![4177392923032, -3151020865839, 5058428513970], ![-76547784692147, 57740239245591, -92692141702330]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [19, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[20, 13], [19, 12], [16, 6], [1]], ![[2, 10], [13, 11], [13, 17], [1]]]
 h' := ![![[11, 22], [7, 6], [18, 9], [4, 11], [0, 1]], ![[0, 1], [4, 17], [2, 14], [10, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [12, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [19, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![298, -7026, 428]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-322, -566, 428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-701400, 7942429, -1671459]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-701400, 7942429, -1671459]] 
 ![![23, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![-701400, 7942429, -1671459], ![6270970, 61142583, 22155828], ![27999937, -273812365, 69085012]]]
  hmulB := by decide  
  f := ![![![10290575743479216, -91036660983613, 278168411464809]], ![![1350385173083428, -11946324507372, 36502767952539]], ![![2087992222558033, -18471642874004, 56441300679205]]]
  g := ![![![-703104, 7942429, -1671459], ![-12518953, 61142583, 22155828], ![21913564, -273812365, 69085012]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![10290575743479216, -91036660983613, 278168411464809]] ![![-701400, 7942429, -1671459]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3094479450716954264633532721768780395777770609133846009194719391475508273647678, 27375638030183778593730771543824367875832585686297620103769684662824386716251, -83648034334899156782705190962681044890072670470136770636660806993501795469573]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-3094479450716954264633532721768780395777770609133846009194719391475508273647678, 27375638030183778593730771543824367875832585686297620103769684662824386716251, -83648034334899156782705190962681044890072670470136770636660806993501795469573]] 
 ![![29, 0, 0], ![0, 29, 0], ![5, 8, 1]] where
  M :=![![![-3094479450716954264633532721768780395777770609133846009194719391475508273647678, 27375638030183778593730771543824367875832585686297620103769684662824386716251, -83648034334899156782705190962681044890072670470136770636660806993501795469573], ![-56272396304715378188974419418856677014240084783839150532891122330677408753322, 497819674314536326559343850418265154918198261214504361730467284058158726523, -1521120244347821001512876331207941262574913411243910325351753005028635320820], ![1031152050048973659986193063095996906556704631327938867743699368584845932351127, -9122195098009926575576255569329072724933624751370696199548648602480762866411, 27873457704498314920290115394242633030750783947512124465500151946882545442774]]]
  hmulB := by decide  
  f := ![![![3501015022848929640514447883061189042, -167146047780695284804326932007810961801, 1384965877056983638990159938524760729]], ![![-165761081903638301165336772069286201072, -47742722428259465002121469842354957931, -500053177465028870773990636084908124674]], ![![-51460317876560029296287268565830750135, 170693522725223778967365798146510827084, -145116874501513820613911127270234728051]]]
  g := ![![![-92284113070429602783448509205357764528531284716660764000393632983034458493097, 24019307334806104581219734456733542310221170670599716730932970365890991395615, -83648034334899156782705190962681044890072670470136770636660806993501795469573], ![-1678165347688837006255518543545412782805707507848951686418357148466697660318, 436785573417141528919391534485579146741982950040199550501534183596111768727, -1521120244347821001512876331207941262574913411243910325351753005028635320820], ![30751198673326968461542844349130473841481059020357870531593055477601145004733, -8003788163241256756479213059423108171411720563154058342191374626811762979607, 27873457704498314920290115394242633030750783947512124465500151946882545442774]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [11, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [9], [0, 5], [0, 1]], ![[], [9], [0, 24], [0, 28]]]
 h' := ![![[0, 28], [17], [0, 3], [0, 18], [0, 1]], ![[0, 1], [17], [0, 26], [0, 11], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [11, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-306, 798, -908]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![146, 278, -908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3501015022848929640514447883061189042, 167146047780695284804326932007810961801, -1384965877056983638990159938524760729]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-3501015022848929640514447883061189042, 167146047780695284804326932007810961801, -1384965877056983638990159938524760729]] 
 ![![29, 0, 0], ![4, 1, 0], ![24, 0, 1]] where
  M :=![![![-3501015022848929640514447883061189042, 167146047780695284804326932007810961801, -1384965877056983638990159938524760729], ![165761081903638301165336772069286201072, 47742722428259465002121469842354957931, 500053177465028870773990636084908124674], ![183765638305379088472208851270108090549, -6167784177361041734092214565026708457889, 214888770208954749806448401850165919732]]]
  hmulB := by decide  
  f := ![![![3094479450716954264633532721768780395777770609133846009194719391475508273647678, -27375638030183778593730771543824367875832585686297620103769684662824386716251, 83648034334899156782705190962681044890072670470136770636660806993501795469573]], ![![428765179281811463335279493327378560693976638666180109907302368559748638046346, -3793116268794815541430428621576404712353397965738102923338248480529507089363, 11590112330480843039045987592480417959409158458337620443861895895828821282728]], ![![2525391543695100989352365250322576985934820344409805701825157449200943194317005, -22341141987117267574964215913188129527415463162750765044514613217424293735297, 68264805735623498202228774748624222218310114046061047269460662617143467097482]]]
  g := ![![![-22029173279181464190415804737576233750, 167146047780695284804326932007810961801, -1384965877056983638990159938524760729], ![-414706416102416981290307737011652711132, 47742722428259465002121469842354957931, 500053177465028870773990636084908124674], ![679226615956366621706424326447343443053, -6167784177361041734092214565026708457889, 214888770208954749806448401850165919732]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-3094479450716954264633532721768780395777770609133846009194719391475508273647678, 27375638030183778593730771543824367875832585686297620103769684662824386716251, -83648034334899156782705190962681044890072670470136770636660806993501795469573]] ![![-3501015022848929640514447883061189042, 167146047780695284804326932007810961801, -1384965877056983638990159938524760729]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14891742196400471985153491652356711656303875289138777980679486146671086248797823145408, -131741364096963300437434276269178908583283423492461532506173354794357878001275001853, 402544267101973300817226414084168090929721138963184438489331669358144693142035914363]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![14891742196400471985153491652356711656303875289138777980679486146671086248797823145408, -131741364096963300437434276269178908583283423492461532506173354794357878001275001853, 402544267101973300817226414084168090929721138963184438489331669358144693142035914363]] 
 ![![31, 0, 0], ![0, 31, 0], ![22, 24, 1]] where
  M :=![![![14891742196400471985153491652356711656303875289138777980679486146671086248797823145408, -131741364096963300437434276269178908583283423492461532506173354794357878001275001853, 402544267101973300817226414084168090929721138963184438489331669358144693142035914363], ![270802903005010000379792137814989182346437715470722905983158314563786815140760912510, -2395686372540145083885668757507708095806852499046243425785619580267397457505686023, 7320174811083399504923585276631365179870868485799840970811604975071059138210908804], ![-4962272569320642910244151245279195999739937091050674794378153387092094195705705974209, 43899266363962506378351252949602526424833001662863440856434095093505168342744096205, -134137050469503445521319945026686616679090275991507775931958974374625275458780687876]]]
  hmulB := by decide  
  f := ![![![18712619043003667403124899362810147137688, -348912211908816228022865167057553719398123, 37115465979788516724328130260861886452727]], ![![-311796745929027711298537036796691832945396, -1354559622209171451397015920289079651613211, -1009621169746660167344267370911799271741642]], ![![-253733615710221381193901413784731519693265, -894230107940172052060559424006611241457353, -810252892144596268637002552370672722285508]]]
  g := ![![![194702203876034173134661630403387537285484201030603881739167400670706548376549452562, -315896895953042661937124781106103648093438411568028646975810755464188081077746353115, 402544267101973300817226414084168090929721138963184438489331669358144693142035914363], ![3540614747134684234563653604164488657718664799455690471783967906845919809681319962, -5744512317372313974259732754730982981055086972846529894363359321999123121760241849, 7320174811083399504923585276631365179870868485799840970811604975071059138210908804], ![-64879272870695713186293950151357755896772613523790442705646966156462520503630027127, 105264144439743393512581610760970365378161278240614518168498370325306831592047761459, -134137050469503445521319945026686616679090275991507775931958974374625275458780687876]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [10, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 30], [0, 1]]
 g := ![![[7, 28], [16, 2], [6, 2], [23, 1]], ![[0, 3], [0, 29], [21, 29], [15, 30]]]
 h' := ![![[23, 30], [26, 11], [2, 8], [18, 23], [0, 1]], ![[0, 1], [0, 20], [0, 23], [20, 8], [23, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [10, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [10, 8, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-389, -864, -1245]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![871, 936, -1245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18712619043003667403124899362810147137688, 348912211908816228022865167057553719398123, -37115465979788516724328130260861886452727]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-18712619043003667403124899362810147137688, 348912211908816228022865167057553719398123, -37115465979788516724328130260861886452727]] 
 ![![31, 0, 0], ![20, 1, 0], ![22, 0, 1]] where
  M :=![![![-18712619043003667403124899362810147137688, 348912211908816228022865167057553719398123, -37115465979788516724328130260861886452727], ![311796745929027711298537036796691832945396, 1354559622209171451397015920289079651613211, 1009621169746660167344267370911799271741642], ![794297803666278428714802730187896356830847, -12464366248868738236154073617999144980297827, 1703471834117987679419881087346633371011334]]]
  hmulB := by decide  
  f := ![![![-14891742196400471985153491652356711656303875289138777980679486146671086248797823145408, 131741364096963300437434276269178908583283423492461532506173354794357878001275001853, -402544267101973300817226414084168090929721138963184438489331669358144693142035914363]], ![![-9616311188097240313014504038224168461562062693491815565147512298322113283583781413570, 85071708655219553349437780456164060637466945882202480437072668240884676047838894293, -259942113446791916640304898934193328508848182185467374540562741681869836192868683744]], ![![-10408259862951281960101053713115111627062752234516207767115178769021671073478916233057, 92077765928039680749845252418462369755077494037783557234818700334915101538235675631, -281349575024964812014763263381451980121766928425759673252688314564663160440839013810]]]
  g := ![![![-199368277602063898707264818541126549456134, 348912211908816228022865167057553719398123, -37115465979788516724328130260861886452727], ![-1580356820409062096716634307388531779923708, 1354559622209171451397015920289079651613211, 1009621169746660167344267370911799271741642], ![6858233626788558522727706166727253606468969, -12464366248868738236154073617999144980297827, 1703471834117987679419881087346633371011334]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![14891742196400471985153491652356711656303875289138777980679486146671086248797823145408, -131741364096963300437434276269178908583283423492461532506173354794357878001275001853, 402544267101973300817226414084168090929721138963184438489331669358144693142035914363]] ![![-18712619043003667403124899362810147137688, 348912211908816228022865167057553719398123, -37115465979788516724328130260861886452727]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB218I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB218I0 : PrimesBelowBoundCertificateInterval O 1 31 218 where
  m := 11
  g := ![3, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB218I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![343]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![529, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
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
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I5N0, I13N0, I13N1, I17N1, I19N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1, I3N2], [I5N0], [], [], [I13N0, I13N1, I13N1], [I17N1], [I19N1], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
