
import IdealArithmetic.Examples.NF3_1_311116_1.RI3_1_311116_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179], ![366064934107898463133412670, 37055960406180573620545212, 25331220078631244673017497], ![328933632948314194058284965, 33297239213852544583611725, 22761782053184846026907874]]]
  hmulB := by decide  
  f := ![![![7535996446963, -476234376029, -548382909286]], ![![-26559030442006, 4698795387296, -1428703128087]], ![![-10087743390915, -3780934510130, 5651264139354]]]
  g := ![![![21152300908673054556225474, 4764726117665242531212446, 3257136627360210514257179], ![164504486850858944756433729, 37055960406180573620545212, 25331220078631244673017497], ![147818196867230824737336620, 33297239213852544583611725, 22761782053184846026907874]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179]] ![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179]]
  ![![5031102568405563371783396024895265387145099212703791, 509287615948810317371956604403422392524247177334051, 348145791972753763204499316104701894558000382300634]] where
 M := ![![![5031102568405563371783396024895265387145099212703791, 509287615948810317371956604403422392524247177334051, 348145791972753763204499316104701894558000382300634]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![5031102568405563371783396024895265387145099212703791, 509287615948810317371956604403422392524247177334051, 348145791972753763204499316104701894558000382300634]] ![![47069327935011351643663394, 4764726117665242531212446, 3257136627360210514257179]]
  ![![2, 0, 0]] where
 M := ![![![537759814390495227471477446983697031025947798476954191272470251730378329720634, 54436261256904810446100473931077888886922840157135979600447648793888840530248, 37212283774097782957206069312044783140588078036729765301464260115665948948052]]]
 hmul := by decide  
 g := ![![![![268879907195247613735738723491848515512973899238477095636235125865189164860317, 27218130628452405223050236965538944443461420078567989800223824396944420265124, 18606141887048891478603034656022391570294039018364882650732130057832974474026]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9803135724921549, 1235047213333040, 28332564764878]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-9803135724921549, 1235047213333040, 28332564764878]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-9803135724921549, 1235047213333040, 28332564764878], ![6765058634605944, -7503036686844737, 7381950715233362], ![131770142848370274, -6871964549465558, -11208178326843857]]]
  hmulB := by decide  
  f := ![![![134823876799993104737187352776605, 13647929028448601795495790063356, 9329637932674089412997521627566]], ![![349514894604715820663406568655732, 35380635753615257283397934379307, 24185978746005840453325739584190]], ![![314062324303341965790895531357062, 31791848850038696024659390181206, 21732706725166655487902144315951]]]
  g := ![![![-3267711908307183, 1235047213333040, 28332564764878], ![2255019544868648, -7503036686844737, 7381950715233362], ![43923380949456758, -6871964549465558, -11208178326843857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134823876799993104737187352776605, -13647929028448601795495790063356, -9329637932674089412997521627566]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-134823876799993104737187352776605, -13647929028448601795495790063356, -9329637932674089412997521627566]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 3]] where
  M :=![![![-134823876799993104737187352776605, -13647929028448601795495790063356, -9329637932674089412997521627566], ![-1048544683814147461990219705967196, -106141907260845771850193803137921, -72557936238017521359977218752570], ![-942186972910025897372686594071186, -95375546550116088073978170543618, -65198120175499966463706432947853]]]
  hmulB := by decide  
  f := ![![![9803135724921549, -1235047213333040, -28332564764878]], ![![1012692363438535, 2089329824503899, -2470094426666080]], ![![-131770142848370274, 6871964549465558, 11208178326843857]]]
  g := ![![![-40391982590514834313897187571083, -13647929028448601795495790063356, -3109879310891363137665840542522], ![-314134258851100563380008634276425, -106141907260845771850193803137921, -24185978746005840453325739584190], ![-282270475453303269766236141175856, -95375546550116088073978170543618, -21732706725166655487902144315951]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1573, 964, -330]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![203, 964, -110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-9803135724921549, 1235047213333040, 28332564764878]] ![![-134823876799993104737187352776605, -13647929028448601795495790063356, -9329637932674089412997521627566]]
  ![![3, 0, 0]] where
 M := ![![![-3, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28396714811326112, 5794471464503019, -2385096732371446]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-28396714811326112, 5794471464503019, -2385096732371446]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-28396714811326112, 5794471464503019, -2385096732371446], ![-240207032702607111, -2497191488091398, 37151925519389560], ![761753431911498474, -80083666702075588, -19880605881600455]]]
  hmulB := by decide  
  f := ![![![3024908100420762440943884296447370, 306204895245409181854470484133893, 209319729015091726465756723660132]], ![![5914992324041531777150581240118135, 598761861462369761913445178204430, 409309820097509363518515925692698]], ![![4227780826528792646346935807566584, 427969095962857542344510968947830, 292556966216960580058974694070537]]]
  g := ![![![-7997131548066430, 5794471464503019, -2385096732371446], ![-47042529945284863, -2497191488091398, 37151925519389560], ![184384153063129930, -80083666702075588, -19880605881600455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, -1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![7, 0, -1]] 
 ![![5, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![7, 0, -1], ![-108, 13, 1], ![57, -19, 13]]]
  hmulB := by decide  
  f := ![![![188, 19, 13]], ![![405, 41, 28]], ![![375, 38, 26]]]
  g := ![![![2, 0, -1], ![-30, 13, 1], ![15, -19, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![258093247914286281396687737954031257, 26126220472664448982468215506222750, 17859719013125917241591175320882203]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![258093247914286281396687737954031257, 26126220472664448982468215506222750, 17859719013125917241591175320882203]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![258093247914286281396687737954031257, 26126220472664448982468215506222750, 17859719013125917241591175320882203], ![2007228314835592409039251581173946174, 203187374780859675912077117041183539, 138897603822860776653218117716454297], ![1803627827299583207335870281381771429, 182577338413405733695423038059425357, 124808713362866328964672470522515289]]]
  hmulB := by decide  
  f := ![![![-960530435590781258, 120644966953596721, 3184928755000333]], ![![-627242907192459781, -51154041279840586, 146684917597316265]], ![![1801198749918060371, -36155257512437423, -217509052010875729]]]
  g := ![![![16429897994224963300090034929122289, 26126220472664448982468215506222750, 17859719013125917241591175320882203], ![127777680084142119755614128428678966, 203187374780859675912077117041183539, 138897603822860776653218117716454297], ![114816724038898991339097649410801769, 182577338413405733695423038059425357, 124808713362866328964672470522515289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-28396714811326112, 5794471464503019, -2385096732371446]] ![![7, 0, -1]]
  ![![-960530435590781258, 120644966953596721, 3184928755000333]] where
 M := ![![![-960530435590781258, 120644966953596721, 3184928755000333]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-960530435590781258, 120644966953596721, 3184928755000333]] ![![258093247914286281396687737954031257, 26126220472664448982468215506222750, 17859719013125917241591175320882203]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1560536289167826487591523183, 157969708529269421717010010, 107987093267854765493163215]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1560536289167826487591523183, 157969708529269421717010010, 107987093267854765493163215]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![1560536289167826487591523183, 157969708529269421717010010, 107987093267854765493163215], ![12136515198516122938412657250, 1228553146619236738066563913, 839831157907761764808896845], ![10905464204893375912326777825, 1103936520913624014068041025, 754644021031428472915533883]]]
  hmulB := by decide  
  f := ![![![24007283498054, -8955964273455, 6531584358155]], ![![96934745408625, -4727735885398, -8609624285555]], ![![-177645045136537, 20287433050265, 2842868436457]]]
  g := ![![![161226845156629632231267189, 157969708529269421717010010, 107987093267854765493163215], ![1253884366697867982739581410, 1228553146619236738066563913, 839831157907761764808896845], ![1126698302966808860094948899, 1103936520913624014068041025, 754644021031428472915533883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24007283498054, -8955964273455, 6531584358155]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![24007283498054, -8955964273455, 6531584358155]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 6, 1]] where
  M :=![![![24007283498054, -8955964273455, 6531584358155], ![678543217860375, -33094151197786, -60267369998885], ![-1339544449947975, 177835888445675, -6226258377421]]]
  hmulB := by decide  
  f := ![![![1560536289167826487591523183, 157969708529269421717010010, 107987093267854765493163215]], ![![12136515198516122938412657250, 1228553146619236738066563913, 839831157907761764808896845]], ![![12183584526451134290056320644, 1233317872736901980597776359, 843088294535121975323154024]]]
  g := ![![![2496528448557, -6877924346055, 6531584358155], ![105544369694180, 46930009827932, -60267369998885], ![-190474027367222, 30741919815743, -6226258377421]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[3, 1], [4, 1]], ![[0, 6], [1, 6]]]
 h' := ![![[4, 6], [3, 1], [0, 1]], ![[0, 1], [0, 6], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![591314, 602179, -180254]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110224, 240529, -180254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1560536289167826487591523183, 157969708529269421717010010, 107987093267854765493163215]] ![![24007283498054, -8955964273455, 6531584358155]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9992311, 1011500, 691455]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![9992311, 1011500, 691455]] 
 ![![11, 0, 0], ![0, 11, 0], ![9, 1, 1]] where
  M :=![![![9992311, 1011500, 691455], ![77711640, 7866581, 5377545], ![69829065, 7068645, 4832081]]]
  hmulB := by decide  
  f := ![![![776, -275, 195]], ![![20235, -944, -1845]], ![![-1236, 176, -19]]]
  g := ![![![342656, 29095, 691455], ![2664885, 226276, 5377545], ![2394576, 203324, 4832081]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[3, 3], [7, 1], [1]], ![[0, 8], [6, 10], [1]]]
 h' := ![![[10, 10], [5, 5], [7, 10], [0, 1]], ![[0, 1], [0, 6], [8, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1681, 2663, -879]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![872, 322, -879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![776, -275, 195]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![776, -275, 195]] 
 ![![11, 0, 0], ![6, 1, 0], ![9, 0, 1]] where
  M :=![![![776, -275, 195], ![20235, -944, -1845], ![-40815, 5355, -119]]]
  hmulB := by decide  
  f := ![![![9992311, 1011500, 691455]], ![![12515046, 1266871, 866025]], ![![14523624, 1470195, 1005016]]]
  g := ![![![61, -275, 195], ![3864, -944, -1845], ![-6534, 5355, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![9992311, 1011500, 691455]] ![![776, -275, 195]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![482254678, -90307867, 31493100]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![482254678, -90307867, 31493100]] 
 ![![13, 0, 0], ![3, 1, 0], ![11, 0, 1]] where
  M :=![![![482254678, -90307867, 31493100], ![3130331199, 112680344, -573340302], ![-11548356336, 1140216102, 383603945]]]
  hmulB := by decide  
  f := ![![![696956468748299884, 70551393767631515, 48228486397129434]], ![![577784624495213313, 58487886092590835, 39981948876926766]], ![![964388304499932662, 97622939260278217, 66734423612793503]]]
  g := ![![![31288783, -90307867, 31493100], ![699925653, 112680344, -573340302], ![-1476049849, 1140216102, 383603945]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-632339873697085, -47010019765968, 142802462151545]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-632339873697085, -47010019765968, 142802462151545]] 
 ![![13, 0, 0], ![11, 1, 0], ![7, 0, 1]] where
  M :=![![![-632339873697085, -47010019765968, 142802462151545], ![15281635853068956, -1583174686138291, -424862580747353], ![-13216822477362609, 2995306899475163, -1442144626840387]]]
  hmulB := by decide  
  f := ![![![3555760686405422478777867452156, 359941952731412429963239027219, 246054041515300675062864792299]], ![![5135925376331258266402742817205, 519898601755536924455598927093, 355399394733960102339083237408]], ![![3826075025650643177607045687977, 387305287809394250473666929300, 264759444245331594144422555172]]]
  g := ![![![-85757453179404, -47010019765968, 142802462151545], ![2743891958909356, -1583174686138291, -424862580747353], ![-2774629691054361, 2995306899475163, -1442144626840387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![482254678, -90307867, 31493100]] ![![-632339873697085, -47010019765968, 142802462151545]]
  ![![-2101239512299559597988382, 214633826764394249912293, 61817983890362244673861]] where
 M := ![![![-2101239512299559597988382, 214633826764394249912293, 61817983890362244673861]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-2101239512299559597988382, 214633826764394249912293, 61817983890362244673861]] ![![-632339873697085, -47010019765968, 142802462151545]]
  ![![13, 0, 0]] where
 M := ![![![3791616191191607066626187453504457279229, -55859696657698422212001523745391113144, -480402530790881075866035489359993284826]]]
 hmul := by decide  
 g := ![![![![291662783937815928202014419500342867633, -4296899742899878631692424903491624088, -36954040830067775066618114566153329602]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [11, 5, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16, 8], [9, 0, 9], [0, 1]]
 g := ![![[12, 4, 15], [3, 2], [13, 1], []], ![[4, 8, 7, 13], [6, 16], [], [0, 13]], ![[6, 12, 16, 4], [15, 4], [0, 1], [16, 13]]]
 h' := ![![[4, 16, 8], [16, 7, 7], [10, 9, 11], [0, 0, 1], [0, 1]], ![[9, 0, 9], [3, 7, 5], [1, 13, 4], [16, 2], [4, 16, 8]], ![[0, 1], [9, 3, 5], [15, 12, 2], [7, 15, 16], [9, 0, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 13], []]
 b := ![[], [15, 14, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [11, 5, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-888267, 78064, -38386]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52251, 4592, -2258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![460, 99, -176]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![460, 99, -176]] 
 ![![19, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![460, 99, -176], ![-18711, 1714, 770], ![20724, -3938, 1417]]]
  hmulB := by decide  
  f := ![![![-5460998, -552805, -377894]], ![![-2522735, -255371, -174570]], ![![-2008578, -203324, -138991]]]
  g := ![![![19, 99, -176], ![-1075, 1714, 770], ![1298, -3938, 1417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17647391575, 1786407226, 1221176677]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![17647391575, 1786407226, 1221176677]] 
 ![![19, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![17647391575, 1786407226, 1221176677], ![137246302794, 13893145965, 9497266679], ![123324909819, 12483913507, 8533924287]]]
  hmulB := by decide  
  f := ![![![418702, -21623, -35851]], ![![-119051, 26530, -12489]], ![![116865, -35851, 23175]]]
  g := ![![![167089611, 1786407226, 1221176677], ![1299479940, 13893145965, 9497266679], ![1167668951, 12483913507, 8533924287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 18, -1]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-133, 18, -1]] 
 ![![19, 0, 0], ![13, 1, 0], ![6, 0, 1]] where
  M :=![![![-133, 18, -1], ![-54, -91, 109], ![2001, -127, -145]]]
  hmulB := by decide  
  f := ![![![27038, 2737, 1871]], ![![29567, 2993, 2046]], ![![18483, 1871, 1279]]]
  g := ![![![-19, 18, -1], ![25, -91, 109], ![238, -127, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![460, 99, -176]] ![![17647391575, 1786407226, 1221176677]]
  ![![-27038, -2737, -1871]] where
 M := ![![![-27038, -2737, -1871]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-27038, -2737, -1871]] ![![-133, 18, -1]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![927220236144838581605, 93860496204384156574, 64162441344961794175]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![927220236144838581605, 93860496204384156574, 64162441344961794175]] 
 ![![23, 0, 0], ![0, 23, 0], ![10, 17, 1]] where
  M :=![![![927220236144838581605, 93860496204384156574, 64162441344961794175], ![7211125153869026240622, 729966580483836129703, 499000535881343145269], ![6479674433410666642017, 655923408327969149881, 448385091870683659981]]]
  hmulB := by decide  
  f := ![![![-20467415102, 833299047, 2001455147]], ![![218657053017, -30809547890, 2998339135]], ![![151669961042, -20973976963, 1638124858]]]
  g := ![![![12417209682400897385, -43343522028694188887, 64162441344961794175], ![96570425871982382084, -337088805630391188690, 499000535881343145269], ![86774935421905654009, -302896658846680568252, 448385091870683659981]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 12, 1] where
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
 g := ![![[4, 8], [17, 12], [0, 6], [1]], ![[0, 15], [11, 11], [20, 17], [1]]]
 h' := ![![[11, 22], [18, 13], [0, 14], [20, 11], [0, 1]], ![[0, 1], [0, 10], [16, 9], [3, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [3, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99750, 31851, -9598]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8510, 8479, -9598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20467415102, -833299047, -2001455147]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![20467415102, -833299047, -2001455147]] 
 ![![23, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![20467415102, -833299047, -2001455147], ![-218657053017, 30809547890, -2998339135], ![24086646303, -33027853511, 33309445031]]]
  hmulB := by decide  
  f := ![![![-927220236144838581605, -93860496204384156574, -64162441344961794175]], ![![-877922106952033321004, -88870153362835405293, -60751074552643837553]], ![![-805805978404068182734, -81569993868911442841, -55760731711095086272]]]
  g := ![![![2528370377, -833299047, -2001455147], ![-26565752814, 30809547890, -2998339135], ![2324078698, -33027853511, 33309445031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![927220236144838581605, 93860496204384156574, 64162441344961794175]] ![![20467415102, -833299047, -2001455147]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235916, -62381, 35664]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![235916, -62381, 35664]] 
 ![![29, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![235916, -62381, 35664], ![3664569, -102830, -409950], ![-8769996, 1051902, 84313]]]
  hmulB := by decide  
  f := ![![![422557319110, 42774562181, 29240420070]], ![![142462196287, 14421139566, 9858199764]], ![![160109587862, 16207546792, 11079376441]]]
  g := ![![![7518, -62381, 35664], ![190001, -102830, -409950], ![-386588, 1051902, 84313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68753520851138018889457, 6959769999970367097318, 4757654737144518990647]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![68753520851138018889457, 6959769999970367097318, 4757654737144518990647]] 
 ![![29, 0, 0], ![9, 1, 0], ![13, 0, 1]] where
  M :=![![![68753520851138018889457, 6959769999970367097318, 4757654737144518990647], ![534706021611519152281830, 54127132428211639140211, 37000965262677683593261], ![480468839979562064043465, 48636820005923658238385, 33247822428300537848257]]]
  hmulB := by decide  
  f := ![![![1103347438742, -156324289631, 16085367481]], ![![386150819577, -24576963865, -27905613722]], ![![-119185259411, -27194760182, 47319631060]]]
  g := ![![![-1921859335568070064304, 6959769999970367097318, 4757654737144518990647], ![-14946576505420534023878, 54127132428211639140211, 37000965262677683593261], ![-13430490746264063866529, 48636820005923658238385, 33247822428300537848257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-722725, -1926, 105563]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-722725, -1926, 105563]] 
 ![![29, 0, 0], ![17, 1, 0], ![24, 0, 1]] where
  M :=![![![-722725, -1926, 105563], ![11395026, -1359955, -117119], ![-6225099, 2017253, -1354177]]]
  hmulB := by decide  
  f := ![![![-2077878436142, -210339133537, -143786500859]], ![![-1775306651993, -179710447179, -122848924654]], ![![-2220340632429, -224760273103, -153644700623]]]
  g := ![![![-111155, -1926, 105563], ![1287073, -1359955, -117119], ![-276488, 2017253, -1354177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![235916, -62381, 35664]] ![![68753520851138018889457, 6959769999970367097318, 4757654737144518990647]]
  ![![2077878436142, 210339133537, 143786500859]] where
 M := ![![![2077878436142, 210339133537, 143786500859]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![2077878436142, 210339133537, 143786500859]] ![![-722725, -1926, 105563]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![98629, 9984, 6825]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![98629, 9984, 6825]] 
 ![![31, 0, 0], ![0, 1, 0], ![16, 0, 1]] where
  M :=![![![98629, 9984, 6825], ![767052, 77647, 53079], ![689247, 69771, 47695]]]
  hmulB := by decide  
  f := ![![![-1244, 195, -39]], ![![-117, -20, 39]], ![![109, 39, -59]]]
  g := ![![![-341, 9984, 6825], ![-2652, 77647, 53079], ![-2383, 69771, 47695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2186, -9321, 10686]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-2186, -9321, 10686]] 
 ![![31, 0, 0], ![30, 1, 0], ![11, 0, 1]] where
  M :=![![![-2186, -9321, 10686], ![1126125, -84944, -66612], ![-1615770, 258960, -56981]]]
  hmulB := by decide  
  f := ![![![22090037584, 2236126659, 1528602036]], ![![26919307335, 2724983176, 1862781258]], ![![12818121824, 1297550709, 886997455]]]
  g := ![![![5158, -9321, 10686], ![142167, -84944, -66612], ![-282509, 258960, -56981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![98629, 9984, 6825]] ![![98629, 9984, 6825]]
  ![![22090037584, 2236126659, 1528602036]] where
 M := ![![![22090037584, 2236126659, 1528602036]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![22090037584, 2236126659, 1528602036]] ![![-2186, -9321, 10686]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB158I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB158I0 : PrimesBelowBoundCertificateInterval O 1 31 158 where
  m := 11
  g := ![3, 2, 3, 2, 2, 3, 1, 3, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB158I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N0, I31N1]
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
    · exact ![3, 9]
    · exact ![5, 5, 5]
    · exact ![7, 49]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I19N0, I19N1, I19N2, I23N1, I29N0, I29N1, I29N2, I31N0, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1, I13N1], [], [I19N0, I19N1, I19N2], [I23N1], [I29N0, I29N1, I29N2], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
