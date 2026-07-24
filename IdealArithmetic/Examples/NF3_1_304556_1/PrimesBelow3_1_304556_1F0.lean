
import IdealArithmetic.Examples.NF3_1_304556_1.RI3_1_304556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578], ![1911103149348209234212617, -1096405676367167775789001, 282723710820003869113689], ![10454894089535495445350346, 2115321220720576482980868, -1007686816060626084699964]]]
  hmulB := by decide  
  f := ![![![506782080030806684307310238583055333162552393912, 124445627311532094893212376220074292605591964372, 43247220669474555442050432742897637728070416071]], ![![2694210990492269938913035108260934887927945063047, 661591619026965833136664769344745914708635507710, 229915661636772697781868997073009076636458362629]], ![![7752701136193230883409739779704936485597036777951, 1903756652551222423428758097361444733134214452467, 661591619026965833136664769344745914708635507710]]]
  g := ![![![-725099307539885100211643, 88718860306541691089037, 16567129900378795846578], ![1503754412857688505000809, -1096405676367167775789001, 282723710820003869113689], ![4169786434407459481184739, 2115321220720576482980868, -1007686816060626084699964]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]] ![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]]
  ![![2196385604471823149655349727399191514670015389818, -183015992770123177840237141744438526751231540546, -14167364929052437944872326790125262419256445621]] where
 M := ![![![2196385604471823149655349727399191514670015389818, -183015992770123177840237141744438526751231540546, -14167364929052437944872326790125262419256445621]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2196385604471823149655349727399191514670015389818, -183015992770123177840237141744438526751231540546, -14167364929052437944872326790125262419256445621]] ![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]]
  ![![2, 0, 0]] where
 M := ![![![-3488215274188861342805741437279781570814197480429516211494865608656080430, 365552073285453313368652151038594130988100233383989569195797887748180784, -1078888137443698466670603877020091000706228263989998736480140229133746]]]
 hmul := by decide  
 g := ![![![![-1744107637094430671402870718639890785407098740214758105747432804328040215, 182776036642726656684326075519297065494050116691994784597898943874090392, -539444068721849233335301938510045500353114131994999368240070114566873]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-350027394701416827526723146223541, -85952878813692739941281436765110, -29870258984084912144723231391429]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-350027394701416827526723146223541, -85952878813692739941281436765110, -29870258984084912144723231391429]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-350027394701416827526723146223541, -85952878813692739941281436765110, -29870258984084912144723231391429], ![-3371681367063033075860836889822300, -827951538446775421842294848486405, -287728895425163131968567541686759], ![-10709367546837767703619333762602118, -2629796938350650149138878706681778, -913904417260468161783576285251515]]]
  hmulB := by decide  
  f := ![![![-69703032513976073, 2357721866960888, 1535896859844255]], ![![33867781311950955, -14256986963169035, 3381653106857058]], ![![61483669483734748, 35648887239584898, -13233055723272865]]]
  g := ![![![-68111332639851421098665082225191, -85952878813692739941281436765110, -29870258984084912144723231391429], ![-656090679255310463360468985987459, -827951538446775421842294848486405, -287728895425163131968567541686759], ![-2083920591322060410304434161805770, -2629796938350650149138878706681778, -913904417260468161783576285251515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3646275, 370462, -235810]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3646275, 370462, -235810]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3646275, 370462, -235810], ![-25568638, -126685, 875576], ![30846800, -3976628, 243777]]]
  hmulB := by decide  
  f := ![![![-3450957148483, -847418533706, -294494046262]], ![![-13381225973164, -3285899652029, -1141912579968]], ![![-37495567649210, -9207427849904, -3199756171635]]]
  g := ![![![1125657, 370462, -235810], ![-9022140, -126685, 875576], ![12770834, -3976628, 243777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-230049617, -1992895546, 634951823]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-230049617, -1992895546, 634951823]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-230049617, -1992895546, 634951823], ![67851804984, 9929179551, -5343734815], ![-192550533494, -5218352170, 7936284005]]]
  hmulB := by decide  
  f := ![![![-50915298685614583205, -12502782821958035820, -4344954655016862517]], ![![-197426130748347359700, -48480046269933485039, -16847737476974898337]], ![![-519264735308697388638, -127510873554012266278, -44312451995947473099]]]
  g := ![![![1251913825, -1992895546, 634951823], ![15997815294, 9929179551, -5343734815], ![-60704609718, -5218352170, 7936284005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-350027394701416827526723146223541, -85952878813692739941281436765110, -29870258984084912144723231391429]] ![![3646275, 370462, -235810]]
  ![![50915298685614583205, 12502782821958035820, 4344954655016862517]] where
 M := ![![![50915298685614583205, 12502782821958035820, 4344954655016862517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![50915298685614583205, 12502782821958035820, 4344954655016862517]] ![![-230049617, -1992895546, 634951823]]
  ![![3, 0, 0]] where
 M := ![![![-3, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 2], [1, 0, 3], [0, 1]]
 g := ![![[2, 0, 1], []], ![[0, 3], [1, 4]], ![[2, 3, 2, 3], [0, 4]]]
 h' := ![![[4, 4, 2], [0, 0, 1], [0, 1]], ![[1, 0, 3], [3, 2], [4, 4, 2]], ![[0, 1], [1, 3, 4], [1, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-196120, -46945, -13935]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39224, -9389, -2787]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1213373724924968634148, -297956578007728793035, -103545573736905893144]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1213373724924968634148, -297956578007728793035, -103545573736905893144]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![-1213373724924968634148, -297956578007728793035, -103545573736905893144], ![-11687969689067377038875, -2870102904715462924452, -997415307760092272249], ![-37124137677800214745898, -9116219345073708200608, -3168059482723191717487]]]
  hmulB := by decide  
  f := ![![![-193764964732, 7849471493, 3861771373]], ![![61806331789, -18853803252, 3915740836]], ![![8115919748, 46719042717, -14974042058]]]
  g := ![![![-99377979462919881204, -297956578007728793035, -103545573736905893144], ![-957270450038130811090, -2870102904715462924452, -997415307760092272249], ![-3040548609169179451209, -9116219345073708200608, -3168059482723191717487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58702636172505904862467329718, -14415044791804897640046894325, -5009502033453739970579811950]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-58702636172505904862467329718, -14415044791804897640046894325, -5009502033453739970579811950]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![-58702636172505904862467329718, -14415044791804897640046894325, -5009502033453739970579811950], ![-565460268471716294403826208825, -138854668707765744391744320918, -48254636408868432890720494925], ![-1796054012503595819169510477650, -441039802073935441005102411100, -153269713499570642031791215243]]]
  hmulB := by decide  
  f := ![![![1090775808314426, 148170157550975, -82300282430525]], ![![-337172294274317, 94713176390268, -18798786337250]], ![![1834586495503600, -155127048752350, -11122650431857]]]
  g := ![![![3969661796903354425402005176, -14415044791804897640046894325, -5009502033453739970579811950], ![38238249110696881706662816669, -138854668707765744391744320918, -48254636408868432890720494925], ![121454971420002403837300569850, -441039802073935441005102411100, -153269713499570642031791215243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1213373724924968634148, -297956578007728793035, -103545573736905893144]] ![![-1213373724924968634148, -297956578007728793035, -103545573736905893144]]
  ![![8798823384086575469966641815590357396244841, 2160642885339334304822318699249577238182552, 750864467228583452025850964011834170676155]] where
 M := ![![![8798823384086575469966641815590357396244841, 2160642885339334304822318699249577238182552, 750864467228583452025850964011834170676155]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![8798823384086575469966641815590357396244841, 2160642885339334304822318699249577238182552, 750864467228583452025850964011834170676155]] ![![-58702636172505904862467329718, -14415044791804897640046894325, -5009502033453739970579811950]]
  ![![7, 0, 0]] where
 M := ![![![-3086864973089927160792651980706123662750343708336243332331236922742341988, -758011901247218116484010201210091107472601179436140439451954980886970561, -263423542245172736515724301232968264068540430642778974841247781329829215]]]
 hmul := by decide  
 g := ![![![![-440980710441418165827521711529446237535763386905177618904462417534620284, -108287414463888302354858600172870158210371597062305777064564997269567223, -37631934606453248073674900176138323438362918663254139263035397332832745]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 6, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 1], [0, 2, 10], [0, 1]]
 g := ![![[7, 4, 5], [3, 8, 1], []], ![[4, 7, 1, 4], [7, 9, 3, 4], [2, 1]], ![[0, 10, 8, 7], [9, 8, 10, 2], [4, 1]]]
 h' := ![![[8, 8, 1], [5, 10, 7], [0, 0, 1], [0, 1]], ![[0, 2, 10], [10, 9, 2], [5, 4, 2], [8, 8, 1]], ![[0, 1], [4, 3, 2], [3, 7, 8], [0, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 9], []]
 b := ![[], [9, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 6, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1284184, 398002, 86086]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![116744, 36182, 7826]
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

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![261966, -1325, -8145]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![261966, -1325, -8145]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 11, 1]] where
  M :=![![![261966, -1325, -8145], ![-897275, 131646, -12120], ![-487840, -363290, 130321]]]
  hmulB := by decide  
  f := ![![![-981012582, -240897875, -83716590]], ![![-9449722775, -2320478022, -806410215]], ![![-10832992433, -2660154319, -924454184]]]
  g := ![![![24537, 6790, -8145], ![-62495, 20382, -12120], ![-107699, -138217, 130321]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[5, 1], [4], [8, 1]], ![[0, 12], [4], [3, 12]]]
 h' := ![![[8, 12], [8, 12], [5, 11], [0, 1]], ![[0, 1], [0, 1], [2, 2], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![695844, 716445, 290692]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103000, -190859, 290692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![981012582, 240897875, 83716590]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![981012582, 240897875, 83716590]] 
 ![![13, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![981012582, 240897875, 83716590], ![9449722775, 2320478022, 806410215], ![30014863030, 7370462780, 2561375897]]]
  hmulB := by decide  
  f := ![![![-261966, 1325, 8145]], ![![-31735, -9617, 4065]], ![![-63230, 28455, -6892]]]
  g := ![![![-49389211, 240897875, 83716590], ![-475747570, 2320478022, 806410215], ![-1511102335, 7370462780, 2561375897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![261966, -1325, -8145]] ![![981012582, 240897875, 83716590]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [12, 9, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 14, 15], [6, 2, 2], [0, 1]]
 g := ![![[4, 13, 9], [12, 16], [9, 1], []], ![[10, 1, 12, 13], [4, 15], [16, 4], [14, 4]], ![[15, 4, 9, 9], [15, 2], [0, 9], [10, 4]]]
 h' := ![![[3, 14, 15], [11, 0, 14], [11, 9, 4], [0, 0, 1], [0, 1]], ![[6, 2, 2], [12, 15, 11], [14, 4, 7], [11, 12, 2], [3, 14, 15]], ![[0, 1], [8, 2, 9], [1, 4, 6], [1, 5, 14], [6, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 8], []]
 b := ![[], [4, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [12, 9, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1551522, -416126, -95149]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91266, -24478, -5597]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6718582184154368691, 1649817954297729782, 573343095096143727]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![6718582184154368691, 1649817954297729782, 573343095096143727]] 
 ![![19, 0, 0], ![0, 19, 0], ![8, 16, 1]] where
  M :=![![![6718582184154368691, 1649817954297729782, 573343095096143727], ![64717558414873539752, 15892071705692668323, 5522796957989333073], ![205560384966788312554, 50477497262801713046, 17541889659990398105]]]
  hmulB := by decide  
  f := ![![![-5419507497, 228005228, 105348435]], ![![11816333078, -3733932537, 789364119]], ![![9221604138, -2623482150, 524562425]]]
  g := ![![![112201969651853625, -395982714065293150, 573343095096143727], ![1080799092155730272, -3814351559059824255, 5522796957989333073], ![3432908825624480406, -12115407226160245086, 17541889659990398105]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18], [0, 1]]
 g := ![![[13, 1], [], [17], [1]], ![[7, 18], [], [17], [1]]]
 h' := ![![[13, 18], [0, 1], [18], [1, 13], [0, 1]], ![[0, 1], [13, 18], [18], [18, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [16, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [18, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1052, 470, 141]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -94, 141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5419507497, -228005228, -105348435]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![5419507497, -228005228, -105348435]] 
 ![![19, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![5419507497, -228005228, -105348435], ![-11816333078, 3733932537, -789364119], ![-29505209350, -8072717918, 3505927309]]]
  hmulB := by decide  
  f := ![![![-6718582184154368691, -1649817954297729782, -573343095096143727]], ![![-6235063994110973120, -1531085017898658241, -532081143092551731]], ![![-16830330636705925279, -4132863288729637860, -1436248540874991656]]]
  g := ![![![475498564, -228005228, -105348435], ![-1487821229, 3733932537, -789364119], ![-1290748961, -8072717918, 3505927309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![6718582184154368691, 1649817954297729782, 573343095096143727]] ![![5419507497, -228005228, -105348435]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-178464323687594437856404376672853966598195632333913, -43823776706313177665445416214515422025144212645000, -15229595307862421561933118081995116067306816316536]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-178464323687594437856404376672853966598195632333913, -43823776706313177665445416214515422025144212645000, -15229595307862421561933118081995116067306816316536]] 
 ![![23, 0, 0], ![0, 23, 0], ![5, 19, 1]] where
  M :=![![![-178464323687594437856404376672853966598195632333913, -43823776706313177665445416214515422025144212645000, -15229595307862421561933118081995116067306816316536], ![-1719079260571179549478088405233978189428894007463960, -422137848613393182847334265984775823675104693398489, -146700925426801954558269366725541382142739454251536], ![-5460258440624671248800186743040491297592749676244512, -1340823430231232548248317618876041627229193687614512, -465961625319706360512779682199291245700248906043489]]]
  hmulB := by decide  
  f := ![![![4040678273021584783087057, -3605347404320790557424584, 1003022310068805597191048]], ![![106727106703247825133590696, 20089035234122474338143825, -9813019902893566075082704]], ![![73632919185844325009520795, 15135056999151315034819149, -7171677338036175811299865]]]
  g := ![![![-4448536832534014349858208098386016793985284815271, 10675588441003166609186253362756164489290665103008, -15229595307862421561933118081995116067306816316536], ![-42851071019007381595075720504620490378921597226360, 102833901499819302337381900078283062479867171190465, -146700925426801954558269366725541382142739454251536], ![-136106535392440845488534275306262394308326310696829, 326628150036660360934543319256977914829371109878773, -465961625319706360512779682199291245700248906043489]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [19, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22], [0, 1]]
 g := ![![[2, 9], [22, 16], [1, 18], [1]], ![[5, 14], [12, 7], [7, 5], [1]]]
 h' := ![![[8, 22], [19, 3], [4, 4], [4, 8], [0, 1]], ![[0, 1], [20, 20], [13, 19], [22, 15], [8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [7, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [19, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22364, 4451, 1768]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![588, -1267, 1768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9509563668651401713484, -2335172577791896859241, -811516852418272246815]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-9509563668651401713484, -2335172577791896859241, -811516852418272246815]] 
 ![![23, 0, 0], ![11, 1, 0], ![6, 0, 1]] where
  M :=![![![-9509563668651401713484, -2335172577791896859241, -811516852418272246815], ![-91602026343801844008891, -22493833307343757662524, -7817034585793962824538], ![-290952691358676088882740, -71446469046237784114086, -24829005885135654521765]]]
  hmulB := by decide  
  f := ![![![239109407408, -122134255725, 30637005402]], ![![255571296521, -26703274745, 53969463]], ![![-465798150366, -60878234742, 34390837849]]]
  g := ![![![915062426155178139959, -2335172577791896859241, -811516852418272246815], ![8814449893554055096787, -22493833307343757662524, -7817034585793962824538], ![27997065367858846239252, -71446469046237784114086, -24829005885135654521765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-178464323687594437856404376672853966598195632333913, -43823776706313177665445416214515422025144212645000, -15229595307862421561933118081995116067306816316536]] ![![-9509563668651401713484, -2335172577791896859241, -811516852418272246815]]
  ![![23, 0, 0]] where
 M := ![![![10142556340152617814032999365177263463322557898819085234802635603296266532, 2490610532669430954161747803976013638838546732433032872484994937200046129, 865534495948424705694522704051181439082347129254845203049814138655153135]]]
 hmul := by decide  
 g := ![![![![440980710441418165827521711529446237535763386905177618904462417534620284, 108287414463888302354858600172870158210371597062305777064564997269567223, 37631934606453248073674900176138323438362918663254139263035397332832745]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116490596174981143246899, 28605481306696261861142, 9940948421838061885551]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![116490596174981143246899, 28605481306696261861142, 9940948421838061885551]] 
 ![![29, 0, 0], ![0, 29, 0], ![28, 23, 1]] where
  M :=![![![116490596174981143246899, 28605481306696261861142, 9940948421838061885551], ![1122109807708883069271752, 275545770924390133415715, 95757392341926847468977], ![3564122777453787403918762, 875207534624338788971414, 304151252231086395276857]]]
  hmulB := by decide  
  f := ![![![16461889113, 95430980980, -30583035939]], ![![-3268702972310, -472866685911, 255709907001]], ![![-2258838450676, -274533038699, 160260936200]]]
  g := ![![![-5581239987464985846501, -6897804565364798672639, 9940948421838061885551], ![-53761971650519608960676, -66443939756549219254164, 95757392341926847468977], ![-170762492586780402201146, -211043836782436148358493, 304151252231086395276857]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [13, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 28], [0, 1]]
 g := ![![[5, 9], [16], [3, 20], [22, 1]], ![[0, 20], [16], [8, 9], [15, 28]]]
 h' := ![![[22, 28], [8, 26], [19, 25], [4, 7], [0, 1]], ![[0, 1], [0, 3], [18, 4], [13, 22], [22, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [12, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [13, 7, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2238, 579, 382]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-446, -283, 382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16461889113, -95430980980, 30583035939]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-16461889113, -95430980980, 30583035939]] 
 ![![29, 0, 0], ![17, 1, 0], ![20, 0, 1]] where
  M :=![![![-16461889113, -95430980980, 30583035939], ![3268702972310, 472866685911, -255709907001], ![-9212920398362, -242408186242, 377435704931]]]
  hmulB := by decide  
  f := ![![![-116490596174981143246899, -28605481306696261861142, -9940948421838061885551]], ![![-106981032506329741533415, -26270308728904365001901, -9129431569419789638736]], ![![-203239127619083112719198, -49907488302009104351526, -17343800712684401137513]]]
  g := ![![![34282898923, -95430980980, 30583035939], ![11867843167, 472866685911, -255709907001], ![-435886045892, -242408186242, 377435704931]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![116490596174981143246899, 28605481306696261861142, 9940948421838061885551]] ![![-16461889113, -95430980980, 30583035939]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [4, 15, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 5], [20, 25], [0, 1]]
 g := ![![[25, 8, 20], [7, 24, 10], [28, 9, 14], [1]], ![[19, 4, 4], [19, 9, 2], [0, 26, 9], [1]], ![[1, 19, 7], [23, 29, 19], [11, 27, 8], [1]]]
 h' := ![![[24, 5], [3, 5, 12], [12, 25, 14], [27, 16, 13], [0, 1]], ![[20, 25], [29, 22, 21], [27, 13, 9], [25, 7, 15], [24, 5]], ![[0, 1], [5, 4, 29], [5, 24, 8], [29, 8, 3], [20, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [23, 18, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [4, 15, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1408392, 365800, 104439]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45432, 11800, 3369]
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



lemma PB157I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB157I0 : PrimesBelowBoundCertificateInterval O 1 31 157 where
  m := 11
  g := ![3, 3, 1, 3, 1, 2, 1, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB157I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![29791]
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
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
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
  β := ![I2N0, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I13N1, I19N1, I23N1, I29N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1, I3N2], [I5N0], [I7N0, I7N0, I7N1], [], [I13N1], [], [I19N1], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
