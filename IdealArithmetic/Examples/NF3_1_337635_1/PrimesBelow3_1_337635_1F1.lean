
import IdealArithmetic.Examples.NF3_1_337635_1.RI3_1_337635_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [3, 2, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 10, 3], [26, 26, 34], [0, 1]]
 g := ![![[27, 12, 26], [7, 7], [20, 19, 10], [19, 1], []], ![[13, 3, 33, 3], [24, 7], [13, 21, 8, 12], [5, 10], [9, 9]], ![[27, 25, 31, 16], [], [0, 7, 24, 11], [13, 26], [15, 9]]]
 h' := ![![[30, 10, 3], [27, 13, 27], [14, 7, 28], [17, 33, 26], [0, 0, 1], [0, 1]], ![[26, 26, 34], [12, 19, 1], [26, 33, 9], [25, 34, 35], [22, 0, 26], [30, 10, 3]], ![[0, 1], [12, 5, 9], [30, 34], [2, 7, 13], [2, 0, 10], [26, 26, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 32], []]
 b := ![[], [26, 17, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [3, 2, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1166869, -488659, -86802]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31537, -13207, -2346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1123729, -115136, 35112]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1123729, -115136, 35112]] 
 ![![41, 0, 0], ![22, 1, 0], ![34, 0, 1]] where
  M :=![![![-1123729, -115136, 35112], ![9410016, 797631, -265384], ![-40266464, -2991128, 1063015]]]
  hmulB := by decide  
  f := ![![![-54096204313, -17366808704, -2548832552]], ![![-45687893142, -14667441281, -2152661000]], ![![-141719233058, -45496922408, -6677337145]]]
  g := ![![![5255, -115136, 35112], ![21590, 797631, -265384], ![-258638, -2991128, 1063015]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79717, -25592, -3756]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-79717, -25592, -3756]] 
 ![![41, 0, 0], ![30, 1, 0], ![27, 0, 1]] where
  M :=![![![-79717, -25592, -3756], ![-1006608, -323157, -47428], ![-5852048, -1878716, -275729]]]
  hmulB := by decide  
  f := ![![![-14005, -728, 316]], ![![-8182, -445, 188]], ![![-16047, -700, 339]]]
  g := ![![![19255, -25592, -3756], ![243138, -323157, -47428], ![1413515, -1878716, -275729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1123729, -115136, 35112]] ![![-79717, -25592, -3756]]
  ![![14005, 728, -316]] where
 M := ![![![14005, 728, -316]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![14005, 728, -316]] ![![-79717, -25592, -3756]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![679, 218, 32]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![679, 218, 32]] 
 ![![43, 0, 0], ![12, 1, 0], ![8, 0, 1]] where
  M :=![![![679, 218, 32], ![8576, 2753, 404], ![49848, 16004, 2349]]]
  hmulB := by decide  
  f := ![![![1181, 46, -24]], ![![180, 9, -4]], ![![656, 12, -11]]]
  g := ![![![-51, 218, 32], ![-644, 2753, 404], ![-3744, 16004, 2349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7999931419563, -611563433205, 214170341455]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-7999931419563, -611563433205, 214170341455]] 
 ![![43, 0, 0], ![34, 1, 0], ![7, 0, 1]] where
  M :=![![![-7999931419563, -611563433205, 214170341455], ![57397651509940, 3810384951622, -1437297207865], ![-221296651608880, -12982793273115, 5247682159487]]]
  hmulB := by decide  
  f := ![![![1335556609667811112288439, 428761249481781460083510, 62926968814002532067315]], ![![1448217496996703637484822, 464929407738193234305013, 68235173716875499497405]], ![![2497499615968358848706031, 801786347483396762151075, 117673844230469692294133]]]
  g := ![![![262651928354, -611563433205, 214170341455], ![-1444054799771, 3810384951622, -1437297207865], ![4264756850247, -12982793273115, 5247682159487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231030268699393914873, 74168946459185987248, 10885374987701484863]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![231030268699393914873, 74168946459185987248, 10885374987701484863]] 
 ![![43, 0, 0], ![40, 1, 0], ![40, 0, 1]] where
  M :=![![![231030268699393914873, 74168946459185987248, 10885374987701484863], ![2917280496703997943284, 936550964445266024175, 137452517930670489633], ![16959997154357846639180, 5444763268341443170999, 799098446514595534542]]]
  hmulB := by decide  
  f := ![![![-758256200517, -37036432279, 16699636959]], ![![-601273146876, -30422580938, 13423557601]], ![![-1040267780848, -43630429829, 21675448621]]]
  g := ![![![-73747502073862906269, 74168946459185987248, 10885374987701484863], ![-931229274379847967652, 936550964445266024175, 137452517930670489633], ![-5413824917206597711220, 5444763268341443170999, 799098446514595534542]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![679, 218, 32]] ![![-7999931419563, -611563433205, 214170341455]]
  ![![-758256200517, -37036432279, 16699636959]] where
 M := ![![![-758256200517, -37036432279, 16699636959]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-758256200517, -37036432279, 16699636959]] ![![231030268699393914873, 74168946459185987248, 10885374987701484863]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7040265995679, 228665113202, -135235566306]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![7040265995679, 228665113202, -135235566306]] 
 ![![47, 0, 0], ![0, 47, 0], ![20, 26, 1]] where
  M :=![![![7040265995679, 228665113202, -135235566306], ![-36243131770008, -574731736867, 592565792710], ![97525382108144, -937157896414, -1167297529577]]]
  hmulB := by decide  
  f := ![![![26089588263773308301217, 8375687246400566485154, 1229254301285644535194]], ![![329440152744552735431992, 105762024984741257827623, 15522120191515488435114]], ![![234095314168609284464796, 75152935243776799267140, 11029789697837050200199]]]
  g := ![![![207339943017, 79676379514, -135235566306], ![-1023286119664, -340030688241, 592565792710], ![2571730482972, 625799529204, -1167297529577]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [23, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[30, 21], [38, 42], [12, 9], [6, 37], [1]], ![[16, 26], [10, 5], [6, 38], [44, 10], [1]]]
 h' := ![![[15, 46], [19, 16], [6, 29], [3, 3], [24, 15], [0, 1]], ![[0, 1], [24, 31], [18, 18], [1, 44], [14, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [4, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [23, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2152, 2175, 1058]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-496, -539, 1058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26089588263773308301217, -8375687246400566485154, -1229254301285644535194]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-26089588263773308301217, -8375687246400566485154, -1229254301285644535194]] 
 ![![47, 0, 0], ![43, 1, 0], ![41, 0, 1]] where
  M :=![![![-26089588263773308301217, -8375687246400566485154, -1229254301285644535194], ![-329440152744552735431992, -105762024984741257827623, -15522120191515488435114], ![-1915244029290799082589280, -614861561926225532334302, -90239904793225769392509]]]
  hmulB := by decide  
  f := ![![![-7040265995679, -228665113202, 135235566306]], ![![-5669963958387, -196975917677, 111118373584]], ![![-8216516764489, -179534292444, 142807569109]]]
  g := ![![![8180093397535371840497, -8375687246400566485154, -1229254301285644535194], ![103292209562796944191393, -105762024984741257827623, -15522120191515488435114], ![600502962341684156444225, -614861561926225532334302, -90239904793225769392509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![7040265995679, 228665113202, -135235566306]] ![![-26089588263773308301217, -8375687246400566485154, -1229254301285644535194]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3069489318900241210558308277, -985415418647056694560432816, -144624089497330904613525896]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3069489318900241210558308277, -985415418647056694560432816, -144624089497330904613525896]] 
 ![![53, 0, 0], ![3, 1, 0], ![47, 0, 1]] where
  M :=![![![-3069489318900241210558308277, -985415418647056694560432816, -144624089497330904613525896], ![-38759255985284682436424940128, -12443101928392490372703243061, -1826206747796782484507339736], ![-225332076212126511705771054560, -72339623678749033268925322408, -10616895180595707888195903325]]]
  hmulB := by decide  
  f := ![![![-3128175743473537, -163409363564368, 70720190631080]], ![![180537431296393, 6036940733427, -3497704638992]], ![![-3957943027691251, -183629493547080, 85501392961987]]]
  g := ![![![126114889498405309244503911, -985415418647056694560432816, -144624089497330904613525896], ![1592486168798897461387353899, -12443101928392490372703243061, -1826206747796782484507339736], ![9258129590794695449928535263, -72339623678749033268925322408, -10616895180595707888195903325]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4248002356988664072777032851, -1363760087142272622293944549, -200151689494107690720591851]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-4248002356988664072777032851, -1363760087142272622293944549, -200151689494107690720591851]] 
 ![![53, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![-4248002356988664072777032851, -1363760087142272622293944549, -200151689494107690720591851], ![-53640652784420861113118616068, -17220560434789182756865304758, -2527368484790437553867297247], ![-311847050569708201661658523064, -100114012451133119618710928197, -14693191949998745202998007511]]]
  hmulB := by decide  
  f := ![![![1527575284736321, -30305684815108, -15595872029545]], ![![180537431296393, 6036940733427, -3497704638992]], ![![156195706629428, -68636636998101, 9678444218338]]]
  g := ![![![181642489495182095351569866, -1363760087142272622293944549, -200151689494107690720591851], ![2293647905792552530747311410, -17220560434789182756865304758, -2527368484790437553867297247], ![13334426360197732764730639449, -100114012451133119618710928197, -14693191949998745202998007511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141573167, -45450030, -6670455]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-141573167, -45450030, -6670455]] 
 ![![53, 0, 0], ![41, 1, 0], ![40, 0, 1]] where
  M :=![![![-141573167, -45450030, -6670455], ![-1787681940, -573909587, -84229605], ![-10392926100, -3336499515, -489679982]]]
  hmulB := by decide  
  f := ![![![-645859, -29865, 13935]], ![![-429163, -20603, 9390]], ![![-708920, -27615, 14407]]]
  g := ![![![37522571, -45450030, -6670455], ![473807459, -573909587, -84229605], ![2754542515, -3336499515, -489679982]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3069489318900241210558308277, -985415418647056694560432816, -144624089497330904613525896]] ![![-4248002356988664072777032851, -1363760087142272622293944549, -200151689494107690720591851]]
  ![![110998119932573399451283050425991800962324961328103560559, 35634350687879967993178774698751270280102385063965960113, 5229860854155228062385480238138548284053639127598313135]] where
 M := ![![![110998119932573399451283050425991800962324961328103560559, 35634350687879967993178774698751270280102385063965960113, 5229860854155228062385480238138548284053639127598313135]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![110998119932573399451283050425991800962324961328103560559, 35634350687879967993178774698751270280102385063965960113, 5229860854155228062385480238138548284053639127598313135]] ![![-141573167, -45450030, -6670455]]
  ![![53, 0, 0]] where
 M := ![![![-133770797908768001470476428210499278687519047477347577737798703073, -42945191570579821483664792142470581928219681675103614310769299626, -6302833415891678589509716007462162664870925498448445268989493280]]]
 hmul := by decide  
 g := ![![![![-2523977319033358518310876003971684503538095235421652410147145341, -810286633407166443088014946084350602419239276888747439825835842, -118921385205503369613390868065323823865489160348083872999801760]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [42, 25, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 32, 56], [10, 26, 3], [0, 1]]
 g := ![![[9, 9, 48], [9, 24, 22], [53, 53], [29, 21, 19], [1]], ![[19, 7, 48, 34], [43, 34, 19, 31], [46, 15], [27, 16, 3, 10], [3, 32, 3, 32]], ![[25, 26, 5, 53], [42, 29, 40, 7], [49, 26], [41, 28, 50, 15], [29, 22, 29, 27]]]
 h' := ![![[35, 32, 56], [35, 54, 44], [44, 34, 50], [21, 39, 17], [17, 34, 45], [0, 1]], ![[10, 26, 3], [35, 42, 38], [41, 41, 18], [47, 20, 30], [33, 10, 6], [35, 32, 56]], ![[0, 1], [39, 22, 36], [27, 43, 50], [43, 0, 12], [18, 15, 8], [10, 26, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 9], []]
 b := ![[], [11, 25, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [42, 25, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170982, -30975, -24131]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2898, -525, -409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀


def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4259407089976141, 1367421412712690, 200689042438820]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![4259407089976141, 1367421412712690, 200689042438820]] 
 ![![61, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![4259407089976141, 1367421412712690, 200689042438820], ![53784663373603760, 17266792964140391, 2534153782986560], ![312684275233397160, 100382791393412120, 14732639181153831]]]
  hmulB := by decide  
  f := ![![![3950380721, 250683010, -96932220]], ![![221737250, 17800411, -6082360]], ![![1915789606, 96161140, -42637649]]]
  g := ![![![-174081004783339, 1367421412712690, 200689042438820], ![-2198167032224910, 17266792964140391, 2534153782986560], ![-12779335635863066, 100382791393412120, 14732639181153831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1033031233934581, -3463593385100120, 609842962842640]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1033031233934581, -3463593385100120, 609842962842640]] 
 ![![61, 0, 0], ![41, 1, 0], ![54, 0, 1]] where
  M :=![![![-1033031233934581, -3463593385100120, 609842962842640], ![163437914041827520, 30874267225838419, -7537029733042880], ![-1091680941248659680, -136854905237329760, 38411296958881299]]]
  hmulB := by decide  
  f := ![![![-154441156913015662583762794717481, -49581113170415712109797641689480, -7276751726069525594683489759440]], ![![-135774703213447131562449997359781, -43588516560368984519457477897101, -6397250743993646688638276618960]], ![![-322580185907993832222521043147454, -103559731251210818749821349081360, -15198901455548464633986876981061]]]
  g := ![![![1771193074781439, -3463593385100120, 609842962842640], ![-11400121912020199, 30874267225838419, -7537029733042880], ![40084592421348694, -136854905237329760, 38411296958881299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![4259407089976141, 1367421412712690, 200689042438820]] ![![4259407089976141, 1367421412712690, 200689042438820]]
  ![![154441156913015662583762794717481, 49581113170415712109797641689480, 7276751726069525594683489759440]] where
 M := ![![![154441156913015662583762794717481, 49581113170415712109797641689480, 7276751726069525594683489759440]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![154441156913015662583762794717481, 49581113170415712109797641689480, 7276751726069525594683489759440]] ![![-1033031233934581, -3463593385100120, 609842962842640]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1084886255835365673, 348287136037820310, 51116218581458908]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1084886255835365673, 348287136037820310, 51116218581458908]] 
 ![![67, 0, 0], ![0, 67, 0], ![42, 34, 1]] where
  M :=![![![1084886255835365673, 348287136037820310, 51116218581458908], ![13699146579830987344, 4397914069597802647, 645458053494181712], ![79641805878304855736, 25567856841246763320, 3752456016103620935]]]
  hmulB := by decide  
  f := ![![![959570315, 338768130, -71342668]], ![![-19119835024, -2839536299, 748878928]], ![![-7460637966, -1047140318, 281747407]]]
  g := ![![![-15850670516207589, -20741258145250486, 51116218581458908], ![-200150621894397680, -261905369391110083, 645458053494181712], ![-1163602191015630202, -1522621607556363410, 3752456016103620935]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 66], [0, 1]]
 g := ![![[17, 36], [35, 15], [25], [54], [65], [1]], ![[0, 31], [0, 52], [25], [54], [65], [1]]]
 h' := ![![[20, 66], [53, 61], [29, 22], [46, 5], [9, 11], [13, 20], [0, 1]], ![[0, 1], [0, 6], [0, 45], [12, 62], [28, 56], [11, 47], [20, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [54, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [54, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238, 3691, 1218]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-782, -563, 1218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![959570315, 338768130, -71342668]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![959570315, 338768130, -71342668]] 
 ![![67, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![959570315, 338768130, -71342668], ![-19119835024, -2839536299, 748878928], ![109909693864, 12157571400, -3588415227]]]
  hmulB := by decide  
  f := ![![![1084886255835365673, 348287136037820310, 51116218581458908]], ![![204464874325835632, 65640508501459741, 9633702290957936]], ![![1188683669825445608, 381609803600697960, 56006806210501805]]]
  g := ![![![14321945, 338768130, -71342668], ![-285370672, -2839536299, 748878928], ![1640443192, 12157571400, -3588415227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1084886255835365673, 348287136037820310, 51116218581458908]] ![![959570315, 338768130, -71342668]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4264387, -666418, 172720]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-4264387, -666418, 172720]] 
 ![![71, 0, 0], ![0, 71, 0], ![58, 53, 1]] where
  M :=![![![-4264387, -666418, 172720], ![46288960, 5086955, -1505556], ![-224888984, -20516644, 6592511]]]
  hmulB := by decide  
  f := ![![![37279581971, 11968073858, 1756489448]], ![![470739172064, 151124043813, 22179658268]], ![![420395725290, 134962003967, 19807643123]]]
  g := ![![![-201157, -138318, 172720], ![1881848, 1195513, -1505556], ![-8552882, -5210137, 6592511]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [12, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 70], [0, 1]]
 g := ![![[49, 6], [8, 43], [3, 25], [36], [45], [1]], ![[0, 65], [0, 28], [0, 46], [36], [45], [1]]]
 h' := ![![[51, 70], [46, 52], [35, 55], [42, 66], [30, 6], [59, 51], [0, 1]], ![[0, 1], [0, 19], [0, 16], [0, 5], [52, 65], [33, 20], [51, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [54, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [12, 20, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![816, 1605, 467]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-370, -326, 467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37279581971, -11968073858, -1756489448]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-37279581971, -11968073858, -1756489448]] 
 ![![71, 0, 0], ![37, 1, 0], ![7, 0, 1]] where
  M :=![![![-37279581971, -11968073858, -1756489448], ![-470739172064, -151124043813, -22179658268], ![-2736704621880, -878579675804, -128944385545]]]
  hmulB := by decide  
  f := ![![![4264387, 666418, -172720]], ![![1570329, 275641, -68804]], ![![3587883, 354670, -109881]]]
  g := ![![![5884994041, -11968073858, -1756489448], ![74311381083, -151124043813, -22179658268], ![432019071573, -878579675804, -128944385545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-4264387, -666418, 172720]] ![![-37279581971, -11968073858, -1756489448]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14682261281, 535878792, -292179030]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![14682261281, 535878792, -292179030]] 
 ![![73, 0, 0], ![0, 73, 0], ![69, 40, 1]] where
  M :=![![![14682261281, 535878792, -292179030], ![-78303980040, -1728243667, 1363936614], ![221919496296, 402171786, -3092180281]]]
  hmulB := by decide  
  f := ![![![-65691837860511751, -21089420154817164, -3095180093797086]], ![![-829508265137619048, -266301703455559903, -39083660215837242]], ![![-582678407592239091, -187060526133326986, -27453861347194675]]]
  g := ![![![477296087, 167438904, -292179030], ![-2361857622, -771037099, 1363936614], ![5962738845, 1699854562, -3092180281]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [5, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 72], [0, 1]]
 g := ![![[4, 54], [27], [16], [47, 48], [35], [1]], ![[19, 19], [27], [16], [36, 25], [35], [1]]]
 h' := ![![[53, 72], [35, 28], [30, 63], [57, 4], [69, 11], [68, 53], [0, 1]], ![[0, 1], [59, 45], [11, 10], [50, 69], [68, 62], [30, 20], [53, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [23, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [5, 20, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106958, 95865, 26441]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23527, -13175, 26441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65691837860511751, 21089420154817164, 3095180093797086]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![65691837860511751, 21089420154817164, 3095180093797086]] 
 ![![73, 0, 0], ![67, 1, 0], ![58, 0, 1]] where
  M :=![![![65691837860511751, 21089420154817164, 3095180093797086], ![829508265137619048, 266301703455559903, 39083660215837242], ![4822456336353380904, 1548180278828089542, 227218043239722661]]]
  hmulB := by decide  
  f := ![![![-14682261281, -535878792, 292179030]], ![![-12402842819, -468159389, 249480252]], ![![-14705351378, -431275914, 274500877]]]
  g := ![![![-20915339150033825, 21089420154817164, 3095180093797086], ![-264103536423334993, 266301703455559903, 39083660215837242], ![-1535400943192226476, 1548180278828089542, 227218043239722661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![14682261281, 535878792, -292179030]] ![![65691837860511751, 21089420154817164, 3095180093797086]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [36, 63, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 43, 24], [74, 35, 55], [0, 1]]
 g := ![![[34, 73, 19], [8, 22, 21], [15, 27, 21], [25, 20, 55], [35, 1], []], ![[64, 44, 73, 71], [20, 70], [31, 8, 4, 74], [22, 78], [46, 40], [25, 23]], ![[30, 56, 8, 50], [74, 56, 12, 49], [18, 65, 22, 18], [11, 67, 54, 23], [23, 32], [73, 23]]]
 h' := ![![[40, 43, 24], [28, 58, 63], [13, 71, 10], [48, 12, 10], [4, 50, 56], [0, 0, 1], [0, 1]], ![[74, 35, 55], [75, 43, 42], [57, 72], [23, 63, 6], [45, 24], [68, 10, 35], [40, 43, 24]], ![[0, 1], [69, 57, 53], [14, 15, 69], [28, 4, 63], [57, 5, 23], [4, 69, 43], [74, 35, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 41], []]
 b := ![[], [78, 30, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [36, 63, 44, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141252, 49928, 7979]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1788, 632, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB165I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB165I1 : PrimesBelowBoundCertificateInterval O 31 79 165 where
  m := 11
  g := ![1, 3, 3, 2, 3, 1, 3, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB165I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N0, I41N1, I43N0, I43N1, I43N2, I47N1, I53N0, I53N1, I53N2, I61N0, I61N1, I67N1, I71N1, I73N1]
  Il := ![[], [I41N0, I41N1, I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N0, I53N1, I53N2], [], [I61N0, I61N0, I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
