
import IdealArithmetic.Examples.NF3_1_311116_1.RI3_1_311116_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6071926328, -421272137, -400045849]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![6071926328, -421272137, -400045849]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 21, 1]] where
  M :=![![![6071926328, -421272137, -400045849], ![-44468768103, 7629657148, -2127586973], ![-22694777403, -5073238309, 8893473559]]]
  hmulB := by decide  
  f := ![![![1542172928995145975, 156110825352869052, 106716372489720269]], ![![11993700704948396208, 1214096344762562465, 829948579627494043]], ![![8599002058214523723, 870458353456880228, 595039822986790808]]]
  g := ![![![553339916, 215667316, -400045849], ![868226025, 1413756313, -2127586973], ![-9266481771, -5184761704, 8893473559]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [0, 1]]
 g := ![![[6, 26], [10], [9, 3], [11], [1]], ![[0, 11], [10], [14, 34], [11], [1]]]
 h' := ![![[14, 36], [8, 10], [21, 11], [27, 22], [27, 14], [0, 1]], ![[0, 1], [0, 27], [27, 26], [2, 15], [1, 23], [14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [11, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [10, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1497, 901, -498]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![525, 307, -498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1542172928995145975, 156110825352869052, 106716372489720269]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1542172928995145975, 156110825352869052, 106716372489720269]] 
 ![![37, 0, 0], ![23, 1, 0], ![28, 0, 1]] where
  M :=![![![1542172928995145975, 156110825352869052, 106716372489720269], ![11993700704948396208, 1214096344762562465, 829948579627494043], ![10777135906195802283, 1090946125187470799, 745763868703955309]]]
  hmulB := by decide  
  f := ![![![6071926328, -421272137, -400045849]], ![![2572582093, -55664919, -306179500]], ![![3981598913, -455915085, -62373249]]]
  g := ![![![-136119850914405669, 156110825352869052, 106716372489720269], ![-1058623660923253343, 1214096344762562465, 829948579627494043], ![-951243602616939858, 1090946125187470799, 745763868703955309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![6071926328, -421272137, -400045849]] ![![1542172928995145975, 156110825352869052, 106716372489720269]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [27, 18, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 26, 37], [24, 14, 4], [0, 1]]
 g := ![![[37, 33, 8], [2, 16], [10, 40], [22, 9, 1], []], ![[8, 18, 12, 31], [26, 16], [7, 2], [39, 31, 4, 36], [18, 16]], ![[36, 8, 23, 4], [15, 23], [27, 20], [39, 24, 32, 39], [10, 16]]]
 h' := ![![[26, 26, 37], [36, 6, 7], [7, 28, 37], [21, 17, 9], [0, 0, 1], [0, 1]], ![[24, 14, 4], [5, 23, 33], [16, 25, 37], [0, 25, 17], [26, 22, 14], [26, 26, 37]], ![[0, 1], [26, 12, 1], [29, 29, 8], [26, 40, 15], [19, 19, 26], [24, 14, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 40], []]
 b := ![[], [20, 3, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [27, 18, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2536219, -163918, 37064]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61859, -3998, 904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1918698865, 239799624, 7690404]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-1918698865, 239799624, 7690404]] 
 ![![43, 0, 0], ![0, 43, 0], ![35, 9, 1]] where
  M :=![![![-1918698865, 239799624, 7690404], ![1549962504, -1485242041, 1431107340], ![25460006364, -1292680068, -2204640913]]]
  hmulB := by decide  
  f := ![![![-119171844253086571, -12063507675040680, -8246537520202668]], ![![-926816575207010184, -93819634481951923, -64134508530041412]], ![![-310352788743580535, -31416340599944133, -21476011661262697]]]
  g := ![![![-50880535, 3967116, 7690404], ![-1128809172, -334074607, 1431107340], ![2386568333, 431374143, -2204640913]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [39, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 42], [0, 1]]
 g := ![![[26, 31], [10, 4], [16], [42, 23], [1]], ![[25, 12], [39, 39], [16], [26, 20], [1]]]
 h' := ![![[18, 42], [40, 17], [37, 41], [39, 4], [4, 18], [0, 1]], ![[0, 1], [2, 26], [1, 2], [25, 39], [27, 25], [18, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [17, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [39, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![588492, 600749, -184566]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![163914, 52601, -184566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119171844253086571, -12063507675040680, -8246537520202668]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-119171844253086571, -12063507675040680, -8246537520202668]] 
 ![![43, 0, 0], ![33, 1, 0], ![23, 0, 1]] where
  M :=![![![-119171844253086571, -12063507675040680, -8246537520202668], ![-926816575207010184, -93819634481951923, -64134508530041412], ![-832806190252841364, -84303166833606612, -57629111456829883]]]
  hmulB := by decide  
  f := ![![![-1918698865, 239799624, 7690404]], ![![-1436444187, 149491757, 39183504]], ![![-434187617, 98202588, -47157247]]]
  g := ![![![10897541209021331, -12063507675040680, -8246537520202668], ![84751745555543157, -93819634481951923, -64134508530041412], ![76155066947982887, -84303166833606612, -57629111456829883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-1918698865, 239799624, 7690404]] ![![-119171844253086571, -12063507675040680, -8246537520202668]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99565437500, 4636031297, 9088124284]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-99565437500, 4636031297, 9088124284]] 
 ![![47, 0, 0], ![11, 1, 0], ![8, 0, 1]] where
  M :=![![![-99565437500, 4636031297, 9088124284], ![995425516563, -144822120610, 18728063498], ![-17331704112, 144858173614, -158730214501]]]
  hmulB := by decide  
  f := ![![![20274733195267692823838, 2052367327563440680173, 1402985319685049190146]], ![![8100033652268516077415, 819948862457066521813, 560511854515556084734]], ![![6465603696105219834278, 654499058066868424960, 447411415044135117531]]]
  g := ![![![-4750356937, 4636031297, 9088124284], ![51886049687, -144822120610, 18728063498], ![-7253827614, 144858173614, -158730214501]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4711651, -2500890, 3457422]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-4711651, -2500890, 3457422]] 
 ![![47, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![-4711651, -2500890, 3457422], ![365898906, -30457963, -18462762], ![-467169174, 80696358, -22955293]]]
  hmulB := by decide  
  f := ![![![2189049116868955, 221592700758306, 151479368209566]], ![![1107432675293858, 112103011090661, 76632909099858]], ![![1396719518764633, 141386891678148, 96651184588793]]]
  g := ![![![-940811, -2500890, 3457422], ![27188720, -30457963, -18462762], ![-26177429, 80696358, -22955293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2144371233468441474390288092971251532, 217070055391149923237294673352004937, 148387716451596061972268207410437148]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![2144371233468441474390288092971251532, 217070055391149923237294673352004937, 148387716451596061972268207410437148]] 
 ![![47, 0, 0], ![19, 1, 0], ![28, 0, 1]] where
  M :=![![![2144371233468441474390288092971251532, 217070055391149923237294673352004937, 148387716451596061972268207410437148], ![16677083542945824462716850420383226795, 1688185045541164949031268195212638518, 1154032615895303477451499832701592474], ![14985466144503216177208536899621615760, 1516946280233425638049327900686276190, 1036974879367715179319384175156623707]]]
  hmulB := by decide  
  f := ![![![-2080255142049247834, 841176668048664661, -638454232272822526]], ![![-2254348399579883993, 413088942140630749, -137130131332315266]], ![![1467911221519738894, 135643750720999884, -361009040853191661]]]
  g := ![![![-130527997438470144730677032089554945, 217070055391149923237294673352004937, 148387716451596061972268207410437148], ![-1015135012072442700798281714985138177, 1688185045541164949031268195212638518, 1154032615895303477451499832701592474], ![-912166166004848850354711704634108418, 1516946280233425638049327900686276190, 1036974879367715179319384175156623707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-99565437500, 4636031297, 9088124284]] ![![-4711651, -2500890, 3457422]]
  ![![-2080255142049247834, 841176668048664661, -638454232272822526]] where
 M := ![![![-2080255142049247834, 841176668048664661, -638454232272822526]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-2080255142049247834, 841176668048664661, -638454232272822526]] ![![2144371233468441474390288092971251532, 217070055391149923237294673352004937, 148387716451596061972268207410437148]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 30, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30, 18], [14, 22, 35], [0, 1]]
 g := ![![[41, 27, 28], [23, 1], [1, 26, 29], [26, 42], [1]], ![[33, 44, 21, 33], [36, 52], [16, 16, 31, 14], [9, 52], [40, 25, 13, 2]], ![[27, 20, 29, 8], [40, 7], [39, 50, 33, 27], [26, 4], [41, 20, 22, 51]]]
 h' := ![![[14, 30, 18], [29, 45, 44], [43, 29, 52], [52, 36, 20], [43, 23, 28], [0, 1]], ![[14, 22, 35], [21, 40, 29], [13, 6, 23], [1, 22, 28], [12, 25, 23], [14, 30, 18]], ![[0, 1], [28, 21, 33], [2, 18, 31], [9, 48, 5], [2, 5, 2], [14, 22, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 35], []]
 b := ![[], [28, 50, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 30, 25, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4012259, 423629, -139072]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75703, 7993, -2624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1321, 80, 100]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1321, 80, 100]] 
 ![![59, 0, 0], ![0, 59, 0], ![57, 48, 1]] where
  M :=![![![-1321, 80, 100], ![11040, -1761, 380], ![2940, 1420, -2001]]]
  hmulB := by decide  
  f := ![![![-50579, -5120, -3500]], ![![-393360, -39819, -27220]], ![![-374877, -37948, -25941]]]
  g := ![![![-119, -80, 100], ![-180, -339, 380], ![1983, 1652, -2001]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 58], [0, 1]]
 g := ![![[23, 15], [18, 22], [46], [2, 57], [26, 1]], ![[0, 44], [0, 37], [46], [9, 2], [52, 58]]]
 h' := ![![[26, 58], [46, 30], [57, 50], [51, 20], [14, 23], [0, 1]], ![[0, 1], [0, 29], [0, 9], [40, 39], [22, 36], [26, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [56, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 33, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1451, 871, -578]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![583, 485, -578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50579, 5120, 3500]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![50579, 5120, 3500]] 
 ![![59, 0, 0], ![8, 1, 0], ![56, 0, 1]] where
  M :=![![![50579, 5120, 3500], ![393360, 39819, 27220], ![353460, 35780, 24459]]]
  hmulB := by decide  
  f := ![![![1321, -80, -100]], ![![-8, 19, -20]], ![![1204, -100, -61]]]
  g := ![![![-3159, 5120, 3500], ![-24568, 39819, 27220], ![-22076, 35780, 24459]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1321, 80, 100]] ![![50579, 5120, 3500]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 30, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 54, 6], [10, 6, 55], [0, 1]]
 g := ![![[18, 39, 27], [38, 13], [24, 49, 13], [55, 55, 19], [1]], ![[46, 52, 14, 55], [51, 56], [48, 43, 37, 23], [41, 22, 4, 55], [12, 36, 21, 33]], ![[29, 10, 54, 23], [37, 25], [49, 41, 30, 11], [15, 22, 51, 11], [26, 15, 54, 28]]]
 h' := ![![[8, 54, 6], [29, 25, 24], [31, 7, 47], [38, 48, 47], [14, 31, 18], [0, 1]], ![[10, 6, 55], [34, 19, 50], [33, 31, 19], [2, 49, 21], [9, 20, 50], [8, 54, 6]], ![[0, 1], [39, 17, 48], [58, 23, 56], [48, 25, 54], [22, 10, 54], [10, 6, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 30], []]
 b := ![[], [28, 48, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 30, 43, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172163960, -10945901, 9769272]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2822360, -179441, 160152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019455606807234100535217630060, 103197283000542273897258844411, 70545009724468472889285434906]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1019455606807234100535217630060, 103197283000542273897258844411, 70545009724468472889285434906]] 
 ![![67, 0, 0], ![0, 67, 0], ![1, 14, 1]] where
  M :=![![![1019455606807234100535217630060, 103197283000542273897258844411, 70545009724468472889285434906], ![7928452899244221893734603503081, 802580114461507810994022709446, 548638688278785170494267631560], ![7124241009763862626214685406746, 721171486761647341512870196748, 492988265459880989302246176213]]]
  hmulB := by decide  
  f := ![![![-566289638187446, 8102255383435, 72017327296852]], ![![7802178114210321, -982189091201688, -23403794996242]], ![![1573645669943992, -185415363210457, -18837785970187]]]
  g := ![![![14162844732578591457401973062, -13200490345403229053025929019, 70545009724468472889285434906], ![110146480760678160048363221963, -102662112260320665312324240782, 548638688278785170494267631560], ![98973921556775845327051331799, -92248719845920694159978750302, 492988265459880989302246176213]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 66], [0, 1]]
 g := ![![[9, 62], [59, 64], [21], [40], [22], [1]], ![[0, 5], [0, 3], [21], [40], [22], [1]]]
 h' := ![![[42, 66], [52, 53], [1, 59], [29, 17], [50, 43], [27, 42], [0, 1]], ![[0, 1], [0, 14], [0, 8], [6, 50], [47, 24], [49, 25], [42, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [23, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [40, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-519, 171, -117]
  a := ![-2, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 27, -117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-566289638187446, 8102255383435, 72017327296852]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-566289638187446, 8102255383435, 72017327296852]] 
 ![![67, 0, 0], ![51, 1, 0], ![19, 0, 1]] where
  M :=![![![-566289638187446, 8102255383435, 72017327296852], ![7802178114210321, -982189091201688, -23403794996242], ![-3229944074509584, 1319715686339578, -1006495857351993]]]
  hmulB := by decide  
  f := ![![![1019455606807234100535217630060, 103197283000542273897258844411, 70545009724468472889285434906]], ![![894338639498703895836279143823, 90531963395360653429167519021, 61887077376517571460415295698]], ![![395431306553750903528116722058, 40028654683163440978519227471, 27363335077981820510427902081]]]
  g := ![![![-35042296737057, 8102255383435, 72017327296852], ![870723789110821, -982189091201688, -23403794996242], ![-767343623703585, 1319715686339578, -1006495857351993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1019455606807234100535217630060, 103197283000542273897258844411, 70545009724468472889285434906]] ![![-566289638187446, 8102255383435, 72017327296852]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [48, 60, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 51, 34], [60, 19, 37], [0, 1]]
 g := ![![[19, 30, 57], [3, 63, 60], [60, 40, 54], [9, 50], [0, 1], []], ![[33, 1, 40, 70], [34, 7, 22, 33], [44, 46, 31, 63], [54, 9], [67, 6], [60, 20]], ![[1, 16, 39, 2], [34, 45, 38, 16], [18, 32, 30, 24], [11, 64], [7, 45], [57, 20]]]
 h' := ![![[11, 51, 34], [69, 29, 25], [31, 54, 42], [65, 42, 14], [0, 23, 11], [0, 0, 1], [0, 1]], ![[60, 19, 37], [70, 19, 41], [51, 3, 7], [28, 18, 61], [8, 62, 68], [10, 41, 19], [11, 51, 34]], ![[0, 1], [50, 23, 5], [12, 14, 22], [55, 11, 67], [21, 57, 63], [12, 30, 51], [60, 19, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 54], []]
 b := ![[], [56, 17, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [48, 60, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4866340, -409528, 185452]
  a := ![7, 5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68540, -5768, 2612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33476974304894268181358045211563, -3388801599869273323267665070756, -2316563332542543717636948921049]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-33476974304894268181358045211563, -3388801599869273323267665070756, -2316563332542543717636948921049]] 
 ![![73, 0, 0], ![0, 73, 0], ![10, 20, 1]] where
  M :=![![![-33476974304894268181358045211563, -3388801599869273323267665070756, -2316563332542543717636948921049], ![-260355244714202541474593478685560, -26355197509377552522071681826781, -18016246266673096221969041503487], ![-233946462830956527007601739141855, -23681893719092690695496039075395, -16188792709769732552268686614513]]]
  hmulB := by decide  
  f := ![![![176865451530544, -389659953041199, 408337408042289]], ![![42931460209443615, -3052478902805588, -2746297126289483]], ![![10890950020785175, -751367220759905, -722274897110257]]]
  g := ![![![-141251246294093575410802137001, 588252945903857548348922100688, -2316563332542543717636948921049], ![-1098531260924268208971274844530, 4574927778412114683798755455383, -18016246266673096221969041503487], ![-987103229222728787464587301325, 4110876170908246032190105386505, -16188792709769732552268686614513]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [45, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 72], [0, 1]]
 g := ![![[13, 35], [48], [27], [32, 37], [1], [1]], ![[51, 38], [48], [27], [68, 36], [1], [1]]]
 h' := ![![[72, 72], [28, 53], [61, 11], [20, 63], [9, 16], [28, 72], [0, 1]], ![[0, 1], [48, 20], [50, 62], [30, 10], [66, 57], [29, 1], [72, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [31, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [45, 1, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3585, 3520, -1065]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![195, 340, -1065]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![176865451530544, -389659953041199, 408337408042289]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![176865451530544, -389659953041199, 408337408042289]] 
 ![![73, 0, 0], ![27, 1, 0], ![16, 0, 1]] where
  M :=![![![176865451530544, -389659953041199, 408337408042289], ![42931460209443615, -3052478902805588, -2746297126289483], ![-65358507186859965, 10096370471050685, -1883499043681991]]]
  hmulB := by decide  
  f := ![![![-33476974304894268181358045211563, -3388801599869273323267665070756, -2316563332542543717636948921049]], ![![-15948404807484216196866584923257, -1614422475422574414387652585441, -1103608989661942145180365237970]], ![![-10542165091907737231634663870231, -1067160538589055669421625756267, -729504192197951123759724237689]]]
  g := ![![![57045008972141, -389659953041199, 408337408042289], ![2319029378162003, -3052478902805588, -2746297126289483], ![-4216774317894748, 10096370471050685, -1883499043681991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-33476974304894268181358045211563, -3388801599869273323267665070756, -2316563332542543717636948921049]] ![![176865451530544, -389659953041199, 408337408042289]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [75, 25, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 46, 24], [39, 32, 55], [0, 1]]
 g := ![![[15, 28, 44], [26, 8, 32], [52, 78, 73], [11, 32, 5], [20, 1], []], ![[30, 30, 77, 63], [51, 22, 7, 66], [46, 46, 42, 24], [4, 0, 31, 63], [18, 76], [61, 23]], ![[45, 65, 16, 31], [77, 54, 78, 21], [64, 63, 51, 42], [78, 78, 61, 21], [12, 62], [30, 23]]]
 h' := ![![[60, 46, 24], [25, 65, 53], [50, 0, 43], [44, 12, 28], [1, 57, 59], [0, 0, 1], [0, 1]], ![[39, 32, 55], [45, 60, 17], [74, 45, 33], [8, 43, 78], [11, 40, 17], [52, 58, 32], [60, 46, 24]], ![[0, 1], [26, 33, 9], [66, 34, 3], [8, 24, 52], [56, 61, 3], [61, 21, 46], [39, 32, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 41], []]
 b := ![[], [24, 59, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [75, 25, 59, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70863, -6320, 790]
  a := ![0, -4, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![897, -80, 10]
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



lemma PB158I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB158I1 : PrimesBelowBoundCertificateInterval O 31 79 158 where
  m := 11
  g := ![2, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB158I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I43N1, I47N0, I47N1, I47N2, I59N1, I67N1, I73N1]
  Il := ![[I37N1], [], [I43N1], [I47N0, I47N1, I47N2], [], [I59N1], [], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
