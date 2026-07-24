
import IdealArithmetic.Examples.NF3_1_504175_1.RI3_1_504175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1273743604, 385197580, 29732833]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![1273743604, 385197580, 29732833]] 
 ![![83, 0, 0], ![0, 83, 0], ![78, 55, 1]] where
  M :=![![![1273743604, 385197580, 29732833], ![16501722315, 4990347729, 385197580], ![213784656900, 64651419815, 4990347729]]]
  hmulB := by decide  
  f := ![![![402527, 36025, -5179]], ![![-2874345, -244848, 36025]], ![![-1285518, -108770, 16055]]]
  g := ![![![-12595390, -15061545, 29732833], ![-163176975, -195126737, 385197580], ![-2114005614, -2527924160, 4990347729]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [46, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 82], [0, 1]]
 g := ![![[72, 38], [56, 70], [65], [51], [25, 64], [1]], ![[44, 45], [35, 13], [65], [51], [39, 19], [1]]]
 h' := ![![[8, 82], [80, 11], [25, 53], [39, 27], [12, 36], [37, 8], [0, 1]], ![[0, 1], [2, 72], [34, 30], [6, 56], [51, 47], [18, 75], [8, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [11, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [46, 75, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1156, 730, 51]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -25, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![402527, 36025, -5179]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![402527, 36025, -5179]] 
 ![![83, 0, 0], ![28, 1, 0], ![46, 0, 1]] where
  M :=![![![402527, 36025, -5179], ![-2874345, -244848, 36025], ![19993875, 1628780, -244848]]]
  hmulB := by decide  
  f := ![![![1273743604, 385197580, 29732833]], ![![628512569, 190070843, 14671288]], ![![3281648948, 992415765, 76603109]]]
  g := ![![![-4433, 36025, -5179], ![28003, -244848, 36025], ![-172879, 1628780, -244848]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![1273743604, 385197580, 29732833]] ![![402527, 36025, -5179]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181259914238969, -54815490414591, -4231126847440]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-181259914238969, -54815490414591, -4231126847440]] 
 ![![89, 0, 0], ![57, 1, 0], ![44, 0, 1]] where
  M :=![![![-181259914238969, -54815490414591, -4231126847440], ![-2348275400329200, -710150770168969, -54815490414591], ![-30422597180098005, -9200211702153075, -710150770168969]]]
  hmulB := by decide  
  f := ![![![-1715005636, -118851321, 19392079]], ![![-977446263, -68151922, 11084238]], ![![-1589019451, -104755836, 17553435]]]
  g := ![![![35161714839102, -54815490414591, -4231126847440], ![455530337949933, -710150770168969, -54815490414591], ![5901529255393954, -9200211702153075, -710150770168969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155804569, -47117444, -3636926]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-155804569, -47117444, -3636926]] 
 ![![89, 0, 0], ![59, 1, 0], ![79, 0, 1]] where
  M :=![![![-155804569, -47117444, -3636926], ![-2018493930, -610420319, -47117444], ![-26150181420, -7908174430, -610420319]]]
  hmulB := by decide  
  f := ![![![-304841, -57544, 6258]], ![![-163061, -32783, 3502]], ![![-629431, -92874, 10919]]]
  g := ![![![32712829, -47117444, -3636926], ![423804303, -610420319, -47117444], ![5490509159, -7908174430, -610420319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63543216792814, -19216342486109, -1483281130710]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-63543216792814, -19216342486109, -1483281130710]] 
 ![![89, 0, 0], ![62, 1, 0], ![72, 0, 1]] where
  M :=![![![-63543216792814, -19216342486109, -1483281130710], ![-823221027544050, -248953358131564, -19216342486109], ![-10665070079790495, -3225263838307675, -248953358131564]]]
  hmulB := by decide  
  f := ![![![-377499521, -6754774, 2770559]], ![![-245700113, -5055906, 1854156]], ![![-347515338, 2325503, 1891018]]]
  g := ![![![13872654592776, -19216342486109, -1483281130710], ![179724312759694, -248953358131564, -19216342486109], ![2328381232368067, -3225263838307675, -248953358131564]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-181259914238969, -54815490414591, -4231126847440]] ![![-155804569, -47117444, -3636926]]
  ![![249530592158393307546791, 75461482148627023908965, 5824760494739293928058]] where
 M := ![![![249530592158393307546791, 75461482148627023908965, 5824760494739293928058]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![249530592158393307546791, 75461482148627023908965, 5824760494739293928058]] ![![-63543216792814, -19216342486109, -1483281130710]]
  ![![89, 0, 0]] where
 M := ![![![-140098934262739488296123549044227176834, -42367844100648804849977171250733342629, -3270311389838272179967613187220141507]]]
 hmul := by decide  
 g := ![![![![-1574145328794825711192399427463226706, -476043192142121402808732261244194861, -36745071795935642471546215586743163]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9369736139473, 2833537043736, 218716544690]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![9369736139473, 2833537043736, 218716544690]] 
 ![![97, 0, 0], ![39, 1, 0], ![31, 0, 1]] where
  M :=![![![9369736139473, 2833537043736, 218716544690], ![121387682302950, 36709304225723, 2833537043736], ![1572613059273480, 475579812769950, 36709304225723]]]
  hmulB := by decide  
  f := ![![![78339529, -3155628, -223174]], ![![30220413, -748729, -122262]], ![![6980947, -6351954, 448705]]]
  g := ![![![-1112561045893, 2833537043736, 218716544690], ![-14413554957279, 36709304225723, 2833537043736], ![-186731835770639, 475579812769950, 36709304225723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16942503982, -984041279, 176901292]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-16942503982, -984041279, 176901292]] 
 ![![97, 0, 0], ![59, 1, 0], ![11, 0, 1]] where
  M :=![![![-16942503982, -984041279, 176901292], ![98180217060, 5170157518, -984041279], ![-546142909845, -24824942815, 5170157518]]]
  hmulB := by decide  
  f := ![![![2301760282157459939, 696083958844568542, 53729693998242585]], ![![1707462235219739908, 516360057770797186, 39857071182895681]], ![![4243772786211006187, 1283375243009133571, 99061841916685067]]]
  g := ![![![403814611, -984041279, 176901292], ![-2020975489, 5170157518, -984041279], ![8883061686, -24824942815, 5170157518]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27803, -8408, -649]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-27803, -8408, -649]] 
 ![![97, 0, 0], ![96, 1, 0], ![96, 0, 1]] where
  M :=![![![-27803, -8408, -649], ![-360195, -108928, -8408], ![-4666440, -1411195, -108928]]]
  hmulB := by decide  
  f := ![![![18376, 1069, -192]], ![![17088, 1000, -179]], ![![24303, 1337, -248]]]
  g := ![![![8677, -8408, -649], ![112413, -108928, -8408], ![1456344, -1411195, -108928]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![9369736139473, 2833537043736, 218716544690]] ![![-16942503982, -984041279, 176901292]]
  ![![-18376, -1069, 192]] where
 M := ![![![-18376, -1069, 192]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-18376, -1069, 192]] ![![-27803, -8408, -649]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [66, 47, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 12, 26], [75, 88, 75], [0, 1]]
 g := ![![[100, 58, 100], [6, 30], [53, 9, 96], [1, 88], [44, 85], [1]], ![[27, 78, 78, 99], [0, 84], [98, 78, 57, 26], [90, 76], [62, 19], [51, 21, 75, 2]], ![[78, 33, 50, 67], [96, 4], [68, 46, 58, 72], [38, 9], [50, 23], [53, 49, 18, 99]]]
 h' := ![![[66, 12, 26], [64, 86, 91], [37, 29, 63], [65, 89, 46], [38, 41, 47], [35, 54, 40], [0, 1]], ![[75, 88, 75], [20, 28, 43], [11, 88, 36], [32, 91, 100], [35, 80, 51], [17, 18, 76], [66, 12, 26]], ![[0, 1], [2, 88, 68], [50, 85, 2], [12, 22, 56], [46, 81, 3], [35, 29, 86], [75, 88, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 82], []]
 b := ![[], [34, 53, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [66, 47, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4179784, 3124334, 461671]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41384, 30934, 4571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9459032381846719, 2860541455265415, 220800975382077]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![9459032381846719, 2860541455265415, 220800975382077]] 
 ![![103, 0, 0], ![0, 103, 0], ![12, 72, 1]] where
  M :=![![![9459032381846719, 2860541455265415, 220800975382077], ![122544541337052735, 37059154304606344, 2860541455265415], ![1587600507672305325, 480112223245229610, 37059154304606344]]]
  hmulB := by decide  
  f := ![![![-1343319338, -99699930, 15699279]], ![![8713099845, 619090537, -99699930]], ![![5396989278, 384744933, -61853525]]]
  g := ![![![66110880361765, -126574065749943, 220800975382077], ![856485862853085, -1639804179364112, 2860541455265415], ![11096025786573099, -21244144530936186, 37059154304606344]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [64, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 102], [0, 1]]
 g := ![![[58, 66], [70, 16], [79, 25], [64], [38], [99, 1]], ![[0, 37], [6, 87], [82, 78], [64], [38], [95, 102]]]
 h' := ![![[99, 102], [52, 13], [94, 4], [13, 98], [68, 95], [50, 55], [0, 1]], ![[0, 1], [0, 90], [78, 99], [33, 5], [100, 8], [36, 48], [99, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [91, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [64, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2794, 181, 250]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -173, 250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1343319338, -99699930, 15699279]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1343319338, -99699930, 15699279]] 
 ![![103, 0, 0], ![31, 1, 0], ![69, 0, 1]] where
  M :=![![![-1343319338, -99699930, 15699279], ![8713099845, 619090537, -99699930], ![-55333461150, -3749391405, 619090537]]]
  hmulB := by decide  
  f := ![![![9459032381846719, 2860541455265415, 220800975382077]], ![![4036646069653408, 1220737275901303, 94226909632134]], ![![21750230505045912, 6577568773383915, 507712831125919]]]
  g := ![![![6447847, -99699930, 15699279], ![-34945744, 619090537, -99699930], ![176508984, -3749391405, 619090537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![9459032381846719, 2860541455265415, 220800975382077]] ![![-1343319338, -99699930, 15699279]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2193625118, 92522011, -20211406]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![2193625118, 92522011, -20211406]] 
 ![![107, 0, 0], ![22, 1, 0], ![51, 0, 1]] where
  M :=![![![2193625118, 92522011, -20211406], ![-11217330330, -332800632, 92522011], ![51349716105, 347921045, -332800632]]]
  hmulB := by decide  
  f := ![![![78565905906977929, 23759410238271682, 1833953829075529]], ![![25666301916733019, 7761842614798094, 599125182036760]], ![![160685363397165027, 48593463337128361, 3750857755367019]]]
  g := ![![![11111426, 92522011, -20211406], ![-80507841, -332800632, 92522011], ![566993321, 347921045, -332800632]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![437, 44, -6]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![437, 44, -6]] 
 ![![107, 0, 0], ![35, 1, 0], ![59, 0, 1]] where
  M :=![![![437, 44, -6], ![-3330, -313, 44], ![24420, 2170, -313]]]
  hmulB := by decide  
  f := ![![![-2489, -752, -58]], ![![-1115, -337, -26]], ![![-5273, -1594, -123]]]
  g := ![![![-7, 44, -6], ![47, -313, 44], ![-309, 2170, -313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14992687682, -1128206540, 176412057]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-14992687682, -1128206540, 176412057]] 
 ![![107, 0, 0], ![50, 1, 0], ![68, 0, 1]] where
  M :=![![![-14992687682, -1128206540, 176412057], ![97908691635, 7058819443, -1128206540], ![-626154629700, -43117125865, 7058819443]]]
  hmulB := by decide  
  f := ![![![1181908541978673149, 357425394499202915, 27589138967547349]], ![![695396254447873235, 210297389139086332, 16232545260528695]], ![![2605054904687919551, 787804423040513470, 60809461333787958]]]
  g := ![![![274968406, -1128206540, 176412057], ![-1666488185, 7058819443, -1128206540], ![9810298518, -43117125865, 7058819443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![2193625118, 92522011, -20211406]] ![![437, 44, -6]]
  ![![156953345416, 23701364729, -2764612146]] where
 M := ![![![156953345416, 23701364729, -2764612146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![156953345416, 23701364729, -2764612146]] ![![-14992687682, -1128206540, 176412057]]
  ![![107, 0, 0]] where
 M := ![![![1698491816655924312403, 109429993268479161597, -18566470144853801626]]]
 hmul := by decide  
 g := ![![![![15873755295849759929, 1022710217462422071, -173518412568727118]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5029801, 1521081, 117410]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![5029801, 1521081, 117410]] 
 ![![109, 0, 0], ![0, 109, 0], ![19, 12, 1]] where
  M :=![![![5029801, 1521081, 117410], ![65162550, 19706051, 1521081], ![844199955, 255297675, 19706051]]]
  hmulB := by decide  
  f := ![![![29614, 2391, -361]], ![![-200355, -15511, 2391]], ![![-4721, -387, 58]]]
  g := ![![![25679, 1029, 117410], ![332679, 13331, 1521081], ![4309954, 172707, 19706051]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [26, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 108], [0, 1]]
 g := ![![[21, 21], [104], [54, 78], [29, 61], [80], [108, 1]], ![[0, 88], [104], [85, 31], [77, 48], [80], [107, 108]]]
 h' := ![![[108, 108], [81, 81], [13, 70], [9, 80], [13, 37], [26, 84], [0, 1]], ![[0, 1], [0, 28], [52, 39], [38, 29], [85, 72], [51, 25], [108, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [18, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [26, 1, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3302, 4248, 1117]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-225, -84, 1117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29614, 2391, -361]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![29614, 2391, -361]] 
 ![![109, 0, 0], ![97, 1, 0], ![74, 0, 1]] where
  M :=![![![29614, 2391, -361], ![-200355, -15511, 2391], ![1327005, 98520, -15511]]]
  hmulB := by decide  
  f := ![![![5029801, 1521081, 117410]], ![![5073883, 1534412, 118439]], ![![11159681, 3374841, 260499]]]
  g := ![![![-1611, 2391, -361], ![10342, -15511, 2391], ![-64969, 98520, -15511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![5029801, 1521081, 117410]] ![![29614, 2391, -361]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [97, 49, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 44, 49], [19, 68, 64], [0, 1]]
 g := ![![[75, 13, 87], [49, 72], [5, 2], [56, 22], [24, 54, 11], [1]], ![[45, 47, 100, 14], [105, 2], [82, 16], [110, 63], [48, 67, 19, 22], [15, 20, 35, 16]], ![[74, 57, 28, 97], [20, 98], [57, 62], [105, 53], [105, 67, 3, 60], [42, 5, 107, 97]]]
 h' := ![![[70, 44, 49], [102, 53, 55], [30, 33, 80], [96, 26, 51], [45, 57, 19], [16, 64, 89], [0, 1]], ![[19, 68, 64], [67, 60, 9], [67, 58, 51], [87, 83, 109], [19, 61, 17], [59, 25, 35], [70, 44, 49]], ![[0, 1], [69, 0, 49], [38, 22, 95], [16, 4, 66], [101, 108, 77], [73, 24, 102], [19, 68, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 25], []]
 b := ![[], [18, 44, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [97, 49, 24, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-489968, -168144, -14690]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4336, -1488, -130]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [73, 74, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 116, 14], [79, 10, 113], [0, 1]]
 g := ![![[102, 43, 113], [10, 1, 50], [109, 1, 19], [40, 53, 76], [67, 20, 1], [1]], ![[22, 87, 54, 95], [44, 58, 26, 114], [84, 90, 38, 65], [114, 19, 34, 80], [92, 76, 58, 27], [81, 37, 59, 77]], ![[35, 98, 45, 115], [81, 7, 123, 82], [5, 109, 8, 81], [57, 107, 74, 44], [22, 115, 55, 8], [121, 83, 115, 50]]]
 h' := ![![[47, 116, 14], [32, 107, 85], [44, 117, 80], [1, 63, 107], [62, 54, 40], [54, 53, 126], [0, 1]], ![[79, 10, 113], [112, 45, 62], [26, 20, 25], [55, 28, 47], [32, 123, 13], [120, 69, 97], [47, 116, 14]], ![[0, 1], [50, 102, 107], [123, 117, 22], [30, 36, 100], [0, 77, 74], [82, 5, 31], [79, 10, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 11], []]
 b := ![[], [77, 43, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [73, 74, 1, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8153654, 2510536, 184658]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64202, 19768, 1454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [55, 86, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 98, 108], [37, 32, 23], [0, 1]]
 g := ![![[41, 68, 28], [35, 42, 44], [128, 44], [1, 35], [0, 25], [9, 1], []], ![[4, 85, 94, 60], [36, 119, 41, 48], [40, 89], [89, 100], [91, 15], [128, 107], [122, 5]], ![[51, 67, 22, 14], [27, 26, 51, 37], [53, 74], [86, 34], [53, 3], [36, 41], [76, 5]]]
 h' := ![![[103, 98, 108], [40, 94, 91], [49, 86, 100], [88, 114, 31], [55, 61, 64], [29, 88, 126], [0, 0, 1], [0, 1]], ![[37, 32, 23], [89, 89, 95], [43, 123, 43], [127, 89, 73], [31, 34, 121], [78, 33, 43], [100, 120, 32], [103, 98, 108]], ![[0, 1], [23, 79, 76], [113, 53, 119], [88, 59, 27], [44, 36, 77], [48, 10, 93], [71, 11, 98], [37, 32, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 70], []]
 b := ![[], [118, 75, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [55, 86, 122, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64845, -33405, 2096]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-495, -255, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11424173, 3454827, 266673]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![11424173, 3454827, 266673]] 
 ![![137, 0, 0], ![15, 1, 0], ![49, 0, 1]] where
  M :=![![![11424173, 3454827, 266673], ![148003515, 44758298, 3454827], ![1917428985, 579856890, 44758298]]]
  hmulB := by decide  
  f := ![![![148774, 22524, -2625]], ![![5655, 1157, -123]], ![![144458, 17973, -2248]]]
  g := ![![![-390257, 3454827, 266673], ![-5055894, 44758298, 3454827], ![-65500591, 579856890, 44758298]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![282028, 19286, -3169]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![282028, 19286, -3169]] 
 ![![137, 0, 0], ![47, 1, 0], ![120, 0, 1]] where
  M :=![![![282028, 19286, -3169], ![-1758795, -114097, 19286], ![10703730, 651955, -114097]]]
  hmulB := by decide  
  f := ![![![444521279, 134429347, 10376403]], ![![194535794, 58830299, 4541024]], ![![933947745, 282438640, 21801022]]]
  g := ![![![-1782, 19286, -3169], ![9412, -114097, 19286], ![-45595, 651955, -114097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 2, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![13, 2, 0]] 
 ![![137, 0, 0], ![75, 1, 0], ![129, 0, 1]] where
  M :=![![![13, 2, 0], ![0, 13, 2], ![1110, 250, 13]]]
  hmulB := by decide  
  f := ![![![-331, -26, 4]], ![![-165, -13, 2]], ![![-417, -32, 5]]]
  g := ![![![-1, 2, 0], ![-9, 13, 2], ![-141, 250, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![11424173, 3454827, 266673]] ![![282028, 19286, -3169]]
  ![![-331, -26, 4]] where
 M := ![![![-331, -26, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-331, -26, 4]] ![![13, 2, 0]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB201I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB201I2 : PrimesBelowBoundCertificateInterval O 79 137 201 where
  m := 11
  g := ![2, 3, 3, 1, 2, 3, 2, 1, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB201I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![137, 137, 137]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I103N1, I107N0, I107N1, I107N2, I109N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [], [], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
