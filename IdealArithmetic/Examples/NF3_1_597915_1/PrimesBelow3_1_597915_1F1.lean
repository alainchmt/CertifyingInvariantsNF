
import IdealArithmetic.Examples.NF3_1_597915_1.RI3_1_597915_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![451307889016051210, 22500784476907890, -33880718394413793]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![451307889016051210, 22500784476907890, -33880718394413793]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 7, 1]] where
  M :=![![![451307889016051210, 22500784476907890, -33880718394413793], ![-5748601276490942823, -57161970258259601, 281648430998504499], ![8048843226458559522, -125697439808772765, -259928113908534527]]]
  hmulB := by decide  
  f := ![![![1358391616734999270645651971862526, 273170433286619121264339275201775, 118935730458558453706694944987041]], ![![20884350774986733826373514143187561, 4199810334390350347452483862247548, 1828556274917277608994629366653077]], ![![4814988349731290763815849780633064, 968286639553604170250312942945098, 421582516756991778114655234258987]]]
  g := ![![![12197510513947330, 7017994952373093, -33880718394413793], ![-155367602067322779, -54829756412102462, 281648430998504499], ![217536303417798906, 45778361014891052, -259928113908534527]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[22, 3], [30], [5, 11], [33], [1]], ![[23, 34], [30], [21, 26], [33], [1]]]
 h' := ![![[25, 36], [3, 22], [4, 20], [30, 14], [23, 25], [0, 1]], ![[0, 1], [35, 15], [23, 17], [10, 23], [19, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [15, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2701, 4245, 2504]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, -359, 2504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9512154576102101101844, -790127768730304802461, 920486548095253491171]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-9512154576102101101844, -790127768730304802461, 920486548095253491171]] 
 ![![37, 0, 0], ![21, 1, 0], ![2, 0, 1]] where
  M :=![![![-9512154576102101101844, -790127768730304802461, 920486548095253491171], ![155822944186827737385319, 3765733435326293840680, -9082481794128198893201], ![-249252180416693554126035, 375126153013620725728, 10347473143898629637788]]]
  hmulB := by decide  
  f := ![![![42372902044367511864228771758630647764591168, 8521124444873135998800187866002239981543756, 3710014103597748642286011865279511080331381]], ![![41656367663153487539927367881784985885301843, 8377030499526608182548526547363137721277697, 3647277011452555771663505851433759981035538]], ![![29238279332862714807562816143486079957083064, 5879772324501508475986317498195546644710867, 2559995267170292577184715063013342175862673]]]
  g := ![![![141609607325507912635, -790127768730304802461, 920486548095253491171], ![2565067719817080122093, 3765733435326293840680, -9082481794128198893201], ![-7508777727507482395727, 375126153013620725728, 10347473143898629637788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![451307889016051210, 22500784476907890, -33880718394413793]] ![![-9512154576102101101844, -790127768730304802461, 920486548095253491171]]
  ![![37, 0, 0]] where
 M := ![![![7658071015861662093882657661089936236425, -284568482485507946125318364180408228914, -139519948158766575095163026157986598864]]]
 hmul := by decide  
 g := ![![![![206974892320585461996828585434863141525, -7691040067175890435819415248119141322, -3770809409696393921490892598864502672]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2915635447, 1009889404, -535923194]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-2915635447, 1009889404, -535923194]] 
 ![![41, 0, 0], ![0, 41, 0], ![33, 22, 1]] where
  M :=![![![-2915635447, 1009889404, -535923194], ![-89623087366, -8996661533, 9686884814], ![239145564140, 9129271958, -16127844345]]]
  hmulB := by decide  
  f := ![![![1382013437464556953, 277920744554898208, 121003969446946694]], ![![21247520264537681090, 4272843151727345375, 1860354048098345582]], ![![13306630350332330901, 2675942587986602660, 1165079187151333981]]]
  g := ![![![360239755, 312199992, -535923194], ![-9982689908, -5417271401, 9686884814], ![18813766525, 8876630428, -16127844345]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 40], [0, 1]]
 g := ![![[26, 40], [37], [18], [39, 20], [1]], ![[0, 1], [37], [18], [26, 21], [1]]]
 h' := ![![[26, 40], [29, 32], [22, 18], [39, 10], [1, 26], [0, 1]], ![[0, 1], [0, 9], [39, 23], [12, 31], [21, 15], [26, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [25, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3806, 1877, 1634]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1408, -831, 1634]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1382013437464556953, 277920744554898208, 121003969446946694]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1382013437464556953, 277920744554898208, 121003969446946694]] 
 ![![41, 0, 0], ![32, 1, 0], ![14, 0, 1]] where
  M :=![![![1382013437464556953, 277920744554898208, 121003969446946694], ![21247520264537681090, 4272843151727345375, 1860354048098345582], ![32519955107466203512, 6539712199137469946, 2847326623291849515]]]
  hmulB := by decide  
  f := ![![![-2915635447, 1009889404, -535923194]], ![![-4461546870, 568775595, -182016034]], ![![4837235802, 567505454, -576360221]]]
  g := ![![![-224524535623157059, 277920744554898208, 121003969446946694], ![-3451912616197907538, 4272843151727345375, 1860354048098345582], ![-5283253853439481170, 6539712199137469946, 2847326623291849515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-2915635447, 1009889404, -535923194]] ![![1382013437464556953, 277920744554898208, 121003969446946694]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3781, -302, 358]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-3781, -302, 358]] 
 ![![43, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![-3781, -302, 358], ![60614, 1399, -3490], ![-96034, 236, 3927]]]
  hmulB := by decide  
  f := ![![![6317513, 1270442, 553138]], ![![3287211, 661053, 287816]], ![![5367073, 1079310, 469921]]]
  g := ![![![-147, -302, 358], ![2237, 1399, -3490], ![-3459, 236, 3927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5710077802211, -1148287730956, -499953228520]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-5710077802211, -1148287730956, -499953228520]] 
 ![![43, 0, 0], ![29, 1, 0], ![24, 0, 1]] where
  M :=![![![-5710077802211, -1148287730956, -499953228520], ![-87788577538832, -17654145879919, -7686442162088], ![-134363001656996, -27020189854052, -11764325951223]]]
  hmulB := by decide  
  f := ![![![38389639, -803852, -1106248]], ![![21454033, -142787, -818448]], ![![21420172, -1152364, -157383]]]
  g := ![![![920677764651, -1148287730956, -499953228520], ![14154796857417, -17654145879919, -7686442162088], ![21664333184648, -27020189854052, -11764325951223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-3781, -302, 358]] ![![-3781, -302, 358]]
  ![![-38389639, 803852, 1106248]] where
 M := ![![![-38389639, 803852, 1106248]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-38389639, 803852, 1106248]] ![![-5710077802211, -1148287730956, -499953228520]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12383318, -2188920, 903913]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![12383318, -2188920, 903913]] 
 ![![47, 0, 0], ![0, 47, 0], ![41, 43, 1]] where
  M :=![![![12383318, -2188920, 903913], ![150191283, 21183079, -20223099], ![-486390532, -23652945, 36124425]]]
  hmulB := by decide  
  f := ![![![6104057451660, 1227516423345, 534448624999]], ![![93845747721519, 18872233346678, 8216785511763]], ![![94239727370968, 18951462039067, 8251280908242]]]
  g := ![![![-525045, -873557, 903913], ![20836986, 18952688, -20223099], ![-41861531, -33553260, 36124425]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 46], [0, 1]]
 g := ![![[0, 12], [0, 6], [0, 21], [], [1]], ![[0, 35], [0, 41], [0, 26], [], [1]]]
 h' := ![![[0, 46], [0, 23], [0, 10], [0, 16], [43], [0, 1]], ![[0, 1], [0, 24], [0, 37], [0, 31], [43], [0, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4592159, 6192125, 3772968]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3193607, -3320117, 3772968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6104057451660, 1227516423345, 534448624999]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![6104057451660, 1227516423345, 534448624999]] 
 ![![47, 0, 0], ![35, 1, 0], ![22, 0, 1]] where
  M :=![![![6104057451660, 1227516423345, 534448624999], ![93845747721519, 18872233346678, 8216785511763], ![143633678892119, 28884508571850, 12576032056606]]]
  hmulB := by decide  
  f := ![![![12383318, -2188920, 903913]], ![![12417179, -1179343, 242848]], ![![-4552288, -1527855, 1191713]]]
  g := ![![![-1034401853519, 1227516423345, 534448624999], ![-15903227673851, 18872233346678, 8216785511763], ![-24340358007829, 28884508571850, 12576032056606]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![12383318, -2188920, 903913]] ![![6104057451660, 1227516423345, 534448624999]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37371318087, -1887036458, 2821114262]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-37371318087, -1887036458, 2821114262]] 
 ![![53, 0, 0], ![0, 53, 0], ![10, 25, 1]] where
  M :=![![![-37371318087, -1887036458, 2821114262], ![478636465886, 4926514993, -23559634450], ![-672501402806, 10237094144, 21890962265]]]
  hmulB := by decide  
  f := ![![![6585440559860290565, 1324321814827025266, 576596744067804678]], ![![101246686865248650470, 20360550653494045889, 8864784286412788094]], ![![51924200213223258638, 10441875594315054709, 4546290336861608543]]]
  g := ![![![-1237404919, -1366318736, 2821114262], ![13476090762, 11205988231, -23559634450], ![-16819075952, -10132772877, 21890962265]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [21, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 52], [0, 1]]
 g := ![![[11, 13], [7], [11, 37], [7], [34, 1]], ![[29, 40], [7], [50, 16], [7], [15, 52]]]
 h' := ![![[34, 52], [2, 38], [34, 22], [1, 39], [28, 22], [0, 1]], ![[0, 1], [22, 15], [40, 31], [2, 14], [34, 31], [34, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [47, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [21, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3167, 4299, 2858]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-599, -1267, 2858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6585440559860290565, -1324321814827025266, -576596744067804678]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-6585440559860290565, -1324321814827025266, -576596744067804678]] 
 ![![53, 0, 0], ![15, 1, 0], ![46, 0, 1]] where
  M :=![![![-6585440559860290565, -1324321814827025266, -576596744067804678], ![-101246686865248650470, -20360550653494045889, -8864784286412788094], ![-154961034071013540414, -31162422013076499692, -13567813252667503649]]]
  hmulB := by decide  
  f := ![![![37371318087, 1887036458, -2821114262]], ![![1545911423, 441113809, -353907160]], ![![45124189336, 1444652508, -2861551289]]]
  g := ![![![750996922446492521, -1324321814827025266, -576596744067804678], ![11546068870040571513, -20360550653494045889, -8864784286412788094], ![17671598221657341940, -31162422013076499692, -13567813252667503649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-37371318087, -1887036458, 2821114262]] ![![-6585440559860290565, -1324321814827025266, -576596744067804678]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-406531511523462007, 8897258878538104, 11463340651169536]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-406531511523462007, 8897258878538104, 11463340651169536]] 
 ![![59, 0, 0], ![0, 59, 0], ![38, 7, 1]] where
  M :=![![![-406531511523462007, 8897258878538104, 11463340651169536], ![1978025769107066864, -184962943817965583, 36788049074796224], ![99977027484993320, 323203510702690808, -215419815786855135]]]
  hmulB := by decide  
  f := ![![![473807740199721451414430816252707, 95281996804432261270402302074392, 41484847950564374165256914667776]], ![![7284472993155372504799737012338480, 1464896145772612596035005271828075, 637801430583764967667447672591808]], ![![1358391616734999270645651971862526, 273170433286619121264339275201775, 118935730458558453706694944987041]]]
  g := ![![![-14273533157083125, -1209256367451672, 11463340651169536], ![9831862784149328, -7499648937992189, 36788049074796224], ![140439491989584550, 31036308834079267, -215419815786855135]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [55, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 58], [0, 1]]
 g := ![![[50, 19], [35, 12], [9], [47, 4], [23, 1]], ![[15, 40], [16, 47], [9], [21, 55], [46, 58]]]
 h' := ![![[23, 58], [22, 14], [39, 37], [11, 3], [33, 2], [0, 1]], ![[0, 1], [49, 45], [5, 22], [21, 56], [20, 57], [23, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [48, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [55, 36, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2670, 4125, 2216]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1382, -193, 2216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![473807740199721451414430816252707, 95281996804432261270402302074392, 41484847950564374165256914667776]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![473807740199721451414430816252707, 95281996804432261270402302074392, 41484847950564374165256914667776]] 
 ![![59, 0, 0], ![6, 1, 0], ![23, 0, 1]] where
  M :=![![![473807740199721451414430816252707, 95281996804432261270402302074392, 41484847950564374165256914667776], ![7284472993155372504799737012338480, 1464896145772612596035005271828075, 637801430583764967667447672591808], ![11149100307687934280746936235916808, 2242066664933814054075692855281304, 976173860847147776743105288717275]]]
  hmulB := by decide  
  f := ![![![-406531511523462007, 8897258878538104, 11463340651169536]], ![![-7816327119215342, -2230159161809101, 1789289711556160]], ![![-156783859958553099, 8946448557780800, 817576596441427]]]
  g := ![![![-17831114296438181728964271755127, 95281996804432261270402302074392, 41484847950564374165256914667776], ![-274141301439099954707823577766806, 1464896145772612596035005271828075, 637801430583764967667447672591808], ![-419581330193209303538960042987599, 2242066664933814054075692855281304, 976173860847147776743105288717275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-406531511523462007, 8897258878538104, 11463340651169536]] ![![473807740199721451414430816252707, 95281996804432261270402302074392, 41484847950564374165256914667776]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89354453216, 26999068081, -13843013917]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-89354453216, 26999068081, -13843013917]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 20, 1]] where
  M :=![![![-89354453216, 26999068081, -13843013917], ![-2313157243645, -243688485562, 257521586399], ![6333374367559, 251338948622, -433368921882]]]
  hmulB := by decide  
  f := ![![![-670193630984706030746, -134774892826609748788, -58679667974857460065]], ![![-10303773009353845168691, -2072072665037112098215, -902160138688305610109]], ![![-3779642708759770881446, -760080247625629448015, -330931493466662749322]]]
  g := ![![![1485323405, 4981300761, -13843013917], ![-92802260112, -88428200222, 257521586399], ![196183120525, 146208481742, -433368921882]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [57, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 60], [0, 1]]
 g := ![![[15, 15], [48], [60, 4], [57, 25], [60, 1]], ![[0, 46], [48], [56, 57], [32, 36], [59, 60]]]
 h' := ![![[60, 60], [25, 25], [57, 29], [45, 59], [57, 5], [0, 1]], ![[0, 1], [0, 36], [28, 32], [47, 2], [52, 56], [60, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [43, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [57, 1, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![347005, 268227, 153080]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26935, -45793, 153080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![670193630984706030746, 134774892826609748788, 58679667974857460065]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![670193630984706030746, 134774892826609748788, 58679667974857460065]] 
 ![![61, 0, 0], ![26, 1, 0], ![28, 0, 1]] where
  M :=![![![670193630984706030746, 134774892826609748788, 58679667974857460065], ![10303773009353845168691, 2072072665037112098215, 902160138688305610109], ![15770227844467941994688, 3171368197675227630371, 1380782644027168525617]]]
  hmulB := by decide  
  f := ![![![89354453216, -26999068081, 13843013917]], ![![76006115201, -7512906304, 1678635663]], ![![-62810650451, -16513325490, 13458578878]]]
  g := ![![![-73393185013166497042, 134774892826609748788, 58679667974857460065], ![-1128370494506288958491, 2072072665037112098215, 902160138688305610109], ![-1727004251276208116594, 3171368197675227630371, 1380782644027168525617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-89354453216, 26999068081, -13843013917]] ![![670193630984706030746, 134774892826609748788, 58679667974857460065]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [58, 24, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 62, 6], [1, 4, 61], [0, 1]]
 g := ![![[62, 47, 6], [39, 21, 6], [11, 19], [25, 23], [23, 1], []], ![[1, 52, 26, 26], [23, 13, 23, 64], [66, 22], [30, 19], [5, 16], [31, 36]], ![[34, 20, 57, 45], [8, 14, 66, 5], [49, 49], [53, 16], [4, 25], [43, 36]]]
 h' := ![![[22, 62, 6], [16, 52, 41], [14, 19, 41], [60, 59, 35], [6, 60, 36], [0, 0, 1], [0, 1]], ![[1, 4, 61], [15, 32, 7], [24, 63, 10], [57, 18, 25], [51, 43, 35], [26, 30, 4], [22, 62, 6]], ![[0, 1], [30, 50, 19], [62, 52, 16], [31, 57, 7], [31, 31, 63], [53, 37, 62], [1, 4, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 21], []]
 b := ![[], [35, 64, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [58, 24, 44, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51322, -9045, 2010]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-766, -135, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1196721536218, -240658832508, -104780497989]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1196721536218, -240658832508, -104780497989]] 
 ![![71, 0, 0], ![0, 71, 0], ![52, 26, 1]] where
  M :=![![![-1196721536218, -240658832508, -104780497989], ![-18398782821135, -3699966499555, -1610929166097], ![-28159878608232, -5662907622471, -2465574500485]]]
  hmulB := by decide  
  f := ![![![-2411528, -97809, 166389]], ![![28256901, 123658, -1281639]], ![![8055245, -14618, -332776]]]
  g := ![![![59885413510, 34980762186, -104780497989], ![920697659379, 537805518577, -1610929166097], ![1409154865028, 823127174509, -2465574500485]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70], [0, 1]]
 g := ![![[56, 38], [57, 24], [50, 25], [1], [50], [1]], ![[48, 33], [37, 47], [41, 46], [1], [50], [1]]]
 h' := ![![[11, 70], [15, 40], [58, 38], [13, 5], [3, 70], [4, 11], [0, 1]], ![[0, 1], [29, 31], [50, 33], [68, 66], [63, 1], [54, 60], [11, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [12, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5640, 12192, 8552]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6184, -2960, 8552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2411528, 97809, -166389]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2411528, 97809, -166389]] 
 ![![71, 0, 0], ![8, 1, 0], ![7, 0, 1]] where
  M :=![![![2411528, 97809, -166389], ![-28256901, -123658, 1281639], ![37357575, -833082, -1043290]]]
  hmulB := by decide  
  f := ![![![1196721536218, 240658832508, 104780497989]], ![![393979649449, 79228692389, 34495396479]], ![![514604638898, 103486189437, 45056873048]]]
  g := ![![![39349, 97809, -166389], ![-510410, -123658, 1281639], ![722891, -833082, -1043290]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1196721536218, -240658832508, -104780497989]] ![![2411528, 97809, -166389]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-309358704057584, 10883630957247, 6035915979579]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-309358704057584, 10883630957247, 6035915979579]] 
 ![![73, 0, 0], ![0, 73, 0], ![66, 10, 1]] where
  M :=![![![-309358704057584, 10883630957247, 6035915979579], ![1053908894422503, -174097239533000, 68961299719239], ![1112647312221441, 275560465966884, -227327193317324]]]
  hmulB := by decide  
  f := ![![![281836012918017913735589188, 56676782170989741887434368, 24676515706494875745328521]], ![![4333037750152603236226045827, 871367126441400027068477149, 379384710248433307863489381]], ![![939224604900672547111505274, 188876601646624273746873313, 82235021971800632946042523]]]
  g := ![![![-9694919982326, -677746970391, 6035915979579], ![-47911464206127, -11831647078430, 68961299719239], ![220770439331025, 34915512316988, -227327193317324]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [37, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 72], [0, 1]]
 g := ![![[50, 2], [71], [3], [3, 46], [41], [1]], ![[0, 71], [71], [3], [21, 27], [41], [1]]]
 h' := ![![[48, 72], [70, 32], [19, 61], [35, 52], [71, 22], [36, 48], [0, 1]], ![[0, 1], [0, 41], [27, 12], [49, 21], [32, 51], [4, 25], [48, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [63, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [37, 25, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27987, 36825, 21750]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19281, -2475, 21750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281836012918017913735589188, -56676782170989741887434368, -24676515706494875745328521]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-281836012918017913735589188, -56676782170989741887434368, -24676515706494875745328521]] 
 ![![73, 0, 0], ![69, 1, 0], ![18, 0, 1]] where
  M :=![![![-281836012918017913735589188, -56676782170989741887434368, -24676515706494875745328521], ![-4333037750152603236226045827, -871367126441400027068477149, -379384710248433307863489381], ![-6631841803633881270330540324, -1333653032504248748266312071, -580659464828451327234527983]]]
  hmulB := by decide  
  f := ![![![309358704057584, -10883630957247, -6035915979579]], ![![277970434048641, -7902373924891, -6649856196030]], ![![61038484394727, -6458435934210, 1625763091574]]]
  g := ![![![55795058076673726574154734, -56676782170989741887434368, -24676515706494875745328521], ![857811215873641070863584744, -871367126441400027068477149, -379384710248433307863489381], ![1312905312411937071921458853, -1333653032504248748266312071, -580659464828451327234527983]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-309358704057584, 10883630957247, 6035915979579]] ![![-281836012918017913735589188, -56676782170989741887434368, -24676515706494875745328521]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [14, 75, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 34, 63], [7, 44, 16], [0, 1]]
 g := ![![[21, 18, 50], [32, 54, 16], [36, 78, 25], [10, 37, 23], [29, 1], []], ![[31, 73, 75, 15], [57, 31, 45, 29], [44, 62, 46, 6], [65, 51, 36, 15], [8, 40], [16, 19]], ![[52, 18, 32, 38], [78, 74, 5, 51], [4, 55, 71, 13], [56, 10, 59, 72], [42, 50], [63, 19]]]
 h' := ![![[22, 34, 63], [26, 35, 45], [49, 8, 4], [18, 38, 5], [68, 23, 55], [0, 0, 1], [0, 1]], ![[7, 44, 16], [14, 12, 77], [1, 76, 48], [21, 20, 7], [22, 62, 77], [23, 30, 44], [22, 34, 63]], ![[0, 1], [74, 32, 36], [12, 74, 27], [69, 21, 67], [76, 73, 26], [36, 49, 34], [7, 44, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 23], []]
 b := ![[], [65, 35, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [14, 75, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7198480, -1334152, -535462]
  a := ![-2, -8, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91120, -16888, -6778]
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



lemma PB219I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB219I1 : PrimesBelowBoundCertificateInterval O 31 79 219 where
  m := 11
  g := ![2, 2, 3, 2, 2, 2, 2, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB219I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I37N1, I41N1, I43N0, I43N1, I47N1, I53N1, I59N1, I61N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N0, I43N1], [I47N1], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
