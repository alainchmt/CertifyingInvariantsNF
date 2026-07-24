
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60291279980506213337752049278002, 6640774898065306199740679084776, 3283528121064660750793895859113]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![60291279980506213337752049278002, 6640774898065306199740679084776, 3283528121064660750793895859113]] 
 ![![37, 0, 0], ![22, 1, 0], ![5, 0, 1]] where
  M :=![![![60291279980506213337752049278002, 6640774898065306199740679084776, 3283528121064660750793895859113], ![489098252726762482471984708274737, 53871661050248861232470032292876, 26636818248197209497115603705654], ![622015184876232558465056396877168, 68511778606741967577754488842073, 33875617700116957935095107671998]]]
  hmulB := by decide  
  f := ![![![-23921915903094494, 4807062271558801, -1461126433055484]], ![![-20525638342396906, 2708495600341882, -140195062251775]], ![![21383949189180599, -1433087420605129, -945869375115340]]]
  g := ![![![-2762794821141995319203037023855, 6640774898065306199740679084776, 3283528121064660750793895859113], ![-22412496800532392219673892451265, 53871661050248861232470032292876, 26636818248197209497115603705654], ![-28503298188450689673541024216444, 68511778606741967577754488842073, 33875617700116957935095107671998]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117279113680675713408176, -12917692151332555113598, -6387146995528168513121]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-117279113680675713408176, -12917692151332555113598, -6387146995528168513121]] 
 ![![37, 0, 0], ![30, 1, 0], ![0, 0, 1]] where
  M :=![![![-117279113680675713408176, -12917692151332555113598, -6387146995528168513121], ![-951398106013144672280317, -104791616010171812556646, -51814166765606438541748], ![-1209949259690500710805974, -133269697944434230251405, -65895141395897929128496]]]
  hmulB := by decide  
  f := ![![![-1896784628476, 203547703603, 23801262862]], ![![-1450514622800, 120917143504, 45518212923]], ![![764503975887, -11779582356, -64840137490]]]
  g := ![![![7304098671872998378372, -12917692151332555113598, -6387146995528168513121], ![59252712818702964984299, -104791616010171812556646, -51814166765606438541748], ![75355180503852059371248, -133269697944434230251405, -65895141395897929128496]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![60291279980506213337752049278002, 6640774898065306199740679084776, 3283528121064660750793895859113]] ![![60291279980506213337752049278002, 6640774898065306199740679084776, 3283528121064660750793895859113]]
  ![![8925434192353618274260897003053379206506054830866549464297647900, 983090744765741566797351022442673700177877177475125250329614577, 486088770594700673937619505444976192561805546010078317601873504]] where
 M := ![![![8925434192353618274260897003053379206506054830866549464297647900, 983090744765741566797351022442673700177877177475125250329614577, 486088770594700673937619505444976192561805546010078317601873504]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![8925434192353618274260897003053379206506054830866549464297647900, 983090744765741566797351022442673700177877177475125250329614577, 486088770594700673937619505444976192561805546010078317601873504]] ![![-117279113680675713408176, -12917692151332555113598, -6387146995528168513121]]
  ![![37, 0, 0]] where
 M := ![![![-2570220432028532077270231892784687068301964546435498047538840117179412994785379978124205, -283096582673784115296437050414743638168481427115370787490221755205173079591691794246062, -139976976249788159175722362995933524965402592681912880174913573113534480843478905726480]]]
 hmul := by decide  
 g := ![![![![-69465417081852218304600861967153704548701744498256703987536219383227378237442702111465, -7651258991183354467471271632830909139688687219334345607843831221761434583559237682326, -3783161520264544842587090891781987161227097099511158923646312786852283266039970425040]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23588224586750549985172564, 2598121814236937172421717, 1284640146661785388483846]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![23588224586750549985172564, 2598121814236937172421717, 1284640146661785388483846]] 
 ![![41, 0, 0], ![17, 1, 0], ![17, 0, 1]] where
  M :=![![![23588224586750549985172564, 2598121814236937172421717, 1284640146661785388483846], ![191353698810779290093185004, 21076627335253711999112922, 10421328777861115085140893], ![243355819978837140762461181, 26804393954417294785436616, 13253420371629534086393746]]]
  hmulB := by decide  
  f := ![![![-16294872552276, -316650476746, 1828431115269]], ![![82205565877, -811751665904, 630322301105]], ![![-13289563174710, 1386709062431, 197756899993]]]
  g := ![![![-1034603140207993501224927, 2598121814236937172421717, 1284640146661785388483846], ![-8392964758833482203393411, 21076627335253711999112922, 10421328777861115085140893], ![-10673829843023389025820853, 26804393954417294785436616, 13253420371629534086393746]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1107378, 121972, 60309]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1107378, 121972, 60309]] 
 ![![41, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![1107378, 121972, 60309], ![8983333, 989468, 489242], ![11424636, 1258365, 622198]]]
  hmulB := by decide  
  f := ![![![1334, 329, -388]], ![![-618, 314, -187]], ![![2949, -216, -116]]]
  g := ![![![-76816, 121972, 60309], ![-623151, 989468, 489242], ![-792498, 1258365, 622198]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4254588407481281, -823158491480166, 234866933436594]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![4254588407481281, -823158491480166, 234866933436594]] 
 ![![41, 0, 0], ![39, 1, 0], ![16, 0, 1]] where
  M :=![![![4254588407481281, -823158491480166, 234866933436594], ![37580957798759214, 1199069823901385, -4585526324274018], ![-154127281208856678, 12689559752288598, 4961437656695237]]]
  hmulB := by decide  
  f := ![![![64137420464878711234969656250009, 7064407522738589403292714324554, 3492993079215916080309589844298]], ![![73698988395239700479136546616557, 8117565132240619031417400109535, 4013726379138581511900448679556]], ![![41168144119784234849418268544906, 4534459679061246943491307514814, 2242061521219329887612178188597]]]
  g := ![![![795119479029811, -823158491480166, 234866933436594], ![1565503801341207, 1199069823901385, -4585526324274018], ![-17765929611103312, 12689559752288598, 4961437656695237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![23588224586750549985172564, 2598121814236937172421717, 1284640146661785388483846]] ![![1107378, 121972, 60309]]
  ![![64137420464878711234969656250009, 7064407522738589403292714324554, 3492993079215916080309589844298]] where
 M := ![![![64137420464878711234969656250009, 7064407522738589403292714324554, 3492993079215916080309589844298]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![64137420464878711234969656250009, 7064407522738589403292714324554, 3492993079215916080309589844298]] ![![4254588407481281, -823158491480166, 234866933436594]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [7, 34, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 29, 4], [11, 13, 39], [0, 1]]
 g := ![![[12, 38, 13], [29, 21, 10], [37, 41], [6, 13, 1], []], ![[15, 17, 12, 25], [42, 37, 8, 36], [7, 31], [36, 1, 30, 31], [10, 16]], ![[22, 30, 19, 22], [2, 28, 36, 26], [42, 14], [35, 40, 17, 33], [18, 16]]]
 h' := ![![[2, 29, 4], [12, 28, 23], [0, 15, 15], [1, 6, 16], [0, 0, 1], [0, 1]], ![[11, 13, 39], [12, 7, 24], [29, 39, 40], [32, 1, 17], [20, 8, 13], [2, 29, 4]], ![[0, 1], [33, 8, 39], [4, 32, 31], [30, 36, 10], [38, 35, 29], [11, 13, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 27], []]
 b := ![[], [23, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [7, 34, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-462637, 51471, -19135]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10759, 1197, -445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92835924068585, 10225400329744, 5055944531660]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![92835924068585, 10225400329744, 5055944531660]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 25, 1]] where
  M :=![![![92835924068585, 10225400329744, 5055944531660], ![753108712684492, 82951057538113, 41015112585400], ![957772906651632, 105493767566316, 52161345282457]]]
  hmulB := by decide  
  f := ![![![6689303, -147584, -532340]], ![![-81152852, 9588175, 326760]], ![![-39014189, 4672941, 107213]]]
  g := ![![![-498953194885, -2471770488548, 5055944531660], ![-4047635676164, -20051633129721, 41015112585400], ![-5147617762657, -25500848180747, 52161345282457]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[24, 6], [42, 34], [19, 7], [0, 16], [1]], ![[0, 41], [0, 13], [38, 40], [30, 31], [1]]]
 h' := ![![[43, 46], [40, 10], [36, 9], [0, 30], [39, 43], [0, 1]], ![[0, 1], [0, 37], [0, 38], [21, 17], [8, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [12, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9931, 4460, -724]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![143, 480, -724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6689303, 147584, 532340]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-6689303, 147584, 532340]] 
 ![![47, 0, 0], ![18, 1, 0], ![31, 0, 1]] where
  M :=![![![-6689303, 147584, 532340], ![81152852, -9588175, -326760], ![-41300448, 16681716, -9113831]]]
  hmulB := by decide  
  f := ![![![-92835924068585, -10225400329744, -5055944531660]], ![![-51577773317426, -5681026882415, -2808981152240]], ![![-81610352186761, -8988961229540, -4444587782211]]]
  g := ![![![-549965, 147584, 532340], ![5614246, -9588175, -326760], ![-1256225, 16681716, -9113831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![92835924068585, 10225400329744, 5055944531660]] ![![-6689303, 147584, 532340]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172117607529259331261, -18957870656667468340, -9373710503996974538]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-172117607529259331261, -18957870656667468340, -9373710503996974538]] 
 ![![53, 0, 0], ![0, 53, 0], ![45, 48, 1]] where
  M :=![![![-172117607529259331261, -18957870656667468340, -9373710503996974538], ![-1396261965798202167634, -153791085818612420713, -76041932275343392624], ![-1775708949990485711460, -195585222691895349714, -96707024199936496429]]]
  hmulB := by decide  
  f := ![![![-11284566497, 630508976, 598024178]], ![![90236681282, -13611693613, 1956496524]], ![![72608682663, -11491257462, 1997834717]]]
  g := ![![![4711308776426500433, 8131702519531836028, -9373710503996974538], ![38219339369665103782, 65966446479205102363, -76041932275343392624], ![48605795075597294865, 83893432809529367526, -96707024199936496429]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 52], [0, 1]]
 g := ![![[30, 46], [6], [35, 24], [42], [27, 1]], ![[0, 7], [6], [47, 29], [42], [1, 52]]]
 h' := ![![[27, 52], [41, 24], [5, 18], [49, 17], [19, 25], [0, 1]], ![[0, 1], [0, 29], [14, 35], [31, 36], [5, 28], [27, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [49, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 26, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3092103, 988641, -204809]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![232236, 204141, -204809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11284566497, -630508976, -598024178]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![11284566497, -630508976, -598024178]] 
 ![![53, 0, 0], ![27, 1, 0], ![2, 0, 1]] where
  M :=![![![11284566497, -630508976, -598024178], ![-90236681282, 13611693613, -1956496524], ![-24704971968, -15951744018, 14937681161]]]
  hmulB := by decide  
  f := ![![![172117607529259331261, 18957870656667468340, 9373710503996974538]], ![![114027120171475549277, 12559501765068567281, 6210039922325692550]], ![![39998946510358573094, 4405678566136420498, 2178385758640197085]]]
  g := ![![![556685985, -630508976, -598024178], ![-8563007845, 13611693613, -1956496524], ![7096542532, -15951744018, 14937681161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-172117607529259331261, -18957870656667468340, -9373710503996974538]] ![![11284566497, -630508976, -598024178]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [12, 9, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 51, 44], [27, 7, 15], [0, 1]]
 g := ![![[50, 41, 17], [35, 24, 17], [58, 9], [48, 5, 53], [1]], ![[57, 9, 46, 37], [48, 38, 56, 43], [25, 49], [6, 54, 29, 37], [50, 53, 1, 47]], ![[21, 8, 14, 57], [38, 30, 10, 41], [10, 16], [44, 9, 40, 26], [2, 39, 32, 12]]]
 h' := ![![[49, 51, 44], [52, 4, 28], [31, 10, 31], [14, 6, 56], [47, 50, 17], [0, 1]], ![[27, 7, 15], [49, 39, 18], [12, 26, 8], [28, 35, 7], [52, 54, 18], [49, 51, 44]], ![[0, 1], [41, 16, 13], [7, 23, 20], [56, 18, 55], [12, 14, 24], [27, 7, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 58], []]
 b := ![[], [10, 49, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [12, 9, 42, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8957557, 806058, 33453]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151823, 13662, 567]
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

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39376812254338084388722068, 4337153672454561269763698, 2144503656197167075341477]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![39376812254338084388722068, 4337153672454561269763698, 2144503656197167075341477]] 
 ![![61, 0, 0], ![0, 61, 0], ![42, 25, 1]] where
  M :=![![![39376812254338084388722068, 4337153672454561269763698, 2144503656197167075341477], ![319434752053257439987718585, 35184097662064204476200602, 17396761049878472198135536], ![406244073141887825232868554, 44745698619779145867686553, 22124490284640293547828764]]]
  hmulB := by decide  
  f := ![![![3169720509320, 79856207369, -370029613066]], ![![-56774243213836, 5549610602454, 1139340262977]], ![![-20157479764903, 2121378873696, 285776874959]]]
  g := ![![![-831021988622015291403606, -807794061188108452684807, 2144503656197167075341477], ![-6741462492485875284163507, -6553031616145862302904718, 17396761049878472198135536], ![-8573516701852532848785894, -8333878008134888407016927, 22124490284640293547828764]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [25, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 60], [0, 1]]
 g := ![![[42, 22], [4], [14, 5], [17, 57], [48, 1]], ![[0, 39], [4], [10, 56], [8, 4], [35, 60]]]
 h' := ![![[48, 60], [34, 12], [16, 2], [2, 35], [20, 22], [0, 1]], ![[0, 1], [0, 49], [51, 59], [35, 26], [39, 39], [48, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [6, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [25, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47561, 1123, 1709]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-397, -682, 1709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3169720509320, 79856207369, -370029613066]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![3169720509320, 79856207369, -370029613066]] 
 ![![61, 0, 0], ![60, 1, 0], ![12, 0, 1]] where
  M :=![![![3169720509320, 79856207369, -370029613066], ![-56774243213836, 5549610602454, 1139340262977], ![56621553295377, -12690114475392, 4490126546846]]]
  hmulB := by decide  
  f := ![![![39376812254338084388722068, 4337153672454561269763698, 2144503656197167075341477]], ![![43967926021533483660836765, 4842841278841604601016762, 2394540662650958962600396]], ![![14405997052359751440943170, 1586746601462850509915589, 784566133754201613966008]]]
  g := ![![![46208252852, 79856207369, -370029613066], ![-6613491188800, 5549610602454, 1139340262977], ![12526998414045, -12690114475392, 4490126546846]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![39376812254338084388722068, 4337153672454561269763698, 2144503656197167075341477]] ![![3169720509320, 79856207369, -370029613066]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1375264013, 291324562, -95769216]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-1375264013, 291324562, -95769216]] 
 ![![67, 0, 0], ![9, 1, 0], ![20, 0, 1]] where
  M :=![![![-1375264013, 291324562, -95769216], ![-15235339172, -217999593, 1648161242], ![56064963906, -4908331500, -1574836273]]]
  hmulB := by decide  
  f := ![![![8433035407743359889, 928855547076541426, 459272201821096916]], ![![2153854544092014691, 237236018129234837, 117301241016871426]], ![![3815864815508155314, 420297915211459376, 207816112578027279]]]
  g := ![![![-31071653, 291324562, -95769216], ![-690098025, -217999593, 1648161242], ![1966218998, -4908331500, -1574836273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327446219350064516972, -105034250111336682786, 50850714396660912777]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![327446219350064516972, -105034250111336682786, 50850714396660912777]] 
 ![![67, 0, 0], ![15, 1, 0], ![29, 0, 1]] where
  M :=![![![327446219350064516972, -105034250111336682786, 50850714396660912777], ![7990227802911793020453, -187726567252574325262, -626872679350005239484], ![-22172325994633821999498, 2308279075757830218357, 334111861986094231436]]]
  hmulB := by decide  
  f := ![![![-1384275415978849405005981134823555628671556, -152470828906161667249572492704975242508085, -75389131846838426769813699045327879994998]], ![![-477518309767711896065254746132515665437192, -52596189795560704292982556963226380169239, -26006162067756834093364784344987144066797]], ![![-812318329319533680925080603109029548295707, -89472692772946066121552528368809710709267, -44239732154290846861972815306668688709408]]]
  g := ![![![6392376918163407287, -105034250111336682786, 50850714396660912777], ![432618418102247161857, -187726567252574325262, -626872679350005239484], ![-992324718337283701291, 2308279075757830218357, 334111861986094231436]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62667414226800, 5307267627617, 1901116439170]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-62667414226800, 5307267627617, 1901116439170]] 
 ![![67, 0, 0], ![43, 1, 0], ![28, 0, 1]] where
  M :=![![![-62667414226800, 5307267627617, 1901116439170], ![280256279937776, -63459577606586, 22734105259745], ![583877974325001, 30893236726908, -80886415238714]]]
  hmulB := by decide  
  f := ![![![-4430687649595964966997851944, -488017493311108410198150898, -241300027098547055180751285]], ![![-3380036389434059346315914603, -372293652029918822310897532, -184080426531283153931366525]], ![![-2533879513633745659918907278, -279093817120842355900359883, -137997810646848917476710164]]]
  g := ![![![-5135987798673, 5307267627617, 1901116439170], ![35409898055942, -63459577606586, 22734105259745], ![22690871966447, 30893236726908, -80886415238714]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-1375264013, 291324562, -95769216]] ![![327446219350064516972, -105034250111336682786, 50850714396660912777]]
  ![![4000850890700953786873783791518, -131301613064589181390174003138, -284554197365183929243069674285]] where
 M := ![![![4000850890700953786873783791518, -131301613064589181390174003138, -284554197365183929243069674285]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![4000850890700953786873783791518, -131301613064589181390174003138, -284554197365183929243069674285]] ![![-62667414226800, 5307267627617, 1901116439170]]
  ![![67, 0, 0]] where
 M := ![![![-453666009997789584742872908072156963639322773, 20775131138444107955009813666145236625458694, 27637627672794084933492322285616266376149740]]]
 hmul := by decide  
 g := ![![![![-6771134477578949026013028478688909905064519, 310076584155882208283728562181272188439682, 412501905564090819902870481874869647405220]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11656, 1344, 73]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-11656, 1344, 73]] 
 ![![71, 0, 0], ![0, 71, 0], ![65, 33, 1]] where
  M :=![![![-11656, 1344, 73], ![8481, -9406, 6574], ![196872, -5655, -14636]]]
  hmulB := by decide  
  f := ![![![2462566, 271239, 134114]], ![![19976964, 2200360, 1087967]], ![![11897359, 1310433, 647943]]]
  g := ![![![-231, -15, 73], ![-5899, -3188, 6574], ![16172, 6723, -14636]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 70], [0, 1]]
 g := ![![[31, 37], [12, 58], [22, 60], [64], [16], [1]], ![[25, 34], [64, 13], [66, 11], [64], [16], [1]]]
 h' := ![![[67, 70], [58, 45], [59, 49], [42, 42], [8, 63], [64, 67], [0, 1]], ![[0, 1], [20, 26], [5, 22], [16, 29], [40, 8], [9, 4], [67, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [24, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [7, 4, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5206, 2008, -363]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![259, 197, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2462566, 271239, 134114]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2462566, 271239, 134114]] 
 ![![71, 0, 0], ![50, 1, 0], ![5, 0, 1]] where
  M :=![![![2462566, 271239, 134114], ![19976964, 2200360, 1087967], ![25405887, 2798328, 1383632]]]
  hmulB := by decide  
  f := ![![![-11656, 1344, 73]], ![![-8089, 814, 144]], ![![1952, 15, -201]]]
  g := ![![![-165774, 271239, 134114], ![-1344801, 2200360, 1087967], ![-1710263, 2798328, 1383632]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-11656, 1344, 73]] ![![2462566, 271239, 134114]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4879237056, 225291307, 295789986]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-4879237056, 225291307, 295789986]] 
 ![![73, 0, 0], ![0, 73, 0], ![62, 54, 1]] where
  M :=![![![-4879237056, 225291307, 295789986], ![44805285244, -6203394358, 534876563], ![-1025228349, 8409321696, -6512979614]]]
  hmulB := by decide  
  f := ![![![-491844272675874068, -54174121047010298, -26786369455715573]], ![![-3989966284630462073, -439474298035601226, -217297866323620344]], ![![-3438723293992545904, -378757713213611737, -187276578636833634]]]
  g := ![![![-318057756, -215717369, 295789986], ![159492306, -480640120, 534876563], ![5517527503, 4933016724, -6512979614]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [25, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 72], [0, 1]]
 g := ![![[35, 38], [69], [41], [30, 65], [1], [1]], ![[0, 35], [69], [41], [22, 8], [1], [1]]]
 h' := ![![[1, 72], [29, 44], [32, 19], [53, 48], [16, 24], [48, 1], [0, 1]], ![[0, 1], [0, 29], [51, 54], [28, 25], [40, 49], [49, 72], [1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [14, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [25, 72, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3003, 3070, 165]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99, -80, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-491844272675874068, -54174121047010298, -26786369455715573]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-491844272675874068, -54174121047010298, -26786369455715573]] 
 ![![73, 0, 0], ![24, 1, 0], ![50, 0, 1]] where
  M :=![![![-491844272675874068, -54174121047010298, -26786369455715573], ![-3989966284630462073, -439474298035601226, -217297866323620344], ![-5074276185506706834, -558905465756552121, -276350552758991180]]]
  hmulB := by decide  
  f := ![![![-4879237056, 225291307, 295789986]], ![![-990361700, -10909630, 104573099]], ![![-3355987413, 269505302, 113376982]]]
  g := ![![![29419905551207558, -54174121047010298, -26786369455715573], ![238661783348013487, -439474298035601226, -217297866323620344], ![303520310008220590, -558905465756552121, -276350552758991180]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-4879237056, 225291307, 295789986]] ![![-491844272675874068, -54174121047010298, -26786369455715573]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![891327561349179888, -1406306656746852287, 1019400915724306292]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![891327561349179888, -1406306656746852287, 1019400915724306292]] 
 ![![79, 0, 0], ![0, 79, 0], ![37, 16, 1]] where
  M :=![![![891327561349179888, -1406306656746852287, 1019400915724306292], ![158780953419312567250, -8037691246490362438, -9070335115182874019], ![-337493028369185154951, 42078070159383221358, -373662788054340706]]]
  hmulB := by decide  
  f := ![![![4869184600841339532756375061797226570, 536315680837562723130211808433859366, 265181043903644547667405462652239131]], ![![39500068355582490346852612168924868311, 4350729699094597693012365902751510516, 2151216316380524520316248116864818568]], ![![10916398706584293154183055989384899536, 1202385262535421235167832921177186075, 594518844937656664361775969396082231]]]
  g := ![![![-466158307853799404, -224262295042224721, 1019400915724306292], ![6258017122545302607, 1735286969575134454, -9070335115182874019], ![-4097057027989551251, 608312338838641426, -373662788054340706]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [78, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 78], [0, 1]]
 g := ![![[7, 11], [52, 19], [5, 42], [67, 22], [49], [1]], ![[5, 68], [27, 60], [62, 37], [63, 57], [49], [1]]]
 h' := ![![[7, 78], [52, 13], [5, 63], [67, 68], [50, 41], [1, 7], [0, 1]], ![[0, 1], [64, 66], [51, 16], [69, 11], [21, 38], [50, 72], [7, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [21, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [78, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19163, 5005, -2230]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1287, 515, -2230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4869184600841339532756375061797226570, 536315680837562723130211808433859366, 265181043903644547667405462652239131]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![4869184600841339532756375061797226570, 536315680837562723130211808433859366, 265181043903644547667405462652239131]] 
 ![![79, 0, 0], ![1, 1, 0], ![78, 0, 1]] where
  M :=![![![4869184600841339532756375061797226570, 536315680837562723130211808433859366, 265181043903644547667405462652239131], ![39500068355582490346852612168924868311, 4350729699094597693012365902751510516, 2151216316380524520316248116864818568], ![50234573899709750918833751172111787278, 5533080363794893734243109416920735127, 2735829063551635895826329594320551314]]]
  hmulB := by decide  
  f := ![![![891327561349179888, -1406306656746852287, 1019400915724306292]], ![![2021168113679262622, -119544277256167275, -101910559486817313]], ![![-3392018716252520553, -855871507175585532, 1001767197954956330]]]
  g := ![![![-206977879803550606435841301690016266, 536315680837562723130211808433859366, 265181043903644547667405462652239131], ![-1679057392673329366213001352522563171, 4350729699094597693012365902751510516, 2151216316380524520316248116864818568], ![-2135356625583705603669152741795087979, 5533080363794893734243109416920735127, 2735829063551635895826329594320551314]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![891327561349179888, -1406306656746852287, 1019400915724306292]] ![![4869184600841339532756375061797226570, 536315680837562723130211808433859366, 265181043903644547667405462652239131]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB225I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB225I1 : PrimesBelowBoundCertificateInterval O 31 79 225 where
  m := 11
  g := ![3, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB225I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N1
  β := ![I37N0, I37N1, I41N0, I41N1, I41N2, I47N1, I53N1, I61N1, I67N0, I67N1, I67N2, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [I41N0, I41N1, I41N2], [], [I47N1], [I53N1], [], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
