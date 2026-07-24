
import IdealArithmetic.Examples.NF3_1_439803_1.RI3_1_439803_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28738367687962187554921710805285, 396227192900468141381375800822, 1284185052638251370712617993294]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![28738367687962187554921710805285, 396227192900468141381375800822, 1284185052638251370712617993294]] 
 ![![139, 0, 0], ![0, 139, 0], ![39, 62, 1]] where
  M :=![![![28738367687962187554921710805285, 396227192900468141381375800822, 1284185052638251370712617993294], ![99674703438946291827634337085282, 1374254389658440628575357145289, 4454002595841996501763624399870], ![48488084590271566076342588569410, 668524317557928625979434135796, 2166708775459376911338108746933]]]
  hmulB := by decide  
  f := ![![![-237912235759697, -49186382719618, 242118192928066]], ![![18544728090021846, -5273207904529465, -151372868828878]], ![![8202135738261213, -2346254803016428, -38230856209817]]]
  g := ![![![-153560067373594359013456049879, -569951410580367747070510358154, 1284185052638251370712617993294], ![-532599984164687566483072046832, -1976790694622628363171002558609, 4454002595841996501763624399870], ![-259090342824777938603191745043, -961636113387938416381174878950, 2166708775459376911338108746933]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [114, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 138], [0, 1]]
 g := ![![[44, 9], [62, 29], [6], [13, 64], [113], [5], [1]], ![[75, 130], [131, 110], [6], [79, 75], [113], [5], [1]]]
 h' := ![![[127, 138], [21, 136], [135, 53], [47, 59], [12, 131], [55, 35], [25, 127], [0, 1]], ![[0, 1], [57, 3], [55, 86], [34, 80], [108, 8], [52, 104], [30, 12], [127, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [123, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [114, 12, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257, 1517, -3112]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![875, 1399, -3112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-237912235759697, -49186382719618, 242118192928066]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-237912235759697, -49186382719618, 242118192928066]] 
 ![![139, 0, 0], ![59, 1, 0], ![59, 0, 1]] where
  M :=![![![-237912235759697, -49186382719618, 242118192928066], ![18544728090021846, -5273207904529465, -151372868828878], ![-397696768417662, 2727741387608440, -5371580669968701]]]
  hmulB := by decide  
  f := ![![![28738367687962187554921710805285, 396227192900468141381375800822, 1284185052638251370712617993294]], ![![12915384151285721996892196220123, 178069487559611949425011002833, 577128925910063506286389107944]], ![![12547135094820436200120313137275, 172992292796298913435112276146, 560673574684289264628651585261]]]
  g := ![![![-83603518259411, -49186382719618, 242118192928066], ![2435935206605497, -5273207904529465, -151372868828878], ![1119344035185883, 2727741387608440, -5371580669968701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![28738367687962187554921710805285, 396227192900468141381375800822, 1284185052638251370712617993294]] ![![-237912235759697, -49186382719618, 242118192928066]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [106, 1, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 28, 33], [119, 120, 116], [0, 1]]
 g := ![![[9, 46, 1], [31, 26], [18, 16, 143], [137, 130], [25, 135, 127], [59, 1], []], ![[98, 9, 92, 88], [], [3, 13, 52, 33], [112, 47], [96, 18, 41, 100], [117, 96], [92, 46]], ![[99, 76, 109, 7], [52, 26], [95, 43, 17, 120], [90, 30], [28, 117, 109, 29], [64, 39], [9, 46]]]
 h' := ![![[89, 28, 33], [88, 81, 148], [29, 70, 18], [61, 23, 21], [32, 134, 117], [4, 133, 53], [0, 0, 1], [0, 1]], ![[119, 120, 116], [39, 17, 20], [121, 13], [13, 86, 1], [73, 111, 135], [26, 102, 21], [106, 16, 120], [89, 28, 33]], ![[0, 1], [96, 51, 130], [86, 66, 131], [25, 40, 127], [124, 53, 46], [6, 63, 75], [95, 133, 28], [119, 120, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 12], []]
 b := ![[], [145, 8, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [106, 1, 90, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2614503, -1019160, 558601]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17547, -6840, 3749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163914778080924373326, -271803638047638491070, 461583583743689913227]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![163914778080924373326, -271803638047638491070, 461583583743689913227]] 
 ![![151, 0, 0], ![0, 151, 0], ![18, 27, 1]] where
  M :=![![![163914778080924373326, -271803638047638491070, 461583583743689913227], ![34998328672168846336339, -9257536842488925313371, -1712845520637418015333], ![-14466709957256505027212, 8938961485206237705059, -9801144118584202295511]]]
  hmulB := by decide  
  f := ![![![702288165002800017931462542862750421293028, 9682723502171595200705662240766152677673, 31382017723961147195926839348262655737977]], ![![2435780811749351524487777954297756797179575, 33583069297444331616293254308468498117838, 108843805741333908801572137274391877159361]], ![![527100575133016956126712862787970940686328, 7267343209219935088803236788372116432546, 23553692651318567610508843665346419139467]]]
  g := ![![![-53937680326526450760, -84334837080313020849, 461583583743689913227], ![435957271812201129883, 244962200097492457620, -1712845520637418015333], ![1072542279319596929086, 1811720878721719865456, -9801144118584202295511]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [123, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 150], [0, 1]]
 g := ![![[2, 124], [88, 20], [69, 50], [9], [126, 118], [116], [1]], ![[0, 27], [0, 131], [0, 101], [9], [90, 33], [116], [1]]]
 h' := ![![[56, 150], [48, 107], [120, 41], [106, 79], [55, 3], [106, 119], [28, 56], [0, 1]], ![[0, 1], [0, 44], [0, 110], [0, 72], [72, 148], [126, 32], [144, 95], [56, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [138, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [123, 95, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![505815, 277108, -800260]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98745, 144928, -800260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-236199884941637876138566, 82130146687022359025279, -28837989475862013955457]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-236199884941637876138566, 82130146687022359025279, -28837989475862013955457]] 
 ![![151, 0, 0], ![85, 1, 0], ![127, 0, 1]] where
  M :=![![![-236199884941637876138566, 82130146687022359025279, -28837989475862013955457], ![-2056264896267330356519631, 287267747364442057900752, 628203184020316858246775], ![5920289442238653449570085, -1926599006758503637219058, 451528040738486775951310]]]
  hmulB := by decide  
  f := ![![![-1340005073510897063578738480508201840010861423070, -18475177661952210545099994632242599000600334016, -59878643928093491829068546603997670751300028889]], ![![-785086338981545388716034761066022928786586250685, -10824294533939863714945023516110126293271449495, -35081886086832172063978112351004903818653014282]], ![![-1141996914111573219682645339494571398642012098368, -15745161189825091129695889120832444962402222569, -51030572897687148397384797451418526746021621320]]]
  g := ![![![-23541971456318295502942, 82130146687022359025279, -28837989475862013955457], ![-703680978760431432287576, 287267747364442057900752, 628203184020316858246775], ![743954594986249285214395, -1926599006758503637219058, 451528040738486775951310]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![163914778080924373326, -271803638047638491070, 461583583743689913227]] ![![-236199884941637876138566, 82130146687022359025279, -28837989475862013955457]]
  ![![151, 0, 0]] where
 M := ![![![3252892045420610667181096581851147029487918949, -953904548036071801828227286445099645441656852, 32943047709769347119327723906097653380238138]]]
 hmul := by decide  
 g := ![![![![21542331426626560709808586634775808142304099, -6317248662490541733961770108907944671799052, 218165878872644682909455125205944724372438]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [112, 141, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 51, 61], [54, 105, 96], [0, 1]]
 g := ![![[140, 45, 153], [14, 10], [33, 31, 154], [96, 52, 51], [89, 43, 9], [74, 1], []], ![[39, 10, 62, 78], [71, 67], [128, 62, 107, 29], [78, 138, 114, 74], [32, 3, 110, 133], [43, 35], [75, 110]], ![[68, 118, 152, 80], [95, 124], [104, 79, 150, 78], [95, 141, 147, 43], [67, 141, 108, 129], [9, 89], [40, 110]]]
 h' := ![![[20, 51, 61], [5, 125, 56], [72, 6, 18], [81, 71, 25], [80, 52, 88], [33, 130, 154], [0, 0, 1], [0, 1]], ![[54, 105, 96], [71, 138, 3], [4, 146, 58], [106, 32, 48], [9, 73, 9], [100, 115, 79], [7, 26, 105], [20, 51, 61]], ![[0, 1], [26, 51, 98], [33, 5, 81], [140, 54, 84], [119, 32, 60], [127, 69, 81], [6, 131, 51], [54, 105, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 95], []]
 b := ![[], [105, 17, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [112, 141, 83, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5640853, 2863523, -2527072]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35929, 18239, -16096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [97, 95, 157, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 20, 2], [50, 142, 161], [0, 1]]
 g := ![![[108, 125, 113], [138, 161, 69], [75, 81], [155, 69], [145, 56], [104, 6, 1], []], ![[22, 26, 107, 17], [130, 17, 61, 129], [53, 65], [46, 74], [72, 132], [44, 39, 9, 67], [104, 4]], ![[68, 100, 117, 51], [83, 4, 48, 21], [157, 160], [147, 150], [51, 62], [59, 134, 115, 15], [108, 4]]]
 h' := ![![[119, 20, 2], [143, 138, 73], [103, 1, 118], [80, 113, 9], [114, 88, 118], [18, 133, 120], [0, 0, 1], [0, 1]], ![[50, 142, 161], [119, 26, 47], [149, 120, 132], [143, 121, 37], [81, 67, 143], [120, 57, 28], [161, 34, 142], [119, 20, 2]], ![[0, 1], [22, 162, 43], [147, 42, 76], [124, 92, 117], [107, 8, 65], [1, 136, 15], [11, 129, 20], [50, 142, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 34], []]
 b := ![[], [80, 121, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [97, 95, 157, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1090144, 921439, -1217284]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6688, 5653, -7468]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [89, 37, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 32, 150], [120, 134, 17], [0, 1]]
 g := ![![[158, 38, 108], [26, 70, 38], [109, 65, 77], [24, 77], [4, 2], [11, 86, 1], []], ![[79, 41, 158, 100], [10, 14, 36, 48], [104, 41, 53, 29], [58, 18], [165, 4], [63, 127, 128, 24], [52, 122]], ![[20, 162, 3, 46], [42, 118, 81, 90], [77, 108, 14, 80], [94, 132], [41, 58], [37, 124, 29, 40], [18, 122]]]
 h' := ![![[133, 32, 150], [24, 47, 129], [152, 66, 120], [71, 80, 54], [6, 109, 54], [23, 122, 13], [0, 0, 1], [0, 1]], ![[120, 134, 17], [102, 104, 121], [104, 64, 95], [76, 102, 31], [27, 28, 39], [4, 164, 2], [35, 72, 134], [133, 32, 150]], ![[0, 1], [133, 16, 84], [84, 37, 119], [31, 152, 82], [106, 30, 74], [9, 48, 152], [106, 95, 32], [120, 134, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 151], []]
 b := ![[], [29, 141, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [89, 37, 81, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211399622, -195431917, 280439760]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1265866, -1170251, 1679280]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [165, 50, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 118, 149], [59, 54, 24], [0, 1]]
 g := ![![[9, 157, 23], [168, 152], [122], [118, 61, 138], [71, 144], [157, 131, 1], []], ![[81, 44, 65, 52], [132, 40], [58, 38, 117, 49], [63, 119, 103, 119], [116, 73], [167, 46, 96, 81], [73, 57]], ![[49, 11, 124, 84], [64, 9], [91, 26, 127, 124], [49, 86, 107, 52], [131, 47], [153, 167, 149, 113], [25, 57]]]
 h' := ![![[72, 118, 149], [171, 71, 14], [111, 141, 49], [79, 128], [171, 91, 151], [45, 118, 12], [0, 0, 1], [0, 1]], ![[59, 54, 24], [54, 5, 90], [6, 48, 127], [126, 53, 42], [62, 71, 88], [80, 99, 65], [59, 131, 54], [72, 118, 149]], ![[0, 1], [15, 97, 69], [56, 157, 170], [19, 165, 131], [159, 11, 107], [144, 129, 96], [48, 42, 118], [59, 54, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 121], []]
 b := ![[], [56, 151, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [165, 50, 42, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3460, -346, -346]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, -2, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀


def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![810259, -277068, 89324]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![810259, -277068, 89324]] 
 ![![179, 0, 0], ![53, 1, 0], ![148, 0, 1]] where
  M :=![![![810259, -277068, 89324], ![6323812, -788477, -2127220], ![-20083700, 6443696, -1342613]]]
  hmulB := by decide  
  f := ![![![14765778475521, 203581602820, 659814510508]], ![![4658095752611, 64223000567, 208148806648]], ![![12347756429840, 170243380624, 551764262083]]]
  g := ![![![12709, -277068, 89324], ![2027607, -788477, -2127220], ![-910016, 6443696, -1342613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1368113387075245003399963, -18862718050525945541592, -61134674769028291956728]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-1368113387075245003399963, -18862718050525945541592, -61134674769028291956728]] 
 ![![179, 0, 0], ![73, 1, 0], ![104, 0, 1]] where
  M :=![![![-1368113387075245003399963, -18862718050525945541592, -61134674769028291956728], ![-4745095393316230371751240, -65422498875124926767083, -212036419173235856289464], ![-2308314736656893894096776, -31825644322153187323664, -103147934976176817850267]]]
  hmulB := by decide  
  f := ![![![2889562714935, -569541606328, -541832602264]], ![![938982595549, -149379599403, -249452209040]], ![![1391475766672, -285278109168, -238279803795]]]
  g := ![![![35569112885989337344335, -18862718050525945541592, -61134674769028291956728], ![123366115187622448806425, -65422498875124926767083, -212036419173235856289464], ![60013086795433954396416, -31825644322153187323664, -103147934976176817850267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![810259, -277068, 89324]] ![![810259, -277068, 89324]]
  ![![-2889562714935, 569541606328, 541832602264]] where
 M := ![![![-2889562714935, 569541606328, 541832602264]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-2889562714935, 569541606328, 541832602264]] ![![-1368113387075245003399963, -18862718050525945541592, -61134674769028291956728]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [162, 108, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 135, 107], [138, 45, 74], [0, 1]]
 g := ![![[16, 57, 156], [161, 178], [111, 71, 81], [145, 5], [55, 108, 12], [138, 80, 1], []], ![[94, 19, 105, 90], [85, 38], [3, 170, 161, 47], [44, 29], [43, 152, 167, 120], [159, 58, 97, 18], [171, 46]], ![[140, 137, 4, 112], [38, 137], [179, 36, 10, 19], [174, 168], [37, 78, 64, 58], [106, 154, 25, 19], [23, 46]]]
 h' := ![![[123, 135, 107], [150, 128, 95], [118, 178, 84], [92, 16, 9], [140, 55, 154], [88, 10, 66], [0, 0, 1], [0, 1]], ![[138, 45, 74], [131, 129, 52], [114, 175, 20], [37, 76, 126], [123, 102, 145], [118, 125, 58], [97, 50, 45], [123, 135, 107]], ![[0, 1], [46, 105, 34], [49, 9, 77], [68, 89, 46], [127, 24, 63], [123, 46, 57], [114, 131, 135], [138, 45, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 56], []]
 b := ![[], [26, 109, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [162, 108, 101, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5750008, -2890570, 2615812]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31768, -15970, 14452]
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



lemma PB188I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 187 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 187 (by omega)

def PB188I3 : PrimesBelowBoundCertificateInterval O 137 187 188 where
  m := 9
  g := ![2, 1, 2, 1, 1, 1, 1, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB188I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N0, I179N1]
    · exact ![I181N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![5929741]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
  β := ![I139N1, I151N1, I179N0, I179N1]
  Il := ![[I139N1], [], [I151N1], [], [], [], [], [I179N0, I179N0, I179N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
