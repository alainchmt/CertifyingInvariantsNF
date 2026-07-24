
import IdealArithmetic.Examples.NF3_1_391287_1.RI3_1_391287_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [74, 119, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18, 19], [16, 120, 120], [0, 1]]
 g := ![![[15, 117, 78], [94, 50, 112], [52, 9], [6, 16, 106], [95, 47], [18, 1], []], ![[131, 118, 15, 90], [35, 82, 95, 104], [12, 28], [34, 97, 127, 33], [113, 100], [95, 83], [93, 83]], ![[115, 116, 136, 47], [11, 71, 98, 89], [65, 107], [102, 66, 128, 86], [39, 77], [44, 46], [131, 83]]]
 h' := ![![[2, 18, 19], [133, 94, 56], [78, 79, 116], [112, 111, 136], [87, 45, 84], [58, 8, 66], [0, 0, 1], [0, 1]], ![[16, 120, 120], [44, 8, 27], [109, 118, 131], [118, 33, 81], [109, 91, 93], [100, 6, 10], [72, 99, 120], [2, 18, 19]], ![[0, 1], [58, 37, 56], [47, 81, 31], [39, 134, 61], [37, 3, 101], [137, 125, 63], [14, 40, 18], [16, 120, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 14], []]
 b := ![[], [18, 8, 109], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [74, 119, 121, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31275, 48789, -6672]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-225, 351, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20145233533714899, 2171143027863611, 1142794778150000]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![20145233533714899, 2171143027863611, 1142794778150000]] 
 ![![149, 0, 0], ![0, 149, 0], ![100, 106, 1]] where
  M :=![![![20145233533714899, 2171143027863611, 1142794778150000], ![134964230350136389, 14545706171401288, 7656223861740833], ![353103540373783320, 38055567264259167, 20030787005278510]]]
  hmulB := by decide  
  f := ![![![-48897619, 23166110, -6064913]], ![![-750955670, -53868990, 63433417]], ![![-551693877, -24829073, 40965431]]]
  g := ![![![-631773451552249, -798423513127761, 1142794778150000], ![-4232605072643939, -5349087403846490, 7656223861740833], ![-11073658792980320, -13994683592585657, 20030787005278510]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [86, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 148], [0, 1]]
 g := ![![[72, 26], [95], [141, 81], [88], [73, 123], [35], [1]], ![[0, 123], [95], [123, 68], [88], [145, 26], [35], [1]]]
 h' := ![![[66, 148], [145, 131], [92, 63], [133, 9], [129, 104], [65, 47], [63, 66], [0, 1]], ![[0, 1], [0, 18], [78, 86], [131, 140], [139, 45], [38, 102], [98, 83], [66, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [143, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [86, 83, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4595, 2326, 483]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-355, -328, 483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48897619, 23166110, -6064913]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-48897619, 23166110, -6064913]] 
 ![![149, 0, 0], ![128, 1, 0], ![94, 0, 1]] where
  M :=![![![-48897619, 23166110, -6064913], ![-750955670, -53868990, 63433417], ![2288675247, -306029937, -13601683]]]
  hmulB := by decide  
  f := ![![![20145233533714899, 2171143027863611, 1142794778150000]], ![![18211772635339889, 1962765192872104, 1033113795066717]], ![![15078895923107274, 1625120885123749, 855392591619990]]]
  g := ![![![-16403073, 23166110, -6064913], ![1218348, -53868990, 63433417], ![286839365, -306029937, -13601683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![20145233533714899, 2171143027863611, 1142794778150000]] ![![-48897619, 23166110, -6064913]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [17, 103, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 120, 108], [85, 30, 43], [0, 1]]
 g := ![![[145, 52, 18], [74, 12, 39], [102, 35, 118], [143, 125], [27, 107, 74], [36, 1], []], ![[66, 45, 27, 13], [17, 46, 134, 3], [40, 48, 134, 48], [11, 137], [111, 84, 103, 134], [5, 145], [72, 37]], ![[64, 23, 61, 95], [27, 133, 107, 80], [126, 81, 130, 116], [27, 21], [129, 121, 90, 16], [39, 55], [137, 37]]]
 h' := ![![[102, 120, 108], [101, 70, 13], [78, 61, 48], [21, 130, 32], [145, 145, 124], [143, 50, 136], [0, 0, 1], [0, 1]], ![[85, 30, 43], [43, 85, 98], [131, 128, 25], [58, 34, 51], [68, 79, 52], [121, 18, 118], [120, 127, 30], [102, 120, 108]], ![[0, 1], [88, 147, 40], [30, 113, 78], [133, 138, 68], [21, 78, 126], [111, 83, 48], [64, 24, 120], [85, 30, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 126], []]
 b := ![[], [116, 66, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [17, 103, 115, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1327347078, 80598515, -35302894]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8790378, 533765, -233794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1060017237909, 979963994891, -314088585508]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1060017237909, 979963994891, -314088585508]] 
 ![![157, 0, 0], ![0, 157, 0], ![154, 122, 1]] where
  M :=![![![-1060017237909, 979963994891, -314088585508], ![-38670594255851, -1097715476276, 2625803399165], ![92154503960772, -15189346819485, 548123927998]]]
  hmulB := by decide  
  f := ![![![250207352809039478685061, 26965979255708377956466, 14193712659938414791451]], ![![1676279539936901397017654, 180660235573515856354242, 95091650427063548660849]], ![![1575946779879197879659469, 169846919753621004608347, 89399993684567769691501]]]
  g := ![![![301335190639, 250310646031, -314088585508], ![-2821938329473, -2047425032958, 2625803399165], ![49321140440, -522678127613, 548123927998]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [97, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 156], [0, 1]]
 g := ![![[39, 138], [130], [151, 46], [154, 35], [89, 36], [68], [1]], ![[10, 19], [130], [89, 111], [100, 122], [20, 121], [68], [1]]]
 h' := ![![[142, 156], [25, 83], [111, 82], [134, 108], [2, 52], [144, 6], [60, 142], [0, 1]], ![[0, 1], [36, 74], [137, 75], [84, 49], [7, 105], [54, 151], [128, 15], [142, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [81, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [97, 15, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2361, 2756, -312]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![291, 260, -312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55375053, 13081459, -8159285]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![55375053, 13081459, -8159285]] 
 ![![157, 0, 0], ![104, 1, 0], ![40, 0, 1]] where
  M :=![![![55375053, 13081459, -8159285], ![-992195659, 66771449, 31085092], ![908872995, -357456492, 84775082]]]
  hmulB := by decide  
  f := ![![![-16772123004051082, -1807607633923582, -951445638763193]], ![![-11825902302159058, -1274531034279557, -670857420203223]], ![![-6145636515749629, -662343072400873, -348628438923414]]]
  g := ![![![-6233919, 13081459, -8159285], ![-58470255, 66771449, 31085092], ![220976719, -357456492, 84775082]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1060017237909, 979963994891, -314088585508]] ![![55375053, 13081459, -8159285]]
  ![![157, 0, 0]] where
 M := ![![![-1316481165843242418806, 163840047822632555764, 12484368095181888381]]]
 hmul := by decide  
 g := ![![![![-8385230355689442158, 1043567183583646852, 79518268122177633]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-208022653350105391, -22419543198786826, -11800667467445822]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-208022653350105391, -22419543198786826, -11800667467445822]] 
 ![![163, 0, 0], ![0, 163, 0], ![77, 140, 1]] where
  M :=![![![-208022653350105391, -22419543198786826, -11800667467445822], ![-1393660552894711814, -150201107748981099, -79059297063806300], ![-3646199248717530702, -392967401634026580, -206840861614000573]]]
  hmulB := by decide  
  f := ![![![467602971, -47785874, -8412794]], ![![-961749406, 540627227, -151770416]], ![![-644510609, 440635326, -131650311]]]
  g := ![![![4298335838301981, 9997999400267658, -11800667467445822], ![28796965159621922, 66982211541005527, -79059297063806300], ![75340779727365113, 175243884811816280, -206840861614000573]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [68, 153, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 162], [0, 1]]
 g := ![![[43, 84], [118, 121], [84], [115], [151], [129, 100], [1]], ![[68, 79], [24, 42], [84], [115], [151], [151, 63], [1]]]
 h' := ![![[10, 162], [126, 35], [143, 11], [65, 35], [86, 21], [30, 92], [95, 10], [0, 1]], ![[0, 1], [150, 128], [90, 152], [89, 128], [133, 142], [135, 71], [32, 153], [10, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [17, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [68, 153, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![951, 351, -483]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![234, 417, -483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-467602971, 47785874, 8412794]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-467602971, 47785874, 8412794]] 
 ![![163, 0, 0], ![68, 1, 0], ![111, 0, 1]] where
  M :=![![![-467602971, 47785874, 8412794], ![961749406, -540627227, 151770416], ![6415741194, 184741344, -436642685]]]
  hmulB := by decide  
  f := ![![![208022653350105391, 22419543198786826, 11800667467445822]], ![![95332521353999254, 10274417455622609, 5408004201534492]], ![![164028918837909381, 17678139243554382, 9304999696322005]]]
  g := ![![![-28532899, 47785874, 8412794], ![128085182, -540627227, 151770416], ![259635999, 184741344, -436642685]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-208022653350105391, -22419543198786826, -11800667467445822]] ![![-467602971, 47785874, 8412794]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![442132200, 47650589, 25081187]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![442132200, 47650589, 25081187]] 
 ![![167, 0, 0], ![0, 167, 0], ![31, 88, 1]] where
  M :=![![![442132200, 47650589, 25081187], ![2962091851, 319238050, 168032954], ![7749646827, 835214526, 439620415]]]
  hmulB := by decide  
  f := ![![![-16162, 3281, -332]], ![![-43121, -18447, 9511]], ![![-23526, -9248, 4877]]]
  g := ![![![-2008291, -12931101, 25081187], ![-13454669, -86632706, 168032954], ![-35201114, -226654982, 439620415]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [37, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 166], [0, 1]]
 g := ![![[47, 36], [103, 38], [117, 144], [126], [36], [76, 85], [1]], ![[68, 131], [153, 129], [34, 23], [126], [36], [56, 82], [1]]]
 h' := ![![[98, 166], [30, 6], [13, 47], [64, 12], [65, 31], [27, 161], [130, 98], [0, 1]], ![[0, 1], [117, 161], [110, 120], [71, 155], [97, 136], [107, 6], [48, 69], [98, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [17, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [37, 69, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2453, 988, -300]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 164, -300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16162, 3281, -332]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-16162, 3281, -332]] 
 ![![167, 0, 0], ![69, 1, 0], ![50, 0, 1]] where
  M :=![![![-16162, 3281, -332], ![-43121, -18447, 9511], ![366828, -22791, -12217]]]
  hmulB := by decide  
  f := ![![![442132200, 47650589, 25081187]], ![![200414453, 21599573, 11369071]], ![![178779981, 19267928, 10141795]]]
  g := ![![![-1353, 3281, -332], ![4516, -18447, 9511], ![15271, -22791, -12217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![442132200, 47650589, 25081187]] ![![-16162, 3281, -332]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76588208765742354166, -8254258020886813389, -4344680586545296275]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-76588208765742354166, -8254258020886813389, -4344680586545296275]] 
 ![![173, 0, 0], ![0, 173, 0], ![106, 102, 1]] where
  M :=![![![-76588208765742354166, -8254258020886813389, -4344680586545296275], ![-513107412364548739611, -55299908985219651952, -29107454649205736442], ![-1342430090016586604955, -144679768812606114558, -76153105613538575005]]]
  hmulB := by decide  
  f := ![![![7783009612, -1250207685, 33822294]], ![![5308882965, 8931750415, -3716800761]], ![![7047513092, 4529400117, -2133314203]]]
  g := ![![![2219352216231555208, 2513891108709441657, -4344680586545296275], ![14868686592203811117, 16841968007131592284, -29107454649205736442], ![38900572861378626275, 44063219674961436624, -76153105613538575005]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [91, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 172], [0, 1]]
 g := ![![[41, 137], [29], [6, 95], [153, 106], [85], [118, 89], [1]], ![[109, 36], [29], [38, 78], [145, 67], [85], [46, 84], [1]]]
 h' := ![![[75, 172], [166, 39], [146, 78], [90, 21], [21, 148], [161, 36], [82, 75], [0, 1]], ![[0, 1], [150, 134], [114, 95], [108, 152], [49, 25], [93, 137], [171, 98], [75, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [157, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [91, 98, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1374, 1345, 483]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-288, -277, 483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7783009612, -1250207685, 33822294]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![7783009612, -1250207685, 33822294]] 
 ![![173, 0, 0], ![39, 1, 0], ![140, 0, 1]] where
  M :=![![![7783009612, -1250207685, 33822294], ![5308882965, 8931750415, -3716800761], ![-147285316386, 5069692521, 6465157339]]]
  hmulB := by decide  
  f := ![![![-76588208765742354166, -8254258020886813389, -4344680586545296275]], ![![-20231488752765899145, -2180439143351476151, -1147687846962267579]], ![![-69738608770060787215, -7516045616975491266, -3956117848149595685]]]
  g := ![![![299456579, -1250207685, 33822294], ![1024986840, 8931750415, -3716800761], ![-7226158105, 5069692521, 6465157339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-76588208765742354166, -8254258020886813389, -4344680586545296275]] ![![7783009612, -1250207685, 33822294]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)


lemma PB177I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 176 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 176 (by omega)

def PB177I3 : PrimesBelowBoundCertificateInterval O 137 176 177 where
  m := 7
  g := ![1, 2, 1, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB177I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I149N1, I157N1, I163N1, I167N1, I173N1]
  Il := ![[], [I149N1], [], [I157N1], [I163N1], [I167N1], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
