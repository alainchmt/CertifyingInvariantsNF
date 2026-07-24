
import IdealArithmetic.Examples.NF3_1_439803_1.RI3_1_439803_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3684811484270297687, 50803947065907851, 164657223446681635]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![3684811484270297687, 50803947065907851, 164657223446681635]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3684811484270297687, 50803947065907851, 164657223446681635], ![12780214099526301597, 176205844824075501, 571088799973944443], ![6217105052328447417, 85717675742706574, 277813738955891203]]]
  hmulB := by decide  
  f := ![![![486849421, -179966263, 81397858]], ![![2953851270, -521269667, -679166123]], ![![-6115491409, 2084555133, -660537001]]]
  g := ![![![1760077130411808026, 50803947065907851, 164657223446681635], ![6104562649776178577, 176205844824075501, 571088799973944443], ![2969645656686278107, 85717675742706574, 277813738955891203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![486849421, -179966263, 81397858]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![486849421, -179966263, 81397858]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 2]] where
  M :=![![![486849421, -179966263, 81397858], ![5907702540, -1042539334, -1358332246], ![-12717832239, 4349076529, -1402471860]]]
  hmulB := by decide  
  f := ![![![3684811484270297687, 50803947065907851, 164657223446681635]], ![![8232512791898299642, 113504895944991676, 367873011710313039]], ![![6217105052328447417, 85717675742706574, 277813738955891203]]]
  g := ![![![333407842, -179966263, 40698929], ![3475120937, -1042539334, -679166123], ![-8533454384, 4349076529, -701235930]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3609, 2791, -3464]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3200, 2791, -1732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![3684811484270297687, 50803947065907851, 164657223446681635]] ![![486849421, -179966263, 81397858]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121778479976770, 25724773689626, 19295576499093]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-121778479976770, 25724773689626, 19295576499093]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-121778479976770, 25724773689626, 19295576499093], ![1537208937809413, -552710360147349, 225093766016101], ![2250945645088504, -405151211988495, -501260812768097]]]
  hmulB := by decide  
  f := ![![![368249056465285796771883082848, 5077194763313035989898726687, 16455351225774241657737522683]], ![![548488496792176158799156594271, 7562226908008907319798368835, 24509420186017590411554952954]], ![![329855990133742983734136785103, 4547854438052990602062708347, 14739742237704666535677118625]]]
  g := ![![![-55599610055163, 25724773689626, 19295576499093], ![621608510646887, -552710360147349, 225093766016101], ![1052452556615032, -405151211988495, -501260812768097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-121778479976770, 25724773689626, 19295576499093]] ![![-121778479976770, 25724773689626, 19295576499093]]
  ![![97807644114375559956203609310, -25168698972995544202516624529, -6231416145389553489613237405]] where
 M := ![![![97807644114375559956203609310, -25168698972995544202516624529, -6231416145389553489613237405]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![97807644114375559956203609310, -25168698972995544202516624529, -6231416145389553489613237405]] ![![-121778479976770, 25724773689626, 19295576499093]]
  ![![3, 0, 0]] where
 M := ![![![-64626994279879682129425759904327424426912297, 18951745987471625201885310326723834015397156, -654497636617934048728365375617834173117314]]]
 hmul := by decide  
 g := ![![![![-21542331426626560709808586634775808142304099, 6317248662490541733961770108907944671799052, -218165878872644682909455125205944724372438]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56375902014963074, 777276762729199, 2519178941639739]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![56375902014963074, 777276762729199, 2519178941639739]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 1, 1]] where
  M :=![![![56375902014963074, 777276762729199, 2519178941639739], ![195531332031718301, 2695867477799356, 8737393043473331], ![95118815913104669, 1311440574164994, 4250421003257754]]]
  hmulB := by decide  
  f := ![![![-13913718, -1172496, 10656757]], ![![818225297, -236533119, 1276789]], ![![172644797, -27697180, -45388913]]]
  g := ![![![10771344614664667, -348380435782108, 2519178941639739], ![37358787797648994, -1208305113134795, 8737393043473331], ![18173678981969383, -587796085818552, 4250421003257754]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[3, 1], [1]], ![[2, 4], [1]]]
 h' := ![![[4, 4], [3, 4], [0, 1]], ![[0, 1], [4, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![511804, 277014, -781836]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258728, 211770, -781836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13913718, 1172496, -10656757]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![13913718, 1172496, -10656757]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![13913718, 1172496, -10656757], ![-818225297, 236533119, -1276789], ![-58912406, -99219715, 238878111]]]
  hmulB := by decide  
  f := ![![![-56375902014963074, -777276762729199, -2519178941639739]], ![![-50381446809336275, -694628848105711, -2251314397022614]], ![![-64124484794591393, -884109525016358, -2865427353963342]]]
  g := ![![![11073650, 1172496, -10656757], ![-209930252, 236533119, -1276789], ![-183041027, -99219715, 238878111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![56375902014963074, 777276762729199, 2519178941639739]] ![![13913718, 1172496, -10656757]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60044698062, -17539537670, 467364411]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![60044698062, -17539537670, 467364411]] 
 ![![7, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![60044698062, -17539537670, 467364411], ![907984307, 67769583101, -139848936949], ![-1344001298836, 371601841947, 32690507761]]]
  hmulB := by decide  
  f := ![![![-54183544646901241346564, -747049868313561605087, -2421212606436725950319]], ![![-42327794246579643439695, -583589968577651142136, -1891433823688381527379]], ![![-13059973764322629556595, -180063001496041135058, -583589968577651142136]]]
  g := ![![![13589110486, -17539537670, 467364411], ![-19233025985, 67769583101, -139848936949], ![-298172140390, 371601841947, 32690507761]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5575318713192566, -639281666788144, -1990289973747551]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5575318713192566, -639281666788144, -1990289973747551]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![5575318713192566, -639281666788144, -1990289973747551], ![-154530891312137715, 48010689828679281, -7104543308052703], ![-77088747975152802, -507114813681833, 46732126495102993]]]
  hmulB := by decide  
  f := ![![![-2240038811035037143501826222543434, -30884297247553636929225968255975, -100096998886464386369893525744063]], ![![-3029924339280441126478744393437915, -41774760093864744911456003313998, -135393338597954257146151775179463]], ![![-539921267496018778961272702303851, -7444107143803475582215620976138, -24126590238119809523326878596298]]]
  g := ![![![1344429816274490, -639281666788144, -1990289973747551], ![-63227861469173343, 48010689828679281, -7104543308052703], ![-10578008441865972, -507114813681833, 46732126495102993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![60044698062, -17539537670, 467364411]] ![![5575318713192566, -639281666788144, -1990289973747551]]
  ![![3009140180788846450061501520, -880707784887878079870837561, 26944977224400496914657971]] where
 M := ![![![3009140180788846450061501520, -880707784887878079870837561, 26944977224400496914657971]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![3009140180788846450061501520, -880707784887878079870837561, 26944977224400496914657971]] ![![5575318713192566, -639281666788144, -1990289973747551]]
  ![![7, 0, 0]] where
 M := ![![![150796319986385924968660106443430656996128693, -44220740637433792137732390762355612702593364, 1527161152108512780366185876441613070607066]]]
 hmul := by decide  
 g := ![![![![21542331426626560709808586634775808142304099, -6317248662490541733961770108907944671799052, 218165878872644682909455125205944724372438]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6020, 83, 269]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![6020, 83, 269]] 
 ![![11, 0, 0], ![0, 11, 0], ![5, 10, 1]] where
  M :=![![![6020, 83, 269], ![20879, 288, 933], ![10157, 140, 454]]]
  hmulB := by decide  
  f := ![![![12, -2, -3]], ![![-235, 77, -19]], ![![-226, 71, -12]]]
  g := ![![![425, -237, 269], ![1474, -822, 933], ![717, -400, 454]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[9, 5], [10, 4], [1]], ![[10, 6], [2, 7], [1]]]
 h' := ![![[9, 10], [10, 7], [1, 9], [0, 1]], ![[0, 1], [7, 4], [5, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [10, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3772, 4138, -5997]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2383, 5828, -5997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 2, 3]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-12, 2, 3]] 
 ![![11, 0, 0], ![7, 1, 0], ![6, 0, 1]] where
  M :=![![![-12, 2, 3], ![235, -77, 19], ![196, -21, -73]]]
  hmulB := by decide  
  f := ![![![-6020, -83, -269]], ![![-5729, -79, -256]], ![![-4207, -58, -188]]]
  g := ![![![-4, 2, 3], ![60, -77, 19], ![71, -21, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![6020, 83, 269]] ![![-12, 2, 3]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-559104352714, 134883897757, 54100589429]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-559104352714, 134883897757, 54100589429]] 
 ![![13, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![-559104352714, 134883897757, 54100589429], ![4435513181547, -1830100628480, 1133171771485], ![11143468379295, -2453857726894, -1560332832966]]]
  hmulB := by decide  
  f := ![![![-5636208405605684769289270, -77708624908804597653736, -251856148081252652397065]], ![![-1937273004436903707628519, -26709945838413774534685, -86567791956380160463386]], ![![-5067048788244026065060714, -69861397120916768660643, -226423030893900783890407]]]
  g := ![![![-94999549597, 134883897757, 54100589429], ![-389700300371, -1830100628480, 1133171771485], ![2246204187373, -2453857726894, -1560332832966]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2240073706930, 30884778371, 100098558223]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![2240073706930, 30884778371, 100098558223]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![2240073706930, 30884778371, 100098558223], ![7769358539913, 107119205876, 347176785191], ![3779507749689, 52109561770, 168888762618]]]
  hmulB := by decide  
  f := ![![![-1004702, 199432, 185513]], ![![665781, -300255, 222619]], ![![1149180, -176245, -318808]]]
  g := ![![![134959181695, 30884778371, 100098558223], ![468085611468, 107119205876, 347176785191], ![227706468555, 52109561770, 168888762618]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-559104352714, 134883897757, 54100589429]] ![![2240073706930, 30884778371, 100098558223]]
  ![![1004702, -199432, -185513]] where
 M := ![![![1004702, -199432, -185513]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![1004702, -199432, -185513]] ![![2240073706930, 30884778371, 100098558223]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11012678282164686, -72444973383119, 6676018070728999]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-11012678282164686, -72444973383119, 6676018070728999]] 
 ![![17, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-11012678282164686, -72444973383119, 6676018070728999], ![513908501499366685, -151136612794090546, 6096458283664047], ![87885990039705823, 48253470936148492, -151281502740856784]]]
  hmulB := by decide  
  f := ![![![-22569998630048794611377172280696940, -311181459505704267091910612290212, -1008549100404028776675280616920861]], ![![-7260037700601130209466751369934153, -100096998886464386369893525744063, -324417586897512968633007455828487]], ![![-2240038811035037143501826222543434, -30884297247553636929225968255975, -100096998886464386369893525744063]]]
  g := ![![![-639281666788144, -72444973383119, 6676018070728999], ![48010689828679281, -151136612794090546, 6096458283664047], ![-507114813681833, 48253470936148492, -151281502740856784]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7770175811505072717336060002, -107130473921293330099442391, -347213305287544150102662141]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-7770175811505072717336060002, -107130473921293330099442391, -347213305287544150102662141]] 
 ![![17, 0, 0], ![5, 1, 0], ![2, 0, 1]] where
  M :=![![![-7770175811505072717336060002, -107130473921293330099442391, -347213305287544150102662141], ![-26949685454983486218103869639, -371565926545352235080712650, -1204257096657890790898201269], ![-13110032765965204519094334081, -180753184665649118630344776, -585826874387938895279597432]]]
  hmulB := by decide  
  f := ![![![-29059959194056, 15759883214496, -15173333810529]], ![![-75419219585413, 20742328452061, 2061121344282]], ![![55468495045922, -23861830455831, 16176074495323]]]
  g := ![![![-384711578313148103919619045, -107130473921293330099442391, -347213305287544150102662141], ![-1334314213467114321229641403, -371565926545352235080712650, -1204257096657890790898201269], ![-649094887874181243257847961, -180753184665649118630344776, -585826874387938895279597432]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2586058, -35655, -115559]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-2586058, -35655, -115559]] 
 ![![17, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![-2586058, -35655, -115559], ![-8969353, -123664, -400799], ![-4363261, -60158, -194974]]]
  hmulB := by decide  
  f := ![![![1506, -352, -169]], ![![79, 111, -275]], ![![-1202, 241, 217]]]
  g := ![![![-90362, -35655, -115559], ![-313407, -123664, -400799], ![-152461, -60158, -194974]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-11012678282164686, -72444973383119, 6676018070728999]] ![![-7770175811505072717336060002, -107130473921293330099442391, -347213305287544150102662141]]
  ![![-1506, 352, 169]] where
 M := ![![![-1506, 352, 169]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-1506, 352, 169]] ![![-2586058, -35655, -115559]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [1, 9, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 12, 7], [3, 6, 12], [0, 1]]
 g := ![![[2, 15, 9], [11, 15, 7], [1, 1], []], ![[1, 13, 11, 5], [10, 5, 16, 17], [3, 17], [8, 11]], ![[15, 8, 14, 3], [17, 9, 9, 18], [1, 11], [3, 11]]]
 h' := ![![[17, 12, 7], [8, 1, 3], [18, 9, 11], [0, 0, 1], [0, 1]], ![[3, 6, 12], [13, 18, 6], [13, 16, 15], [15, 2, 6], [17, 12, 7]], ![[0, 1], [10, 0, 10], [16, 13, 12], [6, 17, 12], [3, 6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 11], []]
 b := ![[], [2, 1, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [1, 9, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1114863, 712158, -803700]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-58677, 37482, -42300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10640, -5017, 4007]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![10640, -5017, 4007]] 
 ![![23, 0, 0], ![5, 1, 0], ![15, 0, 1]] where
  M :=![![![10640, -5017, 4007], ![298505, -68490, -36129], ![-330211, 133406, -78524]]]
  hmulB := by decide  
  f := ![![![-10197934134, -140602934, -455698623]], ![![-3754768283, -51768469, -167783270]], ![![-7398922550, -102011859, -330623710]]]
  g := ![![![-1060, -5017, 4007], ![51430, -68490, -36129], ![7853, 133406, -78524]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![862889823357704268, 11897001813175974, 38558564816949769]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![862889823357704268, 11897001813175974, 38558564816949769]] 
 ![![23, 0, 0], ![20, 1, 0], ![16, 0, 1]] where
  M :=![![![862889823357704268, 11897001813175974, 38558564816949769], ![2992803494531484161, 41262960388583145, 133734579322357561], ![1455889047051846764, 20072915641952929, 65056964014935093]]]
  hmulB := by decide  
  f := ![![![-1060438684, 258367819, 97395909]], ![![-573589263, 78401556, 178793767]], ![![186558515, -26524684, -56045670]]]
  g := ![![![348380435782108, 11897001813175974, 38558564816949769], ![1208305113134795, 41262960388583145, 133734579322357561], ![587796085818552, 20072915641952929, 65056964014935093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9685, 3130, -694]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-9685, 3130, -694]] 
 ![![23, 0, 0], ![21, 1, 0], ![11, 0, 1]] where
  M :=![![![-9685, 3130, -694], ![-47178, 1759, 24346], ![231294, -70588, 8019]]]
  hmulB := by decide  
  f := ![![![1732640869, 23888602, 77423726]], ![![1843254885, 25413681, 82366556]], ![![955756699, 13177394, 42708357]]]
  g := ![![![-2947, 3130, -694], ![-15301, 1759, 24346], ![70671, -70588, 8019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![10640, -5017, 4007]] ![![862889823357704268, 11897001813175974, 38558564816949769]]
  ![![-1732640869, -23888602, -77423726]] where
 M := ![![![-1732640869, -23888602, -77423726]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1732640869, -23888602, -77423726]] ![![-9685, 3130, -694]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8989648661648991033899, -2209014641350269980948, -787099545747877805794]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![8989648661648991033899, -2209014641350269980948, -787099545747877805794]] 
 ![![29, 0, 0], ![0, 29, 0], ![18, 19, 1]] where
  M :=![![![8989648661648991033899, -2209014641350269980948, -787099545747877805794], ![-65024694305287131008034, 27727753763704694936521, -18459216676550037653378], ![-181113521024441077814112, 40879610648120524959350, 23309724481004154974625]]]
  hmulB := by decide  
  f := ![![![-48307996252266941807902172182048757364860825, -666041368720456126094797175968677556171400, -2158661458564726846976508484936615940822242]], ![![-167549015046924879469380747692056782555655434, -2310064253687221895300696822411145051422343, -7486992408328375855734885892686036390193442]], ![![-142568333249784791725084269198781286073160596, -1965645755994790881422910603188346030836759, -6370721000121805470759664684973871672835893]]]
  g := ![![![798532430521061777179, 439512990615841666522, -787099545747877805794], ![9215213995607363681130, 13050098986832945184507, -18459216676550037653378], ![-20713398678707443701978, -13862246706584773088225, 23309724481004154974625]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 28], [0, 1]]
 g := ![![[11, 23], [5], [25, 28], [23, 1]], ![[18, 6], [5], [2, 1], [17, 28]]]
 h' := ![![[23, 28], [26, 9], [18, 18], [27, 17], [0, 1]], ![[0, 1], [1, 20], [26, 11], [12, 12], [23, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [19, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [19, 6, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93205, 56586, -154765]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99275, 103349, -154765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13420551311511349266549, -3047802248975581374536, -1688991296525929081608]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![13420551311511349266549, -3047802248975581374536, -1688991296525929081608]] 
 ![![29, 0, 0], ![21, 1, 0], ![13, 0, 1]] where
  M :=![![![13420551311511349266549, -3047802248975581374536, -1688991296525929081608], ![-136147934330447702032888, 51937170787531441354853, -26071409288330580077896], ![-258326651322482772981784, 52180908152805705294000, 45841566289580278605781]]]
  hmulB := by decide  
  f := ![![![3741311071038458489536229100117656204099629193, 51582929119038239039853901874697538023040616, 167181929289258141746441050176034347154699880]], ![![3156679548459261436993671716199131727346558105, 43522384080855251505449830479823643941784277, 141057444045378794163466700650701239365093872]], ![![1894809533645362715672065636149852480732245009, 26124485243879347582974349525333107789606008, 84670295373911434296708779330485481547761061]]]
  g := ![![![3426940875683987454921, -3047802248975581374536, -1688991296525929081608], ![-30617248280010704464557, 51937170787531441354853, -26071409288330580077896], ![-67243658079170558828653, 52180908152805705294000, 45841566289580278605781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![8989648661648991033899, -2209014641350269980948, -787099545747877805794]] ![![13420551311511349266549, -3047802248975581374536, -1688991296525929081608]]
  ![![29, 0, 0]] where
 M := ![![![624727611372170260584449012408498436126818871, -183200211212225710284891333158330395482172508, 6326810487306695804374198630972397006800702]]]
 hmul := by decide  
 g := ![![![![21542331426626560709808586634775808142304099, -6317248662490541733961770108907944671799052, 218165878872644682909455125205944724372438]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [22, 24, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 5, 13], [22, 25, 18], [0, 1]]
 g := ![![[17, 21, 9], [8, 29, 9], [14, 3, 28], [1]], ![[6, 25, 16, 3], [15, 5, 21, 13], [26, 6, 28, 21], [8, 22, 6, 27]], ![[10, 18, 22, 7], [2, 26, 9, 9], [8, 3, 0, 1], [16, 14, 14, 4]]]
 h' := ![![[29, 5, 13], [10, 11, 28], [2, 20, 28], [9, 7, 20], [0, 1]], ![[22, 25, 18], [4, 24, 6], [9, 7, 30], [2, 4, 2], [29, 5, 13]], ![[0, 1], [17, 27, 28], [21, 4, 4], [4, 20, 9], [22, 25, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 20], []]
 b := ![[], [30, 23, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [22, 24, 11, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1953, 744, -31]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, 24, -1]
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



lemma PB188I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB188I0 : PrimesBelowBoundCertificateInterval O 1 31 188 where
  m := 11
  g := ![2, 3, 2, 3, 2, 3, 3, 1, 3, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB188I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![6859]
    · exact ![23, 23, 23]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
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
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I17N2, I23N0, I23N1, I23N2, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N1, I7N1], [I11N0, I11N1], [I13N0, I13N1, I13N1], [I17N0, I17N1, I17N2], [], [I23N0, I23N1, I23N2], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
