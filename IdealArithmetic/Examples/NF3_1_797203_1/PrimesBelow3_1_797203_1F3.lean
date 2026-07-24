
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-37, 30, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-37, 30, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![102, 30, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-37, 30, 1], ![212, -93, 122], ![4661, -755, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -30, 139]], ![![-1, 0, 1], ![-88, -27, 122], ![35, -5, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [121, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 138], [0, 1]]
 g := ![![[17, 54], [49, 64], [124], [133, 13], [69], [89], [1]], ![[0, 85], [34, 75], [124], [80, 126], [69], [89], [1]]]
 h' := ![![[28, 138], [48, 38], [135, 131], [31, 47], [113, 98], [119, 25], [18, 28], [0, 1]], ![[0, 1], [0, 101], [50, 8], [96, 92], [77, 41], [124, 114], [107, 111], [28, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [115, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [121, 111, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1611, 1316, -1550]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1149, 344, -1550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![17, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![17, 1, 0]] 
 ![![139, 0, 0], ![17, 1, 0], ![2, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![17, 1, 0], ![2, 16, 4], ![152, -26, 19]]]
  hmulB := by decide  
  f := ![![![8797, 71988, 18000], ![1668, -625500, 0]], ![![1066, 8798, 2200], ![279, -76450, 0]], ![![113, 1035, 259], ![135, -9000, 0]]]
  g := ![![![1, 0, 0], ![-17, 139, 0], ![-2, 0, 139]], ![![0, 1, 0], ![-2, 16, 4], ![4, -26, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-37, 30, 1]] ![![139, 0, 0], ![17, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2363, 139, 0]], ![![-5143, 4170, 139], ![-417, 417, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![17, 1, 0]]], ![![![-37, 30, 1]], ![![-3, 3, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![16, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![16, 1, 0]] 
 ![![149, 0, 0], ![16, 1, 0], ![15, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![16, 1, 0], ![2, 15, 4], ![152, -26, 18]]]
  hmulB := by decide  
  f := ![![![-2207, -16798, -4480], ![-298, 166880, 0]], ![![-240, -1800, -480], ![1, 17880, 0]], ![![-237, -1692, -451], ![108, 16800, 0]]]
  g := ![![![1, 0, 0], ![-16, 149, 0], ![-15, 0, 149]], ![![0, 1, 0], ![-2, 15, 4], ![2, -26, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65548611960504795848208332351607832908199493, -1621946966120043900340293171265599621882636, -2145295804745535652796853286129321125683196]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-65548611960504795848208332351607832908199493, -1621946966120043900340293171265599621882636, -2145295804745535652796853286129321125683196]] 
 ![![149, 0, 0], ![26, 1, 0], ![136, 0, 1]] where
  M :=![![![-65548611960504795848208332351607832908199493, -1621946966120043900340293171265599621882636, -2145295804745535652796853286129321125683196], ![-329328856253561507025802285834188010347611064, -8148974071000824975149853740979884018553761, -10778379473971246906954879257321040738896936], ![-463210815129545773784206743931432576220163468, -11461773999517249911073709700327437973131364, -15160110774106492328967586540906004009884865]]]
  hmulB := by decide  
  f := ![![![-17621086744730237626561, -1014148925851052655204, 3214575814162688296860]], ![![190865574080807634374, -849354235296888924329, 576855886531215179136]], ![![-14939236756927790622956, -209342191205024058060, 2262876045474000389359]]]
  g := ![![![1801223077879256337859136490032788123178951, -1621946966120043900340293171265599621882636, -2145295804745535652796853286129321125683196], ![9049691799010399474321862351858728286072282, -8148974071000824975149853740979884018553761, -10778379473971246906954879257321040738896936], ![12728660229103259601632895824431525882050964, -11461773999517249911073709700327437973131364, -15160110774106492328967586540906004009884865]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-43, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-43, 1, 0]] 
 ![![149, 0, 0], ![106, 1, 0], ![49, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-43, 1, 0], ![2, -44, 4], ![152, -26, -41]]]
  hmulB := by decide  
  f := ![![![13219, -328596, 29876], ![-5960, -1112881, 0]], ![![9423, -233744, 21252], ![-4171, -791637, 0]], ![![4357, -108062, 9825], ![-1926, -365981, 0]]]
  g := ![![![1, 0, 0], ![-106, 149, 0], ![-49, 0, 149]], ![![-1, 1, 0], ![30, -44, 4], ![33, -26, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![16, 1, 0]] ![![-65548611960504795848208332351607832908199493, -1621946966120043900340293171265599621882636, -2145295804745535652796853286129321125683196]]
  ![![149, 0, 0], ![30, -27, 1]] where
 M := ![![![-9766743182115214581383041520389567103321724457, -241670097951886541150703682518574343660512764, -319649074907084812266731139633268847726796204]], ![![-1378106647621638240597135603459913336878802952, -34100125528921527380594544481229477968675937, -45103112349899817351704531835390178749828072]]]
 hmul := by decide  
 g := ![![![![-63125535606342593390330116278161238407027723, -3802715684866026112430687637367534672937229, -2064526592940128904200912750347767975644137], ![-12034612559005605540795139831451419355819791, 0, 0]]], ![![![-8907137070326512260351948935728350811393108, -536570652735641944998793525597178774173039, -291308757573603267728510233338996934343090], ![-1698107471432930460156507067879635532707662, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![30, -27, 1]] ![![149, 0, 0], ![-43, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-6407, 149, 0]], ![![4470, -4023, 149], ![-1192, 1192, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-43, 1, 0]]], ![![![30, -27, 1]], ![![-8, 8, -1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![0, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![0, 1, 0]] 
 ![![151, 0, 0], ![0, 1, 0], ![76, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![0, 1, 0], ![2, -1, 4], ![152, -26, 2]]]
  hmulB := by decide  
  f := ![![![-151, 75, -304], ![151, 11476, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-76, 38, -153], ![38, 5776, 0]]]
  g := ![![![1, 0, 0], ![0, 151, 0], ![-76, 0, 151]], ![![0, 1, 0], ![-2, -1, 4], ![0, -26, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-50, 75, 1]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-50, 75, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![101, 75, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-50, 75, 1], ![302, -151, 302], ![11501, -1925, 75]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -75, 151]], ![![-1, 0, 1], ![-200, -151, 302], ![26, -50, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [9, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 150], [0, 1]]
 g := ![![[148, 84], [1, 123], [79, 144], [42], [146, 98], [125], [1]], ![[0, 67], [0, 28], [41, 7], [42], [74, 53], [125], [1]]]
 h' := ![![[27, 150], [142, 101], [44, 127], [137, 12], [45, 58], [13, 20], [142, 27], [0, 1]], ![[0, 1], [0, 50], [0, 24], [8, 139], [101, 93], [100, 131], [116, 124], [27, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [2, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [9, 124, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1027, 1918, -363]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![236, 193, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![0, 1, 0]] ![![151, 0, 0], ![-50, 75, 1]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-7550, 11325, 151]], ![![0, 151, 0], ![302, -151, 302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-50, 75, 1]]], ![![![0, 1, 0]], ![![2, -1, 2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-52, -70, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-52, -70, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![105, 87, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-52, -70, 1], ![12, -8, -278], ![-10539, 1845, -217]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -87, 157]], ![![-1, -1, 1], ![186, 154, -278], ![78, 132, -217]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [95, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 156], [0, 1]]
 g := ![![[46, 49], [4], [99, 138], [78, 121], [53, 124], [48], [1]], ![[64, 108], [4], [76, 19], [84, 36], [137, 33], [48], [1]]]
 h' := ![![[26, 156], [2, 7], [15, 2], [126, 74], [146, 11], [69, 76], [62, 26], [0, 1]], ![[0, 1], [27, 150], [67, 155], [9, 83], [118, 146], [4, 81], [110, 131], [26, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [16, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [95, 131, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415699, 112332, -109226]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![75697, 61242, -109226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-36, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-36, 1, 0]] 
 ![![157, 0, 0], ![121, 1, 0], ![60, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-36, 1, 0], ![2, -37, 4], ![152, -26, -34]]]
  hmulB := by decide  
  f := ![![![1637, -32261, 3488], ![-471, -136904, 0]], ![![1273, -24862, 2688], ![-313, -105504, 0]], ![![624, -12329, 1333], ![-187, -52320, 0]]]
  g := ![![![1, 0, 0], ![-121, 157, 0], ![-60, 0, 157]], ![![-1, 1, 0], ![27, -37, 4], ![34, -26, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-52, -70, 1]] ![![157, 0, 0], ![-36, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5652, 157, 0]], ![![-8164, -10990, 157], ![1884, 2512, -314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-36, 1, 0]]], ![![![-52, -70, 1]], ![![12, 16, -2]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-33, 30, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-33, 30, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![130, 30, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-33, 30, 1], ![212, -89, 122], ![4661, -755, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-130, -30, 163]], ![![-1, 0, 1], ![-96, -23, 122], ![27, -5, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [30, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 162], [0, 1]]
 g := ![![[116, 64], [56, 46], [1], [64], [91], [135, 152], [1]], ![[54, 99], [42, 117], [1], [64], [91], [110, 11], [1]]]
 h' := ![![[106, 162], [113, 8], [4, 131], [69, 162], [14, 8], [25, 55], [133, 106], [0, 1]], ![[0, 1], [146, 155], [35, 32], [126, 1], [47, 155], [150, 108], [122, 57], [106, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [95, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [30, 57, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-191, 3567, -2538]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2023, 489, -2538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![41, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![41, 1, 0]] 
 ![![163, 0, 0], ![41, 1, 0], ![161, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![41, 1, 0], ![2, 40, 4], ![152, -26, 43]]]
  hmulB := by decide  
  f := ![![![775, 17118, 1712], ![326, -69764, 0]], ![![173, 4279, 428], ![164, -17441, 0]], ![![767, 16908, 1691], ![316, -68908, 0]]]
  g := ![![![1, 0, 0], ![-41, 163, 0], ![-161, 0, 163]], ![![0, 1, 0], ![-14, 40, 4], ![-35, -26, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-33, 30, 1]] ![![163, 0, 0], ![41, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![6683, 163, 0]], ![![-5379, 4890, 163], ![-1141, 1141, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![41, 1, 0]]], ![![![-33, 30, 1]], ![![-7, 7, 1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![72, -28, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![72, -28, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![72, 139, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![72, -28, 1], ![96, 74, -110], ![-4155, 753, -9]]]
  hmulB := by decide  
  f := ![![![-71, 28, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -139, 167]], ![![0, -1, 1], ![48, 92, -110], ![-21, 12, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [118, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 166], [0, 1]]
 g := ![![[139, 122], [89, 87], [9, 81], [100], [94], [83, 127], [1]], ![[89, 45], [130, 80], [99, 86], [100], [94], [20, 40], [1]]]
 h' := ![![[131, 166], [19, 150], [107, 33], [88, 158], [71, 10], [59, 125], [49, 131], [0, 1]], ![[0, 1], [130, 17], [88, 134], [78, 9], [45, 157], [68, 42], [9, 36], [131, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [64, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [118, 36, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![175073, 48380, -42953]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19567, 36041, -42953]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-57, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-57, 1, 0]] 
 ![![167, 0, 0], ![110, 1, 0], ![9, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-57, 1, 0], ![2, -58, 4], ![152, -26, -55]]]
  hmulB := by decide  
  f := ![![![-4663, 161688, -11152], ![2672, 465596, 0]], ![![-3044, 106477, -7344], ![1838, 306612, 0]], ![![-210, 8713, -601], ![265, 25092, 0]]]
  g := ![![![1, 0, 0], ![-110, 167, 0], ![-9, 0, 167]], ![![-1, 1, 0], ![38, -58, 4], ![21, -26, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![72, -28, 1]] ![![167, 0, 0], ![-57, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-9519, 167, 0]], ![![12024, -4676, 167], ![-4008, 1670, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-57, 1, 0]]], ![![![72, -28, 1]], ![![-24, 10, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-97361743338316684277759639835110714119607, -2409136967215880900354895169564130096810, -3186486079251431049498341921817683892664]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-97361743338316684277759639835110714119607, -2409136967215880900354895169564130096810, -3186486079251431049498341921817683892664]] 
 ![![173, 0, 0], ![0, 173, 0], ![34, 91, 1]] where
  M :=![![![-97361743338316684277759639835110714119607, -2409136967215880900354895169564130096810, -3186486079251431049498341921817683892664], ![-489164157980649281324457762455416211878548, -12103968310563596090447854698286802813533, -16009520027366385700416264521891888172568], ![-688023913021208432853276599877333847874184, -17024590833672872828231273636774714799540, -22517865291462669841010882128796876996627]]]
  hmulB := by decide  
  f := ![![![32254322940835237373, 8268024621814548470, -10442599854503165816]], ![![-1570739128640852107092, 295493894536103000119, 12186898778251862248]], ![![-818720095775249433842, 154306494817325492793, 6149218279276620269]]]
  g := ![![![63461175469548967660023037610927966653, 1662202868466267887884359651536676902518, -3186486079251431049498341921817683892664], ![318841173120276488379741221323167549068, 8351227480807962443048741137536849831735, -16009520027366385700416264521891888172568], ![448459577390302553416724812148901560758, 11746249425950462905802075144992723074529, -22517865291462669841010882128796876996627]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [104, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 172], [0, 1]]
 g := ![![[94, 139], [167], [156, 118], [90, 118], [96], [114, 132], [1]], ![[145, 34], [167], [152, 55], [86, 55], [96], [89, 41], [1]]]
 h' := ![![[85, 172], [165, 73], [38, 101], [155, 34], [37, 34], [81, 31], [69, 85], [0, 1]], ![[0, 1], [142, 100], [146, 72], [104, 139], [159, 139], [121, 142], [28, 88], [85, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [166, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [104, 88, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![511, 60, 71]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -37, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-327613, 64110, 780]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-327613, 64110, 780]] 
 ![![173, 0, 0], ![153, 1, 0], ![155, 0, 1]] where
  M :=![![![-327613, 64110, 780], ![246780, -412003, 258000], ![9823500, -1647360, -218893]]]
  hmulB := by decide  
  f := ![![![515203452679, 12748289430, 16861742340]], ![![470604680199, 11644729163, 15402099540]], ![![482643416965, 11942617890, 15796107143]]]
  g := ![![![-59291, 64110, 780], ![134643, -412003, 258000], ![1709815, -1647360, -218893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-97361743338316684277759639835110714119607, -2409136967215880900354895169564130096810, -3186486079251431049498341921817683892664]] ![![-327613, 64110, 780]]
  ![![173, 0, 0]] where
 M := ![![![-24117046874013620927360008767709, -596756664086957437852513027300, -789310374914526493641673372508]]]
 hmul := by decide  
 g := ![![![![-139404895225512259695722594033, -3449460486051777097413370100, -4562487716268939269605048396]]]]
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
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![79, -8, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![79, -8, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![79, 171, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![79, -8, 1], ![136, 61, -30], ![-1115, 233, 38]]]
  hmulB := by decide  
  f := ![![![-78, 8, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -171, 179]], ![![0, -1, 1], ![14, 29, -30], ![-23, -35, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [2, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 178], [0, 1]]
 g := ![![[113, 161], [100, 75], [117], [177], [82, 153], [6, 61], [1]], ![[64, 18], [155, 104], [117], [177], [51, 26], [3, 118], [1]]]
 h' := ![![[132, 178], [158, 124], [118, 95], [50, 81], [15, 101], [167, 137], [177, 132], [0, 1]], ![[0, 1], [58, 55], [128, 84], [2, 98], [101, 78], [172, 42], [59, 47], [132, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [16, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [2, 47, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4290, 3422, -1994]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![904, 1924, -1994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![30, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![30, 1, 0]] 
 ![![179, 0, 0], ![30, 1, 0], ![141, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![30, 1, 0], ![2, 29, 4], ![152, -26, 32]]]
  hmulB := by decide  
  f := ![![![1807, 27489, 3792], ![537, -169692, 0]], ![![286, 4581, 632], ![180, -28282, 0]], ![![1413, 21653, 2987], ![485, -133668, 0]]]
  g := ![![![1, 0, 0], ![-30, 179, 0], ![-141, 0, 179]], ![![0, 1, 0], ![-8, 29, 4], ![-20, -26, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![79, -8, 1]] ![![179, 0, 0], ![30, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![5370, 179, 0]], ![![14141, -1432, 179], ![2506, -179, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![30, 1, 0]]], ![![![79, -8, 1]], ![![14, -1, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [168, 45, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 129, 141], [79, 51, 40], [0, 1]]
 g := ![![[82, 12, 37], [64, 67], [136, 121, 52], [118, 46], [0, 19, 137], [178, 59, 1], []], ![[168, 14, 136, 88], [156, 126], [122, 86, 108, 92], [22, 33], [106, 103, 156, 54], [43, 48, 18, 35], [96, 152]], ![[168, 141, 104, 160], [174, 49], [51, 95, 3, 175], [17, 11], [19, 131, 63, 24], [107, 161, 154, 103], [16, 152]]]
 h' := ![![[161, 129, 141], [62, 129, 134], [139, 134, 51], [86, 175, 140], [0, 139, 74], [142, 178, 77], [0, 0, 1], [0, 1]], ![[79, 51, 40], [28, 89, 45], [57, 21, 137], [151, 95, 140], [74, 24, 24], [36, 100, 65], [19, 98, 51], [161, 129, 141]], ![[0, 1], [8, 144, 2], [68, 26, 174], [6, 92, 82], [50, 18, 83], [176, 84, 39], [114, 83, 129], [79, 51, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 19], []]
 b := ![[], [151, 175, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [168, 45, 122, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![113668, 226250, -158375]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![628, 1250, -875]
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

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-66, -70, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-66, -70, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![125, 121, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-66, -70, 1], ![12, -22, -278], ![-10539, 1845, -231]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -121, 191]], ![![-1, -1, 1], ![182, 176, -278], ![96, 156, -231]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [91, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 190], [0, 1]]
 g := ![![[26, 144], [60, 12], [103, 30], [47, 49], [125, 79], [176, 128], [1]], ![[66, 47], [127, 179], [175, 161], [50, 142], [9, 112], [63, 63], [1]]]
 h' := ![![[117, 190], [79, 12], [177, 48], [116, 52], [85, 7], [28, 35], [100, 117], [0, 1]], ![[0, 1], [146, 179], [63, 143], [88, 139], [140, 184], [112, 156], [37, 74], [117, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [112, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [91, 74, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15999, 1324, -3064]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2089, 1948, -3064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![87, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![87, 1, 0]] 
 ![![191, 0, 0], ![87, 1, 0], ![40, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![87, 1, 0], ![2, 86, 4], ![152, -26, 89]]]
  hmulB := by decide  
  f := ![![![-4263, -243192, -11312], ![-3056, 540148, 0]], ![![-1967, -110761, -5152], ![-1336, 246008, 0]], ![![-957, -50931, -2369], ![-499, 113120, 0]]]
  g := ![![![1, 0, 0], ![-87, 191, 0], ![-40, 0, 191]], ![![0, 1, 0], ![-40, 86, 4], ![-6, -26, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-66, -70, 1]] ![![191, 0, 0], ![87, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![16617, 191, 0]], ![![-12606, -13370, 191], ![-5730, -6112, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![87, 1, 0]]], ![![![-66, -70, 1]], ![![-30, -32, -1]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![110, -31, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![110, -31, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![110, 162, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![110, -31, 1], ![90, 115, -122], ![-4611, 831, 23]]]
  hmulB := by decide  
  f := ![![![-109, 31, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-110, -162, 193]], ![![0, -1, 1], ![70, 103, -122], ![-37, -15, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [147, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [146, 192], [0, 1]]
 g := ![![[171, 172], [175], [14], [84], [145], [54], [146, 1]], ![[0, 21], [175], [14], [84], [145], [54], [99, 192]]]
 h' := ![![[146, 192], [160, 65], [71, 91], [149, 20], [96, 85], [145, 97], [154, 132], [0, 1]], ![[0, 1], [0, 128], [40, 102], [174, 173], [154, 108], [25, 96], [126, 61], [146, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [42, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [147, 47, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19168, 6329, -4556]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2696, 3857, -4556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-71, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-71, 1, 0]] 
 ![![193, 0, 0], ![122, 1, 0], ![170, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-71, 1, 0], ![2, -72, 4], ![152, -26, -69]]]
  hmulB := by decide  
  f := ![![![21462, -938671, 52152], ![-12545, -2516334, 0]], ![![13572, -593311, 32964], ![-7912, -1590513, 0]], ![![18858, -826808, 45937], ![-11176, -2216460, 0]]]
  g := ![![![1, 0, 0], ![-122, 193, 0], ![-170, 0, 193]], ![![-1, 1, 0], ![42, -72, 4], ![78, -26, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![110, -31, 1]] ![![193, 0, 0], ![-71, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-13703, 193, 0]], ![![21230, -5983, 193], ![-7720, 2316, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-71, 1, 0]]], ![![![110, -31, 1]], ![![-40, 12, -1]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB253I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB253I3 : PrimesBelowBoundCertificateInterval O 137 193 253 where
  m := 11
  g := ![2, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB253I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![151, 22801]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N0, I149N1, I149N2, I151N0, I157N1, I163N1, I167N1, I173N1, I179N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [I151N0], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
