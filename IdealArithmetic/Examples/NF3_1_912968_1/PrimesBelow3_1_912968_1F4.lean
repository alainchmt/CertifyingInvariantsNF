
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [137, 23, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 48, 23], [1, 148, 174], [0, 1]]
 g := ![![[146, 93, 174], [106, 55], [59, 120, 61], [173, 63], [155, 43], [62, 178], [1]], ![[165, 118, 0, 188], [112, 133], [73, 61, 135, 191], [135, 161], [182, 90], [123, 114], [94, 79, 97, 150]], ![[142, 56, 51, 6], [23, 155], [172, 4, 138, 40], [137, 187], [156, 97], [182, 93], [22, 123, 89, 47]]]
 h' := ![![[92, 48, 23], [92, 181, 78], [191, 106, 152], [31, 17, 109], [17, 157, 76], [31, 190, 162], [60, 174, 93], [0, 1]], ![[1, 148, 174], [29, 83, 144], [106, 13, 112], [167, 63, 172], [185, 172, 84], [10, 7, 175], [71, 191, 36], [92, 48, 23]], ![[0, 1], [98, 130, 172], [57, 78, 130], [104, 117, 113], [54, 65, 37], [100, 0, 57], [139, 29, 68], [1, 148, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 62], []]
 b := ![[], [125, 105, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [137, 23, 104, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122928, 591, 1182]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-624, 3, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-18, -54, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-18, -54, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![181, 145, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-18, -54, 1], ![135, 7, -107], ![-10099, -1243, -47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-181, -145, 199]], ![![-1, -1, 1], ![98, 78, -107], ![-8, 28, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [93, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 198], [0, 1]]
 g := ![![[42, 124], [129, 33], [54, 157], [70], [80], [100], [74, 1]], ![[64, 75], [183, 166], [130, 42], [70], [80], [100], [148, 198]]]
 h' := ![![[74, 198], [142, 129], [152, 86], [187, 117], [54, 95], [176, 105], [83, 10], [0, 1]], ![[0, 1], [136, 70], [148, 113], [89, 82], [119, 104], [185, 94], [27, 189], [74, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182]]
 b := ![[], [16, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [93, 125, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-754, 1917, 1258]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1148, -907, 1258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-92, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-92, 1, 0]] 
 ![![199, 0, 0], ![107, 1, 0], ![47, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-92, 1, 0], ![1, -92, 2], ![189, 25, -91]]]
  hmulB := by decide  
  f := ![![![-4210, 607450, -13206], ![5174, 1313997, 0]], ![![-2261, 326586, -7100], ![2787, 706450, 0]], ![![-986, 143468, -3119], ![1240, 310341, 0]]]
  g := ![![![1, 0, 0], ![-107, 199, 0], ![-47, 0, 199]], ![![-1, 1, 0], ![49, -92, 2], ![9, 25, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-18, -54, 1]] ![![199, 0, 0], ![-92, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-18308, 199, 0]], ![![-3582, -10746, 199], ![1791, 4975, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-92, 1, 0]]], ![![![-18, -54, 1]], ![![9, 25, -1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1183105905540, 271869651709, 60801784436]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![1183105905540, 271869651709, 60801784436]] 
 ![![211, 0, 0], ![0, 211, 0], ![142, 197, 1]] where
  M :=![![![1183105905540, 271869651709, 60801784436], ![11763406910113, 2703150516440, 604541087854], ![57889155107653, 13302532227377, 2975020168149]]]
  hmulB := by decide  
  f := ![![![-1289618, 220321, -18414]], ![![-3259925, -1749968, 422228]], ![![-3723510, -1468817, 374571]]]
  g := ![![![-35311599452, -55479061053, 60801784436], ![-351096813105, -551618217018, 604541087854], ![-1727790088955, -2714580288616, 2975020168149]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [4, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 210], [0, 1]]
 g := ![![[14, 53], [204, 79], [180], [65], [52, 150], [34], [155, 1]], ![[0, 158], [0, 132], [180], [65], [92, 61], [34], [99, 210]]]
 h' := ![![[155, 210], [28, 106], [36, 76], [171, 179], [3, 109], [33, 192], [13, 178], [0, 1]], ![[0, 1], [0, 105], [0, 135], [64, 32], [18, 102], [42, 19], [173, 33], [155, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [20, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [4, 56, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![441734, 462718, 113654]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74394, -103920, 113654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1289618, 220321, -18414]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-1289618, 220321, -18414]] 
 ![![211, 0, 0], ![27, 1, 0], ![58, 0, 1]] where
  M :=![![![-1289618, 220321, -18414], ![-3259925, -1749968, 422228], ![39670371, 3537727, -1529647]]]
  hmulB := by decide  
  f := ![![![1183105905540, 271869651709, 60801784436]], ![![207143442463, 47600147453, 10645446766]], ![![599570130943, 137777118609, 30812908367]]]
  g := ![![![-29243, 220321, -18414], ![92417, -1749968, 422228], ![155788, 3537727, -1529647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![1183105905540, 271869651709, 60801784436]] ![![-1289618, 220321, -18414]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7834020837050, -15361257333, -156985804662]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![7834020837050, -15361257333, -156985804662]] 
 ![![223, 0, 0], ![118, 1, 0], ![63, 0, 1]] where
  M :=![![![7834020837050, -15361257333, -156985804662], ![-29685678338451, 3909375720500, -187708319328], ![-19700758734771, -17181512532159, 3894014463167]]]
  hmulB := by decide  
  f := ![![![-11998052756656375895554348, -2757070528398349904278869, -616599929005520854603224]], ![![-6883698127335848193272203, -1581826786245738502087630, -353764720217281082988078]], ![![-6022151775516728900319171, -1383849322433387995601280, -309488417208702067286623]]]
  g := ![![![87608766350, -15361257333, -156985804662], ![-2148728202869, 3909375720500, -187708319328], ![7903115734890, -17181512532159, 3894014463167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48917386, -11240881, -2513946]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-48917386, -11240881, -2513946]] 
 ![![223, 0, 0], ![158, 1, 0], ![118, 0, 1]] where
  M :=![![![-48917386, -11240881, -2513946], ![-486376675, -111766036, -24995708], ![-2393518731, -550014247, -123006917]]]
  hmulB := by decide  
  f := ![![![180864, -14785, -692]], ![![127493, -9742, -626]], ![![82841, -9813, 301]]]
  g := ![![![9075280, -11240881, -2513946], ![90233859, -111766036, -24995708], ![444051787, -550014247, -123006917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42292778805494847, -9718591539282040, -2173496394608426]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-42292778805494847, -9718591539282040, -2173496394608426]] 
 ![![223, 0, 0], ![169, 1, 0], ![215, 0, 1]] where
  M :=![![![-42292778805494847, -9718591539282040, -2173496394608426], ![-420509410120274554, -96630188670705497, -21610679473172506], ![-2069377915147407142, -475528902705152582, -106348780209987537]]]
  hmulB := by decide  
  f := ![![![-7030080397, -144920452, 173125482]], ![![-5181649289, -121943945, 130679332]], ![![-6817635983, -72899022, 154148497]]]
  g := ![![![9271080341587361, -9718591539282040, -2173496394608426], ![92180666197134723, -96630188670705497, -21610679473172506], ![453632261825877577, -475528902705152582, -106348780209987537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![7834020837050, -15361257333, -156985804662]] ![![-48917386, -11240881, -2513946]]
  ![![7030080397, 144920452, -173125482]] where
 M := ![![![7030080397, 144920452, -173125482]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![7030080397, 144920452, -173125482]] ![![-42292778805494847, -9718591539282040, -2173496394608426]]
  ![![223, 0, 0]] where
 M := ![![![-223, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [99, 118, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [220, 7, 130], [206, 219, 97], [0, 1]]
 g := ![![[23, 157, 173], [27, 177, 172], [24, 134], [136, 196], [186, 74], [198, 92, 103], [1]], ![[193, 131, 125, 149], [150, 122, 82, 148], [155, 219], [81, 203], [172, 167], [34, 129, 59, 39], [166, 74, 191, 94]], ![[127, 78, 79, 73], [87, 53, 73, 75], [102, 131], [30, 167], [65, 221], [109, 152, 38, 90], [122, 205, 184, 133]]]
 h' := ![![[220, 7, 130], [51, 119, 207], [202, 135, 95], [218, 44, 208], [17, 136, 14], [147, 29, 172], [128, 109, 199], [0, 1]], ![[206, 219, 97], [173, 56, 194], [112, 39, 219], [193, 126, 197], [99, 202, 89], [130, 166, 124], [21, 220, 93], [220, 7, 130]], ![[0, 1], [165, 52, 53], [221, 53, 140], [176, 57, 49], [167, 116, 124], [84, 32, 158], [226, 125, 162], [206, 219, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 149], []]
 b := ![[], [58, 68, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [99, 118, 28, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2485423, -563641, -74229]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10949, -2483, -327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [225, 156, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [190, 61, 40], [164, 167, 189], [0, 1]]
 g := ![![[162, 23, 176], [191, 62], [84, 85, 43], [156, 204], [177, 43], [135, 143, 53], [1]], ![[11, 210, 47, 8], [136, 5], [45, 194, 167, 106], [129, 25], [50, 15], [88, 47, 37, 7], [6, 161, 23, 109]], ![[2, 173, 141, 84], [225, 85], [4, 144, 221, 18], [197, 146], [50, 5], [0, 132, 65, 170], [153, 193, 215, 120]]]
 h' := ![![[190, 61, 40], [76, 112, 136], [107, 160, 156], [219, 46, 57], [104, 1, 152], [82, 138, 172], [4, 73, 125], [0, 1]], ![[164, 167, 189], [90, 107, 170], [227, 113, 163], [9, 43, 138], [167, 21, 5], [215, 189, 123], [16, 45, 208], [190, 61, 40]], ![[0, 1], [135, 10, 152], [193, 185, 139], [118, 140, 34], [186, 207, 72], [131, 131, 163], [100, 111, 125], [164, 167, 189]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 131], []]
 b := ![[], [207, 64, 220], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [225, 156, 104, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122973, 458, 916]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-537, 2, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![38, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![38, 1, 0]] 
 ![![233, 0, 0], ![38, 1, 0], ![94, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![38, 1, 0], ![1, 38, 2], ![189, 25, 39]]]
  hmulB := by decide  
  f := ![![![-7163, -286662, -15088], ![-2330, 1757752, 0]], ![![-1192, -46739, -2460], ![-232, 286590, 0]], ![![-2888, -115649, -6087], ![-951, 709136, 0]]]
  g := ![![![1, 0, 0], ![-38, 233, 0], ![-94, 0, 233]], ![![0, 1, 0], ![-7, 38, 2], ![-19, 25, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![80, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![80, 1, 0]] 
 ![![233, 0, 0], ![80, 1, 0], ![179, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![80, 1, 0], ![1, 80, 2], ![189, 25, 81]]]
  hmulB := by decide  
  f := ![![![887, 96476, 2412], ![932, -280998, 0]], ![![254, 33118, 828], ![467, -96462, 0]], ![![701, 74117, 1853], ![659, -215874, 0]]]
  g := ![![![1, 0, 0], ![-80, 233, 0], ![-179, 0, 233]], ![![0, 1, 0], ![-29, 80, 2], ![-70, 25, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![114, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![114, 1, 0]] 
 ![![233, 0, 0], ![114, 1, 0], ![143, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![114, 1, 0], ![1, 114, 2], ![189, 25, 115]]]
  hmulB := by decide  
  f := ![![![-20339, -3774200, -66216], ![-26096, 7714164, 0]], ![![-10042, -1846518, -32396], ![-12581, 3774134, 0]], ![![-12539, -2316355, -40639], ![-15901, 4734444, 0]]]
  g := ![![![1, 0, 0], ![-114, 233, 0], ![-143, 0, 233]], ![![0, 1, 0], ![-57, 114, 2], ![-82, 25, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![38, 1, 0]] ![![233, 0, 0], ![80, 1, 0]]
  ![![233, 0, 0], ![6, 59, 1]] where
 M := ![![![54289, 0, 0], ![18640, 233, 0]], ![![8854, 233, 0], ![3041, 118, 2]]]
 hmul := by decide  
 g := ![![![![227, -59, -1], ![233, 0, 0]], ![![74, -58, -1], ![233, 0, 0]]], ![![![32, -58, -1], ![233, 0, 0]], ![![13, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![6, 59, 1]] ![![233, 0, 0], ![114, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![26562, 233, 0]], ![![1398, 13747, 233], ![932, 6757, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![114, 1, 0]]], ![![![6, 59, 1]], ![![4, 29, 1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [146, 32, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 96, 160], [80, 142, 79], [0, 1]]
 g := ![![[37, 15, 54], [195, 85, 29], [88, 152, 64], [2, 15, 72], [196, 66], [186, 72, 33], [1]], ![[204, 200, 74, 4], [33, 144, 211, 170], [184, 155, 98, 121], [67, 0, 29, 27], [157, 83], [218, 35, 100, 144], [17, 28, 171, 18]], ![[26, 104, 87, 223], [124, 56, 127, 229], [133, 57, 108, 171], [199, 227, 106, 92], [116, 11], [115, 84, 161, 104], [181, 64, 226, 221]]]
 h' := ![![[95, 96, 160], [210, 10, 66], [58, 28, 56], [186, 146, 8], [38, 159, 116], [90, 72, 117], [93, 207, 175], [0, 1]], ![[80, 142, 79], [215, 79, 217], [178, 14, 4], [36, 11, 118], [185, 165, 87], [138, 190, 171], [229, 223, 132], [95, 96, 160]], ![[0, 1], [148, 150, 195], [234, 197, 179], [65, 82, 113], [220, 154, 36], [172, 216, 190], [165, 48, 171], [80, 142, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 118], []]
 b := ![[], [133, 87, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [146, 32, 64, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7986424, 1837671, 399847]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33416, 7689, 1673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [158, 10, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [239, 157, 182], [90, 83, 59], [0, 1]]
 g := ![![[180, 138, 120], [160, 29], [217, 113], [2, 174], [152, 215, 231], [71, 92, 32], [1]], ![[94, 233, 143, 122], [143, 60], [19, 239], [207, 82], [101, 57, 104, 27], [162, 189, 10, 194], [150, 15, 230, 194]], ![[36, 193, 10, 180], [34, 226], [87, 143], [170, 1], [237, 10, 4, 214], [189, 161, 57, 214], [81, 69, 172, 47]]]
 h' := ![![[239, 157, 182], [25, 84, 222], [0, 13, 149], [233, 28, 63], [84, 9, 167], [109, 78, 58], [83, 231, 88], [0, 1]], ![[90, 83, 59], [0, 220, 215], [121, 44, 32], [58, 45, 203], [179, 32, 75], [138, 119, 212], [151, 183, 182], [239, 157, 182]], ![[0, 1], [225, 178, 45], [160, 184, 60], [13, 168, 216], [134, 200, 240], [169, 44, 212], [191, 68, 212], [90, 83, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [228, 216], []]
 b := ![[], [57, 237, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [158, 10, 153, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-590450, -27474, 27474]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2450, -114, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9586902490, 2203004675, 492686898]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![9586902490, 2203004675, 492686898]] 
 ![![251, 0, 0], ![0, 251, 0], ![80, 7, 1]] where
  M :=![![![9586902490, 2203004675, 492686898], ![95320828397, 21904074940, 4898696248], ![469085381661, 107792614961, 24107079615]]]
  hmulB := by decide  
  f := ![![![-211228, 5103, 3280]], ![![625023, -129228, 13486]], ![![-44652, -71, 927]]]
  g := ![![![-118836850, -4963361, 492686898], ![-1181573193, -49349796, 4898696248], ![-5814665289, -242856344, 24107079615]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [196, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [244, 250], [0, 1]]
 g := ![![[9, 73], [162, 63], [119], [90, 23], [0, 51], [79, 23], [244, 1]], ![[0, 178], [223, 188], [119], [180, 228], [145, 200], [169, 228], [237, 250]]]
 h' := ![![[244, 250], [125, 233], [150, 125], [181, 133], [0, 104], [78, 94], [117, 104], [0, 1]], ![[0, 1], [0, 18], [28, 126], [3, 118], [25, 147], [173, 157], [142, 147], [244, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195]]
 b := ![[], [153, 223]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [196, 7, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3439, 1923, 454]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -5, 454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211228, -5103, -3280]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![211228, -5103, -3280]] 
 ![![251, 0, 0], ![236, 1, 0], ![139, 0, 1]] where
  M :=![![![211228, -5103, -3280], ![-625023, 129228, -13486], ![-1315427, -478535, 124125]]]
  hmulB := by decide  
  f := ![![![-9586902490, -2203004675, -492686898]], ![![-9393744287, -2158618240, -482760176]], ![![-7177947521, -1649443286, -368886687]]]
  g := ![![![7456, -5103, -3280], ![-116527, 129228, -13486], ![375958, -478535, 124125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![9586902490, 2203004675, 492686898]] ![![211228, -5103, -3280]]
  ![![251, 0, 0]] where
 M := ![![![-251, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [187, 0, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 148, 150], [230, 108, 107], [0, 1]]
 g := ![![[48, 111, 44], [143, 225], [139, 57], [80, 57], [122, 120], [93, 241], [249, 1], []], ![[123, 77, 251, 233], [1, 215], [164, 234], [246, 67], [227, 122], [223, 241], [29, 99], [96, 141]], ![[86, 33, 204, 80], [65, 222], [7, 81], [212, 59], [220, 81], [], [240, 59], [139, 141]]]
 h' := ![![[19, 148, 150], [49, 252, 185], [24, 159, 15], [46, 112, 91], [10, 243, 91], [145, 150, 67], [211, 70, 64], [0, 0, 1], [0, 1]], ![[230, 108, 107], [10, 100, 212], [35, 227, 27], [190, 180, 157], [73, 36, 18], [173, 173, 181], [92, 190, 193], [142, 74, 108], [19, 148, 150]], ![[0, 1], [146, 162, 117], [215, 128, 215], [204, 222, 9], [229, 235, 148], [121, 191, 9], [11, 254], [179, 183, 148], [230, 108, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149, 140], []]
 b := ![[], [35, 245, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [187, 0, 8, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2880713, -687475, -109225]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11209, -2675, -425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB271I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB271I4 : PrimesBelowBoundCertificateInterval O 193 257 271 where
  m := 11
  g := ![1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB271I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
    · exact ![I257N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![233, 233, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![63001, 251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I199N1, I211N1, I223N0, I223N1, I223N2, I233N0, I233N1, I233N2, I251N1]
  Il := ![[], [I199N1], [I211N1], [I223N0, I223N1, I223N2], [], [], [I233N0, I233N1, I233N2], [], [], [I251N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
