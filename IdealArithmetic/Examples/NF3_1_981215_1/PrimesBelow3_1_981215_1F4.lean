
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [66, 105, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 151, 188], [100, 45, 9], [0, 1]]
 g := ![![[136, 119, 47], [143, 173], [1, 29, 116], [135, 155], [131, 43], [191, 121], [1]], ![[84, 19, 162, 26], [106, 161], [21, 182, 89, 174], [23, 76], [48, 193], [182, 181], [18, 3, 190, 59]], ![[13, 76, 185, 150], [153, 51], [55, 149, 146, 157], [44, 182], [93, 49], [32, 55], [193, 101, 158, 138]]]
 h' := ![![[86, 151, 188], [40, 184, 21], [131, 164, 166], [4, 30, 71], [7, 99, 67], [24, 3, 35], [131, 92, 186], [0, 1]], ![[100, 45, 9], [34, 177, 77], [23, 10, 84], [49, 161, 167], [155, 116, 154], [34, 14, 169], [134, 88, 56], [86, 151, 188]], ![[0, 1], [93, 33, 99], [12, 23, 144], [8, 6, 156], [96, 179, 173], [18, 180, 190], [95, 17, 152], [100, 45, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 44], []]
 b := ![[], [37, 111, 180], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [66, 105, 11, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3347424, 298455, -212366]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16992, 1515, -1078]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5257092905, 339622974, 295133890]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![5257092905, 339622974, 295133890]] 
 ![![199, 0, 0], ![0, 199, 0], ![141, 23, 1]] where
  M :=![![![5257092905, 339622974, 295133890], ![56030950016, 3619756817, 3145584934], ![39486473494, 2550937144, 2216775837]]]
  hmulB := by decide  
  f := ![![![-28933, 4678, -2786]], ![![-536804, 10175, 57030]], ![![-76849, 4013, 4537]]]
  g := ![![![-182697415, -32404304, 295133890], ![-1947218722, -345370335, 3145584934], ![-1372255877, -243391493, 2216775837]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [7, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 198], [0, 1]]
 g := ![![[122, 57], [38, 114], [73, 193], [45], [131], [79], [141, 1]], ![[0, 142], [192, 85], [23, 6], [45], [131], [79], [83, 198]]]
 h' := ![![[141, 198], [132, 16], [86, 78], [84, 118], [1, 170], [108, 176], [8, 173], [0, 1]], ![[0, 1], [0, 183], [139, 121], [6, 81], [91, 29], [49, 23], [123, 26], [141, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [196, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [7, 58, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14914, 16420, -6900]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4814, 880, -6900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28933, -4678, 2786]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![28933, -4678, 2786]] 
 ![![199, 0, 0], ![147, 1, 0], ![112, 0, 1]] where
  M :=![![![28933, -4678, 2786], ![536804, -10175, -57030], ![-1133094, 95036, 16001]]]
  hmulB := by decide  
  f := ![![![-5257092905, -339622974, -295133890]], ![![-4164942749, -269067005, -233820436]], ![![-3157190346, -203963368, -177245083]]]
  g := ![![![2033, -4678, 2786], ![42311, -10175, -57030], ![-84902, 95036, 16001]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![5257092905, 339622974, 295133890]] ![![28933, -4678, 2786]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229408, 5877, -38882]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![229408, 5877, -38882]] 
 ![![211, 0, 0], ![0, 211, 0], ![141, 26, 1]] where
  M :=![![![229408, 5877, -38882], ![-7432339, 596977, 142411], ![4466359, -791651, 528710]]]
  hmulB := by decide  
  f := ![![![-2030177821, -131155192, -113974451]], ![![-21637964949, -1397873338, -1214758210]], ![![-4095218011, -264562591, -229906080]]]
  g := ![![![27070, 4819, -38882], ![-130390, -14719, 142411], ![-332141, -68901, 528710]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [55, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 210], [0, 1]]
 g := ![![[83, 188], [196, 55], [201], [194], [150, 5], [101], [77, 1]], ![[0, 23], [0, 156], [201], [194], [113, 206], [101], [154, 210]]]
 h' := ![![[77, 210], [192, 140], [201, 107], [110, 74], [190, 163], [156, 146], [196, 177], [0, 1]], ![[0, 1], [0, 71], [0, 104], [111, 137], [81, 48], [4, 65], [110, 34], [77, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [24, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [55, 134, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402984, 21867, -27084]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24748, 3441, -27084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2030177821, 131155192, 113974451]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![2030177821, 131155192, 113974451]] 
 ![![211, 0, 0], ![138, 1, 0], ![130, 0, 1]] where
  M :=![![![2030177821, 131155192, 113974451], ![21637964949, 1397873338, 1214758210], ![15248838886, 985117841, 856071829]]]
  hmulB := by decide  
  f := ![![![-229408, -5877, 38882]], ![![-114815, -6673, 24755]], ![![-162509, 131, 21450]]]
  g := ![![![-146378755, 131155192, 113974451], ![-1560128545, 1397873338, 1214758210], ![-1099463322, 985117841, 856071829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![229408, 5877, -38882]] ![![2030177821, 131155192, 113974451]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-729157000, 77675316, -13143125]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-729157000, 77675316, -13143125]] 
 ![![223, 0, 0], ![0, 223, 0], ![44, 213, 1]] where
  M :=![![![-729157000, 77675316, -13143125], ![-2588012191, -377842927, 880714726], ![15966294106, -948797219, -779362632]]]
  hmulB := by decide  
  f := ![![![5067696595652246, 327387440215969, 284501156179267]], ![![54012333390024028, 3489348510686750, 3032259530017125]], ![![52760850062482735, 3408499171081806, 2962001090723415]]]
  g := ![![![-676500, 12902067, -13143125], ![-185378745, -842915155, 880714726], ![225373318, 740158939, -779362632]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [93, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 222], [0, 1]]
 g := ![![[120, 153], [38, 74], [70, 211], [159, 31], [64, 203], [49], [213, 1]], ![[151, 70], [190, 149], [190, 12], [72, 192], [41, 20], [49], [203, 222]]]
 h' := ![![[213, 222], [34, 162], [180, 48], [154, 65], [69, 186], [9, 42], [38, 7], [0, 1]], ![[0, 1], [198, 61], [146, 175], [173, 158], [216, 37], [35, 181], [191, 216], [213, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [205, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [93, 10, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2413, 15459, -9061]
  a := ![3, -7, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1777, 8724, -9061]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5067696595652246, 327387440215969, 284501156179267]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![5067696595652246, 327387440215969, 284501156179267]] 
 ![![223, 0, 0], ![112, 1, 0], ![167, 0, 1]] where
  M :=![![![5067696595652246, 327387440215969, 284501156179267], ![54012333390024028, 3489348510686750, 3032259530017125], ![38063901649833117, 2459035005462352, 2136912465786172]]]
  hmulB := by decide  
  f := ![![![-729157000, 77675316, -13143125]], ![![-377818817, 37317455, -2651638]], ![![-474452578, 53914711, -13337509]]]
  g := ![![![-354759595472977, 327387440215969, 284501156179267], ![-3781085387084089, 3489348510686750, 3032259530017125], ![-2664629599767897, 2459035005462352, 2136912465786172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-729157000, 77675316, -13143125]] ![![5067696595652246, 327387440215969, 284501156179267]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -3, 10]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-44, -3, 10]] 
 ![![227, 0, 0], ![0, 227, 0], ![41, 204, 1]] where
  M :=![![![-44, -3, 10], ![1913, -143, -53], ![-1433, 217, -118]]]
  hmulB := by decide  
  f := ![![![-125, -8, -7]], ![![-1329, -86, -74]], ![![-1221, -79, -68]]]
  g := ![![![-2, -9, 10], ![18, 47, -53], ![15, 107, -118]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [171, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 226], [0, 1]]
 g := ![![[106, 77], [204, 221], [132], [136], [173], [169, 27], [34, 1]], ![[0, 150], [0, 6], [132], [136], [173], [179, 200], [68, 226]]]
 h' := ![![[34, 226], [74, 118], [151, 69], [93, 141], [60, 131], [157, 20], [88, 77], [0, 1]], ![[0, 1], [0, 109], [0, 158], [120, 86], [201, 96], [156, 207], [209, 150], [34, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [128, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [171, 193, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6751, 775, -3113]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![592, 2801, -3113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, 8, 7]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![125, 8, 7]] 
 ![![227, 0, 0], ![28, 1, 0], ![148, 0, 1]] where
  M :=![![![125, 8, 7], ![1329, 86, 74], ![926, 61, 53]]]
  hmulB := by decide  
  f := ![![![44, 3, -10]], ![![-3, 1, -1]], ![![35, 1, -6]]]
  g := ![![![-5, 8, 7], ![-53, 86, 74], ![-38, 61, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-44, -3, 10]] ![![125, 8, 7]]
  ![![227, 0, 0]] where
 M := ![![![-227, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26950, 1741, 1513]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![26950, 1741, 1513]] 
 ![![229, 0, 0], ![0, 229, 0], ![184, 29, 1]] where
  M :=![![![26950, 1741, 1513], ![287242, 18556, 16125], ![202413, 13078, 11364]]]
  hmulB := by decide  
  f := ![![![-54, 10, -7]], ![![-1347, 39, 124]], ![![-203, 12, 10]]]
  g := ![![![-1098, -184, 1513], ![-11702, -1961, 16125], ![-8247, -1382, 11364]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [11, 188, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 228], [0, 1]]
 g := ![![[142, 125], [169], [47, 56], [94], [214], [184, 138], [41, 1]], ![[0, 104], [169], [53, 173], [94], [214], [117, 91], [82, 228]]]
 h' := ![![[41, 228], [19, 128], [170, 13], [63, 133], [160, 95], [37, 121], [7, 67], [0, 1]], ![[0, 1], [0, 101], [16, 216], [20, 96], [162, 134], [189, 108], [6, 162], [41, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [210, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [11, 188, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92343, 3633, 5795]
  a := ![-1, 23, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4253, -718, 5795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, 10, -7]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-54, 10, -7]] 
 ![![229, 0, 0], ![141, 1, 0], ![111, 0, 1]] where
  M :=![![![-54, 10, -7], ![-1347, 39, 124], ![2512, -223, -18]]]
  hmulB := by decide  
  f := ![![![26950, 1741, 1513]], ![![17848, 1153, 1002]], ![![13947, 901, 783]]]
  g := ![![![-3, 10, -7], ![-90, 39, 124], ![157, -223, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![26950, 1741, 1513]] ![![-54, 10, -7]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [1, 144, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 19, 161], [178, 213, 72], [0, 1]]
 g := ![![[205, 20, 55], [143, 91], [24, 169], [183, 142, 208], [46, 58], [109, 209, 30], [1]], ![[212, 114, 45, 120], [150, 92], [92, 18], [137, 52, 207, 38], [21, 66], [35, 193, 50, 148], [207, 80, 24, 18]], ![[128, 198, 36, 4], [130, 170], [153, 81], [94, 214, 142, 187], [61, 104], [138, 153, 4, 38], [162, 189, 35, 215]]]
 h' := ![![[28, 19, 161], [203, 194, 145], [146, 109, 215], [50, 42, 13], [185, 107, 212], [124, 173, 72], [232, 89, 206], [0, 1]], ![[178, 213, 72], [68, 36, 141], [190, 170, 201], [7, 61, 211], [60, 87, 172], [224, 173, 84], [76, 121, 190], [28, 19, 161]], ![[0, 1], [96, 3, 180], [172, 187, 50], [32, 130, 9], [43, 39, 82], [77, 120, 77], [58, 23, 70], [178, 213, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 102], []]
 b := ![[], [46, 45, 215], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [1, 144, 27, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7013999, 608596, -28193]
  a := ![1, -1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30103, 2612, -121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421756358568360733, 27246645891343554, 23677457672110815]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![421756358568360733, 27246645891343554, 23677457672110815]] 
 ![![239, 0, 0], ![0, 239, 0], ![158, 62, 1]] where
  M :=![![![421756358568360733, 27246645891343554, 23677457672110815], ![4495147769481822111, 290399177193394060, 252358189460557464], ![3167848005445088724, 204651882748013499, 177843405408787105]]]
  hmulB := by decide  
  f := ![![![517884476, -44168115, -6275196]], ![![-1154394321, 441856895, -473298873]], ![![9861323, 86589329, -124182380]]]
  g := ![![![-13888209010983883, -6028266651797184, 23677457672110815], ![-148022787302452959, -64250245060088572, 252358189460557464], ![-104315523218172694, -45278825324672749, 177843405408787105]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [40, 206, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 238], [0, 1]]
 g := ![![[41, 6], [185, 132], [229, 51], [13, 101], [160], [223, 45], [33, 1]], ![[0, 233], [0, 107], [0, 188], [0, 138], [160], [35, 194], [66, 238]]]
 h' := ![![[33, 238], [9, 217], [161, 111], [197, 23], [7, 36], [162, 152], [114, 93], [0, 1]], ![[0, 1], [0, 22], [0, 128], [0, 216], [0, 203], [159, 87], [76, 146], [33, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [105, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [40, 206, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16787, 7985, 495]
  a := ![-2, 7, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257, -95, 495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![517884476, -44168115, -6275196]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![517884476, -44168115, -6275196]] 
 ![![239, 0, 0], ![37, 1, 0], ![213, 0, 1]] where
  M :=![![![517884476, -44168115, -6275196], ![-1154394321, 441856895, -473298873], ![-7896443109, 278284311, 656422274]]]
  hmulB := by decide  
  f := ![![![421756358568360733, 27246645891343554, 23677457672110815]], ![![84100975048163888, 5433159310347722, 4721439846563421]], ![![389129507868225627, 25138859655247659, 21845781964721300]]]
  g := ![![![14597161, -44168115, -6275196], ![348575567, 441856895, -473298873], ![-661133502, 278284311, 656422274]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![421756358568360733, 27246645891343554, 23677457672110815]] ![![517884476, -44168115, -6275196]]
  ![![239, 0, 0]] where
 M := ![![![239, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3053773040, 328919951, -60165635]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-3053773040, 328919951, -60165635]] 
 ![![241, 0, 0], ![0, 241, 0], ![202, 194, 1]] where
  M :=![![![-3053773040, 328919951, -60165635], ![-11820556236, -1525522472, 3738450731], ![67997955251, -4103426624, -3230287862]]]
  hmulB := by decide  
  f := ![![![-84100975048163888, -5433159310347722, -4721439846563421]], ![![-896361851383265689, -57907494360136265, -50321872720698100]], ![![-794665086014749418, -51337597551237555, -44612602881643998]]]
  g := ![![![37758030, 49796901, -60165635], ![-3182521178, -3015705246, 3738450731], ![2989693375, 2583288044, -3230287862]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [62, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 240], [0, 1]]
 g := ![![[29, 119], [166], [53], [54], [171, 201], [188, 60], [130, 1]], ![[75, 122], [166], [53], [54], [32, 40], [35, 181], [19, 240]]]
 h' := ![![[130, 240], [165, 100], [24, 155], [30, 189], [2, 160], [153, 116], [134, 209], [0, 1]], ![[0, 1], [151, 141], [171, 86], [18, 52], [76, 81], [50, 125], [71, 32], [130, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [79, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [62, 111, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7437, -455, -580]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![517, 465, -580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84100975048163888, 5433159310347722, 4721439846563421]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![84100975048163888, 5433159310347722, 4721439846563421]] 
 ![![241, 0, 0], ![37, 1, 0], ![194, 0, 1]] where
  M :=![![![84100975048163888, 5433159310347722, 4721439846563421], ![896361851383265689, 57907494360136265, 50321872720698100], ![631689601471960696, 40808923291575501, 35463137654961076]]]
  hmulB := by decide  
  f := ![![![3053773040, -328919951, 60165635]], ![![517884476, -44168115, -6275196]], ![![2176074749, -247747070, 61835772]]]
  g := ![![![-4285830911485500, 5433159310347722, 4721439846563421], ![-45679081940901276, 57907494360136265, 50321872720698100], ![-32191241765057185, 40808923291575501, 35463137654961076]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-3053773040, 328919951, -60165635]] ![![84100975048163888, 5433159310347722, 4721439846563421]]
  ![![241, 0, 0]] where
 M := ![![![-241, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1300, 84, 73]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![1300, 84, 73]] 
 ![![251, 0, 0], ![41, 1, 0], ![201, 0, 1]] where
  M :=![![![1300, 84, 73], ![13859, 895, 778], ![9766, 631, 548]]]
  hmulB := by decide  
  f := ![![![-458, 31, 17]], ![![-62, 3, 4]], ![![-349, 25, 11]]]
  g := ![![![-67, 84, 73], ![-714, 895, 778], ![-503, 631, 548]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9529370, -3665784, 3933007]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![9529370, -3665784, 3933007]] 
 ![![251, 0, 0], ![49, 1, 0], ![179, 0, 1]] where
  M :=![![![9529370, -3665784, 3933007], ![754870121, -36865045, -48189638], ![-1038403346, 107719189, -14603118]]]
  hmulB := by decide  
  f := ![![![-5729293325773892, -370128448056811, -321643283986507]], ![![-1361749449228234, -87972840911751, -76448793928250]], ![![-4257277754858717, -275032105838253, -239004135423717]]]
  g := ![![![-2051217, -3665784, 3933007], ![44570528, -36865045, -48189638], ![-14751735, 107719189, -14603118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2088243195603, 134906378362, 117234248799]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![2088243195603, 134906378362, 117234248799]] 
 ![![251, 0, 0], ![160, 1, 0], ![139, 0, 1]] where
  M :=![![![2088243195603, 134906378362, 117234248799], ![22256835142247, 1437854091498, 1249501664384], ![15684972870428, 1013293321923, 880556448487]]]
  hmulB := by decide  
  f := ![![![6173094, -1317817, 1048106]], ![![4737853, -868781, 602011]], ![![2056653, -603196, 582114]]]
  g := ![![![-142598955878, 134906378362, 117234248799], ![-1519842832059, 1437854091498, 1249501664384], ![-1071072928195, 1013293321923, 880556448487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![1300, 84, 73]] ![![9529370, -3665784, 3933007]]
  ![![-6173094, 1317817, -1048106]] where
 M := ![![![-6173094, 1317817, -1048106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-6173094, 1317817, -1048106]] ![![2088243195603, 134906378362, 117234248799]]
  ![![251, 0, 0]] where
 M := ![![![-251, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![192417, -140716, 174057]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![192417, -140716, 174057]] 
 ![![257, 0, 0], ![72, 1, 0], ![23, 0, 1]] where
  M :=![![![192417, -140716, 174057], ![33385603, -1796244, -1895990], ![-41845658, 4573527, -918607]]]
  hmulB := by decide  
  f := ![![![-10321403768838, -666791686427, -579444970748]], ![![-3319643070361, -214458270483, -186365200401]], ![![-1225358876679, -79161626670, -68791809172]]]
  g := ![![![24594, -140716, 174057], ![802813, -1796244, -1895990], ![-1361913, 4573527, -918607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N0)

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := prime_ideal_of_norm_prime hp257.out _ NI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13779577052241430, -890199397939963, -773587275605124]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-13779577052241430, -890199397939963, -773587275605124]] 
 ![![257, 0, 0], ![187, 1, 0], ![181, 0, 1]] where
  M :=![![![-13779577052241430, -890199397939963, -773587275605124], ![-146864970242638721, -9487889765615203, -8245018826129345], ![-103499579304492269, -6686363655037689, -5810480051520512]]]
  hmulB := by decide  
  f := ![![![-1289660231, 137502620, -23414063]], ![![-956327050, 97457448, -10969155]], ![![-798256389, 90294099, -21849410]]]
  g := ![![![1138937771389335, -890199397939963, -773587275605124], ![12138983748859205, -9487889765615203, -8245018826129345], ![8554658807442678, -6686363655037689, -5810480051520512]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, -8, 24]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![-95, -8, 24]] 
 ![![257, 0, 0], ![254, 1, 0], ![70, 0, 1]] where
  M :=![![![-95, -8, 24], ![4592, -335, -136], ![-3592, 528, -271]]]
  hmulB := by decide  
  f := ![![![162593, 10504, 9128]], ![![167438, 10817, 9400]], ![![49038, 3168, 2753]]]
  g := ![![![1, -8, 24], ![386, -335, -136], ![-462, 528, -271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![192417, -140716, 174057]] ![![-13779577052241430, -890199397939963, -773587275605124]]
  ![![162593, 10504, 9128]] where
 M := ![![![162593, 10504, 9128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![162593, 10504, 9128]] ![![-95, -8, 24]]
  ![![257, 0, 0]] where
 M := ![![![257, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)


lemma PB281I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB281I4 : PrimesBelowBoundCertificateInterval O 193 257 281 where
  m := 11
  g := ![1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB281I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0, I257N1, I257N2]
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
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![251, 251, 251]
    · exact ![257, 257, 257]
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
  β := ![I199N1, I211N1, I223N1, I227N1, I229N1, I239N1, I241N1, I251N0, I251N1, I251N2, I257N0, I257N1, I257N2]
  Il := ![[], [I199N1], [I211N1], [I223N1], [I227N1], [I229N1], [], [I239N1], [I241N1], [I251N0, I251N1, I251N2], [I257N0, I257N1, I257N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
