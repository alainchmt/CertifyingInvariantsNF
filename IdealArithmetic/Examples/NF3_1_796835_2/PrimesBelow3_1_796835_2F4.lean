
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![85, -65, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![85, -65, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![85, 132, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![85, -65, 1], ![-336, -195, -588], ![9268, 1291, 262]]]
  hmulB := by decide  
  f := ![![![-84, 65, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -132, 197]], ![![0, -1, 1], ![252, 393, -588], ![-66, -169, 262]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [87, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 196], [0, 1]]
 g := ![![[109, 107], [39], [114, 26], [104], [37], [40], [170, 1]], ![[175, 90], [39], [3, 171], [104], [37], [40], [143, 196]]]
 h' := ![![[170, 196], [49, 111], [129, 32], [168, 115], [101, 33], [94, 148], [182, 51], [0, 1]], ![[0, 1], [7, 86], [53, 165], [18, 82], [195, 164], [38, 49], [184, 146], [170, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [93, 182]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [87, 27, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6311, -6148, -4494]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1907, 2980, -4494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-3, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-3, 1, 0]] 
 ![![197, 0, 0], ![194, 1, 0], ![132, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-3, 1, 0], ![3, 1, 9], ![-141, -20, -6]]]
  hmulB := by decide  
  f := ![![![38902, 12971, 116721], ![-394, -2554893, 0]], ![![38308, 12773, 114939], ![-393, -2515887, 0]], ![![26067, 8691, 78209], ![-219, -1711908, 0]]]
  g := ![![![1, 0, 0], ![-194, 197, 0], ![-132, 0, 197]], ![![-1, 1, 0], ![-7, 1, 9], ![23, -20, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![85, -65, 1]] ![![197, 0, 0], ![-3, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-591, 197, 0]], ![![16745, -12805, 197], ![-591, 0, -591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-3, 1, 0]]], ![![![85, -65, 1]], ![![-3, 0, -3]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [13, 137, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 18, 132], [71, 180, 67], [0, 1]]
 g := ![![[134, 101, 90], [105, 167, 106], [89, 116, 5], [60, 145], [43, 9], [38, 72], [1]], ![[35, 46, 99, 28], [78, 120, 125, 106], [13, 92], [66, 162], [127, 196], [61, 177], [17, 76, 99, 125]], ![[134, 137, 42, 97], [182, 91, 87, 183], [126, 154, 125, 136], [61, 188], [52, 90], [168, 130], [156, 197, 165, 74]]]
 h' := ![![[49, 18, 132], [28, 136, 17], [37, 147, 92], [52, 176, 123], [193, 188, 155], [73, 7, 196], [186, 62, 120], [0, 1]], ![[71, 180, 67], [165, 150, 117], [152, 31, 144], [186, 85], [7, 49, 180], [128, 75, 185], [18, 171, 133], [49, 18, 132]], ![[0, 1], [41, 112, 65], [172, 21, 162], [172, 137, 76], [186, 161, 63], [71, 117, 17], [71, 165, 145], [71, 180, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171, 121], []]
 b := ![[], [44, 169, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [13, 137, 79, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5201661, 1294893, 482177]
  a := ![4, 5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26139, 6507, 2423]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![6, 10, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![6, 10, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![6, 10, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![6, 10, 1], ![-111, 26, 87], ![-1307, -209, -42]]]
  hmulB := by decide  
  f := ![![![-5, -10, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -10, 211]], ![![0, 0, 1], ![-3, -4, 87], ![-5, 1, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [107, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 210], [0, 1]]
 g := ![![[15, 71], [192, 107], [203], [16], [120, 122], [56], [83, 1]], ![[0, 140], [0, 104], [203], [16], [118, 89], [56], [166, 210]]]
 h' := ![![[83, 210], [134, 156], [10, 188], [93, 25], [31, 207], [66, 132], [192, 30], [0, 1]], ![[0, 1], [0, 55], [0, 23], [58, 186], [121, 4], [50, 79], [150, 181], [83, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [86, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [107, 128, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-624960, -478019, -321701]
  a := ![-65, -65, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6186, 12981, -321701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-87, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-87, 1, 0]] 
 ![![211, 0, 0], ![124, 1, 0], ![42, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-87, 1, 0], ![3, -83, 9], ![-141, -20, -90]]]
  hmulB := by decide  
  f := ![![![5185, -177108, 19206], ![-2954, -450274, 0]], ![![3067, -104074, 11286], ![-1687, -264594, 0]], ![![1056, -35254, 3823], ![-530, -89628, 0]]]
  g := ![![![1, 0, 0], ![-124, 211, 0], ![-42, 0, 211]], ![![-1, 1, 0], ![47, -83, 9], ![29, -20, -90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![6, 10, 1]] ![![211, 0, 0], ![-87, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-18357, 211, 0]], ![![1266, 2110, 211], ![-633, -844, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-87, 1, 0]]], ![![![6, 10, 1]], ![![-3, -4, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-41, -100, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-41, -100, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![182, 123, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-41, -100, 1], ![-441, -461, -903], ![14203, 1991, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-182, -123, 223]], ![![-1, -1, 1], ![735, 496, -903], ![-133, -124, 241]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [160, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 222], [0, 1]]
 g := ![![[178, 38], [56, 200], [44, 196], [179, 16], [120, 62], [63], [64, 1]], ![[157, 185], [145, 23], [100, 27], [88, 207], [74, 161], [63], [128, 222]]]
 h' := ![![[64, 222], [183, 201], [96, 73], [127, 14], [201, 4], [56, 109], [18, 145], [0, 1]], ![[0, 1], [113, 22], [85, 150], [131, 209], [11, 219], [119, 114], [155, 78], [64, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [95, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [160, 159, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6247, -10249, -9627]
  a := ![-6, -8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7829, 5264, -9627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![11, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![11, 1, 0]] 
 ![![223, 0, 0], ![11, 1, 0], ![205, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![11, 1, 0], ![3, 15, 9], ![-141, -20, 8]]]
  hmulB := by decide  
  f := ![![![21650, 108623, 65178], ![1561, -1614966, 0]], ![![1060, 5354, 3213], ![224, -79611, 0]], ![![19900, 99855, 59917], ![1485, -1484610, 0]]]
  g := ![![![1, 0, 0], ![-11, 223, 0], ![-205, 0, 223]], ![![0, 1, 0], ![-9, 15, 9], ![-7, -20, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-41, -100, 1]] ![![223, 0, 0], ![11, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![2453, 223, 0]], ![![-9143, -22300, 223], ![-892, -1561, -892]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![11, 1, 0]]], ![![![-41, -100, 1]], ![![-4, -7, -4]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-69, -30, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-69, -30, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![158, 197, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-69, -30, 1], ![-231, -209, -273], ![4333, 591, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-158, -197, 227]], ![![-1, -1, 1], ![189, 236, -273], ![17, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [2, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 226], [0, 1]]
 g := ![![[89, 210], [221, 141], [116], [175], [133], [165, 70], [49, 1]], ![[164, 17], [93, 86], [116], [175], [133], [190, 157], [98, 226]]]
 h' := ![![[49, 226], [12, 133], [74, 145], [144, 32], [128, 42], [124, 70], [129, 129], [0, 1]], ![[0, 1], [173, 94], [142, 82], [123, 195], [143, 185], [149, 157], [94, 98], [49, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [41, 179]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [2, 178, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7151, -7205, -6759]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4673, 5834, -6759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![46, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![46, 1, 0]] 
 ![![227, 0, 0], ![46, 1, 0], ![224, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![46, 1, 0], ![3, 50, 9], ![-141, -20, 43]]]
  hmulB := by decide  
  f := ![![![48190, 849090, 152847], ![13620, -3855141, 0]], ![![9725, 172037, 30969], ![2952, -781107, 0]], ![![47574, 837869, 150827], ![13337, -3804192, 0]]]
  g := ![![![1, 0, 0], ![-46, 227, 0], ![-224, 0, 227]], ![![0, 1, 0], ![-19, 50, 9], ![-39, -20, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-69, -30, 1]] ![![227, 0, 0], ![46, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![10442, 227, 0]], ![![-15663, -6810, 227], ![-3405, -1589, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![46, 1, 0]]], ![![![-69, -30, 1]], ![![-15, -7, -1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [155, 154, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 55, 228], [184, 173, 1], [0, 1]]
 g := ![![[202, 80, 58], [173, 147], [213, 123, 203], [71, 26], [0, 75], [217, 59, 95], [1]], ![[199, 49, 107, 26], [97, 46], [165, 134, 141, 192], [166, 53], [189, 108], [198, 196, 183, 49], [43, 97, 147, 228]], ![[227, 208, 222, 225], [228, 171], [0, 210, 91, 42], [40, 83], [146, 3], [226, 194, 100, 217], [204, 7, 79, 1]]]
 h' := ![![[63, 55, 228], [125, 220, 79], [190, 165, 39], [7, 58, 165], [97, 212, 207], [28, 11, 126], [74, 75, 18], [0, 1]], ![[184, 173, 1], [155, 164, 165], [166, 78, 170], [96, 198, 91], [112, 212, 104], [18, 198, 32], [184, 43, 62], [63, 55, 228]], ![[0, 1], [52, 74, 214], [144, 215, 20], [167, 202, 202], [111, 34, 147], [191, 20, 71], [228, 111, 149], [184, 173, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 14], []]
 b := ![[], [96, 137, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [155, 154, 211, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6188886903, 1493242819, 468001804]
  a := ![42, 62, 125]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27025707, 6520711, 2043676]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35638480217, -517768953, 1521411324]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![35638480217, -517768953, 1521411324]] 
 ![![233, 0, 0], ![28, 1, 0], ![82, 0, 1]] where
  M :=![![![35638480217, -517768953, 1521411324], ![-216072303543, 3139177925, -9224154549], ![229710788745, -3337322856, 9806383244]]]
  hmulB := by decide  
  f := ![![![616756, 202188, 94497]], ![![19535, 22304, 17949]], ![![136475, 50151, 26000]]]
  g := ![![![-320256299, -517768953, 1521411324], ![1941679775, 3139177925, -9224154549], ![-2064238615, -3337322856, 9806383244]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2724551129301245, 39583281246105, -116311439648838]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-2724551129301245, 39583281246105, -116311439648838]] 
 ![![233, 0, 0], ![46, 1, 0], ![159, 0, 1]] where
  M :=![![![-2724551129301245, 39583281246105, -116311439648838], ![16518662834224473, -239989211340065, 705183850161459], ![-17561320939531119, 255137331917442, -749695059360476]]]
  hmulB := by decide  
  f := ![![![-98003062, 21286416, 35227275]], ![![-40391963, 1123486, 7323393]], ![![-64186533, 11338053, 20623105]]]
  g := ![![![59863248229799, 39583281246105, -116311439648838], ![-362944487638646, -239989211340065, 705183850161459], ![385853546054001, 255137331917442, -749695059360476]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1638442410202834964458067175265260633498964443578025, -23803894164848373693363243586545916208767253566089, 69945318134396088180525934557895472931316095642202]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![1638442410202834964458067175265260633498964443578025, -23803894164848373693363243586545916208767253566089, 69945318134396088180525934557895472931316095642202]] 
 ![![233, 0, 0], ![158, 1, 0], ![30, 0, 1]] where
  M :=![![![1638442410202834964458067175265260633498964443578025, -23803894164848373693363243586545916208767253566089, 69945318134396088180525934557895472931316095642202], ![-9933701539444393554534246503422899431941871246248749, 144320470855519706074095509761167510037573516469629, -424071001886823627781846995952599664672853569021407], ![10560716845086417773358388605166207897361740603965355, -153429979912597319757468539290140932206499789458038, 450838366278250498288690083982779869361576482716656]]]
  hmulB := by decide  
  f := ![![![260897903979814653686221158, 41282804883025679416158708, -1645260302812183853415835]], ![![178445059854748112635206231, 29964023609812096120910938, 500128313353401791699459]], ![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]]]
  g := ![![![14167803194064357779372024142500648955127500591219, -23803894164848373693363243586545916208767253566089, 69945318134396088180525934557895472931316095642202], ![-85897879304771666441141318313774146256192617072137, 144320470855519706074095509761167510037573516469629, -424071001886823627781846995952599664672853569021407], ![91319754003988323375011653620279309464126235437063, -153429979912597319757468539290140932206499789458038, 450838366278250498288690083982779869361576482716656]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![35638480217, -517768953, 1521411324]] ![![-2724551129301245, 39583281246105, -116311439648838]]
  ![![-132369704824244810615148490, 1923115774254444224719938, -5650879797564390381850497]] where
 M := ![![![-132369704824244810615148490, 1923115774254444224719938, -5650879797564390381850497]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-132369704824244810615148490, 1923115774254444224719938, -5650879797564390381850497]] ![![1638442410202834964458067175265260633498964443578025, -23803894164848373693363243586545916208767253566089, 69945318134396088180525934557895472931316095642202]]
  ![![233, 0, 0]] where
 M := ![![![-295661137805011451662405878042320143904388144395229303094726679200220861321247, 4295473792147427825481363923993218008447601085578234722584652915256942263498, -12621812164389045267941584211239052369516692031583781159478468723600446065778]]]
 hmul := by decide  
 g := ![![![![-1268931921909920393400883596748155124053168001696263103410844116739145327559, 18435509837542608693053064051473038662865240710636200526114390194235803706, -54170867658322082695028258417334988710372068805080605834671539586268008866]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2794215, -600759, -131582]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-2794215, -600759, -131582]] 
 ![![239, 0, 0], ![0, 239, 0], ![120, 146, 1]] where
  M :=![![![-2794215, -600759, -131582], ![16750785, -2565611, -5012085], ![71154073, 13199418, 1376538]]]
  hmulB := by decide  
  f := ![![![-262029054108, 3806854506, -11186054167]], ![![1588654201065, -23080552744, 67819853055]], ![![831845593297, -12085358839, 35511595830]]]
  g := ![![![54375, 77867, -131582], ![2586615, 3051041, -5012085], ![-393433, -785670, 1376538]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [152, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [196, 238], [0, 1]]
 g := ![![[5, 93], [60, 220], [69, 31], [144, 109], [124], [9, 98], [196, 1]], ![[69, 146], [160, 19], [170, 208], [237, 130], [124], [97, 141], [153, 238]]]
 h' := ![![[196, 238], [201, 136], [28, 170], [100, 105], [87, 161], [66, 210], [83, 24], [0, 1]], ![[0, 1], [89, 103], [127, 69], [126, 134], [95, 78], [118, 29], [7, 215], [196, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [77, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [152, 43, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2559, -1309, -577]
  a := ![2, 4, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![279, 347, -577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![262029054108, -3806854506, 11186054167]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![262029054108, -3806854506, 11186054167]] 
 ![![239, 0, 0], ![123, 1, 0], ![97, 0, 1]] where
  M :=![![![262029054108, -3806854506, 11186054167], ![-1588654201065, 23080552744, -67819853055], ![1688930064547, -24537397383, 72100642620]]]
  hmulB := by decide  
  f := ![![![2794215, 600759, 131582]], ![![1367940, 319912, 88689]], ![![836338, 188595, 47644]]]
  g := ![![![-1484414627, -3806854506, 11186054167], ![8999847522, 23080552744, -67819853055], ![-9567917956, -24537397383, 72100642620]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-2794215, -600759, -131582]] ![![262029054108, -3806854506, 11186054167]]
  ![![239, 0, 0]] where
 M := ![![![-239, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![63, 77, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![63, 77, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![63, 77, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![63, 77, 1], ![90, 351, 690], ![-10754, -1549, -186]]]
  hmulB := by decide  
  f := ![![![-62, -77, -1], ![241, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -77, 241]], ![![0, 0, 1], ![-180, -219, 690], ![4, 53, -186]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [228, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 240], [0, 1]]
 g := ![![[192, 194], [160], [12], [49], [135, 164], [116, 229], [86, 1]], ![[6, 47], [160], [12], [49], [20, 77], [48, 12], [172, 240]]]
 h' := ![![[86, 240], [239, 26], [150, 94], [200, 129], [68, 234], [62, 37], [154, 179], [0, 1]], ![[0, 1], [65, 215], [40, 147], [208, 112], [189, 7], [111, 204], [124, 62], [86, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [122, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [228, 155, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13225, -13379, -6759]
  a := ![8, 11, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1712, 2104, -6759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![33, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![33, 1, 0]] 
 ![![241, 0, 0], ![33, 1, 0], ![186, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![33, 1, 0], ![3, 37, 9], ![-141, -20, 30]]]
  hmulB := by decide  
  f := ![![![110530, 1398513, 340200], ![20967, -9109800, 0]], ![![15129, 191463, 46575], ![2893, -1247175, 0]], ![![85296, 1079350, 262561], ![16250, -7030800, 0]]]
  g := ![![![1, 0, 0], ![-33, 241, 0], ![-186, 0, 241]], ![![0, 1, 0], ![-12, 37, 9], ![-21, -20, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![63, 77, 1]] ![![241, 0, 0], ![33, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![7953, 241, 0]], ![![15183, 18557, 241], ![2169, 2892, 723]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![33, 1, 0]]], ![![![63, 77, 1]], ![![9, 12, 3]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![102, -78, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![102, -78, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![102, 173, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![102, -78, 1], ![-375, -230, -705], ![11101, 1551, 318]]]
  hmulB := by decide  
  f := ![![![-101, 78, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -173, 251]], ![![0, -1, 1], ![285, 485, -705], ![-85, -213, 318]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [76, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 250], [0, 1]]
 g := ![![[79, 245], [24, 91], [209], [132, 114], [213, 13], [120, 58], [20, 1]], ![[210, 6], [87, 160], [209], [153, 137], [222, 238], [25, 193], [40, 250]]]
 h' := ![![[20, 250], [184, 139], [244, 200], [8, 65], [127, 37], [167, 196], [237, 73], [0, 1]], ![[0, 1], [203, 112], [228, 51], [53, 186], [114, 214], [71, 55], [191, 178], [20, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [178, 183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [76, 231, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4779, -3905, -4085]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1641, 2800, -4085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-48, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-48, 1, 0]] 
 ![![251, 0, 0], ![203, 1, 0], ![184, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-48, 1, 0], ![3, -44, 9], ![-141, -20, -51]]]
  hmulB := by decide  
  f := ![![![89560, -1376802, 281637], ![-22590, -7854543, 0]], ![![72469, -1113480, 227772], ![-18071, -6352308, 0]], ![![65696, -1009290, 206459], ![-16338, -5757912, 0]]]
  g := ![![![1, 0, 0], ![-203, 251, 0], ![-184, 0, 251]], ![![-1, 1, 0], ![29, -44, 9], ![53, -20, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![102, -78, 1]] ![![251, 0, 0], ![-48, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-12048, 251, 0]], ![![25602, -19578, 251], ![-5271, 3514, -753]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-48, 1, 0]]], ![![![102, -78, 1]], ![![-21, 14, -3]]]]
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


lemma PB253I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 252 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 252 (by omega)

def PB253I4 : PrimesBelowBoundCertificateInterval O 193 252 253 where
  m := 10
  g := ![2, 1, 2, 2, 2, 1, 3, 2, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB253I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![233, 233, 233]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![63001, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
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
  β := ![I197N1, I211N1, I223N1, I227N1, I233N0, I233N1, I233N2, I239N1, I241N1, I251N1]
  Il := ![[I197N1], [], [I211N1], [I223N1], [I227N1], [], [I233N0, I233N1, I233N2], [I239N1], [I241N1], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
