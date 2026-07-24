
import IdealArithmetic.Examples.NF3_1_662796_4.RI3_1_662796_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![197, 0, 0], ![9, 1, 0], ![116, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 1], ![494, 114, 9]]]
  hmulB := by decide  
  f := ![![![-33, -9, 1]], ![![1, 0, 0]], ![![-42, -8, 1]]]
  g := ![![![0, 1, 0], ![-1, 9, 1], ![-8, 114, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![92, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![92, 1, 0]] 
 ![![197, 0, 0], ![92, 1, 0], ![7, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![92, 1, 0], ![0, 92, 1], ![494, 114, 92]]]
  hmulB := by decide  
  f := ![![![1197, 13, 0], ![-2561, 0, 0]], ![![460, 5, 0], ![-984, 0, 0]], ![![-49, -1, 0], ![105, 1, 0]]]
  g := ![![![1, 0, 0], ![-92, 197, 0], ![-7, 0, 197]], ![![0, 1, 0], ![-43, 92, 1], ![-54, 114, 92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![96, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![96, 1, 0]] 
 ![![197, 0, 0], ![96, 1, 0], ![43, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![96, 1, 0], ![0, 96, 1], ![494, 114, 96]]]
  hmulB := by decide  
  f := ![![![2977, 31, 0], ![-6107, 0, 0]], ![![1440, 15, 0], ![-2954, 0, 0]], ![![527, 5, 0], ![-1081, 1, 0]]]
  g := ![![![1, 0, 0], ![-96, 197, 0], ![-43, 0, 197]], ![![0, 1, 0], ![-47, 96, 1], ![-74, 114, 96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![9, 1, 0]] ![![197, 0, 0], ![92, 1, 0]]
  ![![197, 0, 0], ![-157, -96, 1]] where
 M := ![![![1773, 197, 0], ![828, 101, 1]]]
 hmul := by decide  
 g := ![![![![9, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-157, -96, 1]] ![![197, 0, 0], ![96, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![18912, 197, 0]], ![![-30929, -18912, 197], ![-14578, -9259, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![96, 1, 0]]], ![![![-157, -96, 1]], ![![-74, -47, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![10, -70, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![10, -70, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![10, 129, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![10, -70, 1], ![494, 124, -70], ![-34580, -7486, 124]]]
  hmulB := by decide  
  f := ![![![-9, 70, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -129, 199]], ![![0, -1, 1], ![6, 46, -70], ![-180, -118, 124]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [14, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 198], [0, 1]]
 g := ![![[183, 128], [172, 182], [], [], [53], [196], [25, 1]], ![[0, 71], [145, 17], [], [], [53], [196], [50, 198]]]
 h' := ![![[25, 198], [179, 160], [0, 111], [132], [27], [157, 75], [48, 14], [0, 1]], ![[0, 1], [0, 39], [188, 88], [132], [27], [42, 124], [0, 185], [25, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [191, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [14, 174, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1002, 548, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 41, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![70, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![70, 1, 0]] 
 ![![199, 0, 0], ![70, 1, 0], ![75, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![70, 1, 0], ![0, 70, 1], ![494, 114, 70]]]
  hmulB := by decide  
  f := ![![![5391, 77, 0], ![-15323, 0, 0]], ![![1890, 27, 0], ![-5372, 0, 0]], ![![2055, 29, 0], ![-5841, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 199, 0], ![-75, 0, 199]], ![![0, 1, 0], ![-25, 70, 1], ![-64, 114, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![10, -70, 1]] ![![199, 0, 0], ![70, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![13930, 199, 0]], ![![1990, -13930, 199], ![1194, -4776, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![70, 1, 0]]], ![![![10, -70, 1]], ![![6, -24, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-15, -47, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-15, -47, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![196, 164, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-15, -47, 1], ![494, 99, -47], ![-23218, -4864, 99]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-196, -164, 211]], ![![-1, -1, 1], ![46, 37, -47], ![-202, -100, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [206, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 210], [0, 1]]
 g := ![![[16, 103], [77, 54], [101], [136], [75, 169], [139], [80, 1]], ![[27, 108], [177, 157], [101], [136], [91, 42], [139], [160, 210]]]
 h' := ![![[80, 210], [174, 37], [88, 73], [146, 34], [164, 66], [124, 13], [189, 75], [0, 1]], ![[0, 1], [180, 174], [20, 138], [123, 177], [169, 145], [109, 198], [70, 136], [80, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [165, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [206, 131, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5852, 2820, 1417]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1344, -1088, 1417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![47, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![47, 1, 0]] 
 ![![211, 0, 0], ![47, 1, 0], ![112, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![47, 1, 0], ![0, 47, 1], ![494, 114, 47]]]
  hmulB := by decide  
  f := ![![![330, 7, 0], ![-1477, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![152, 3, 0], ![-680, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 211, 0], ![-112, 0, 211]], ![![0, 1, 0], ![-11, 47, 1], ![-48, 114, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-15, -47, 1]] ![![211, 0, 0], ![47, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![9917, 211, 0]], ![![-3165, -9917, 211], ![-211, -2110, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![47, 1, 0]]], ![![![-15, -47, 1]], ![![-1, -10, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [96, 86, 197, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 30, 103], [113, 192, 120], [0, 1]]
 g := ![![[203, 135, 17], [53, 61, 112], [74, 137, 66], [141, 163, 78], [2, 159, 38], [170, 7], [1]], ![[100, 43, 194, 45], [139, 93, 17, 182], [124, 147, 10, 180], [35, 94, 159, 54], [39, 78, 207, 205], [16, 50], [218, 189, 180, 27]], ![[116, 175, 3, 220], [30, 51, 90, 49], [193, 85, 0, 15], [75, 74, 153, 199], [105, 217, 151, 126], [118, 171], [162, 140, 105, 196]]]
 h' := ![![[136, 30, 103], [41, 199, 169], [32, 137, 119], [67, 170, 17], [31, 83, 154], [32, 105, 201], [127, 137, 26], [0, 1]], ![[113, 192, 120], [160, 121, 94], [63, 196, 164], [173, 49, 35], [168, 9, 207], [72, 32, 124], [50, 71, 148], [136, 30, 103]], ![[0, 1], [180, 126, 183], [207, 113, 163], [15, 4, 171], [57, 131, 85], [108, 86, 121], [145, 15, 49], [113, 192, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 80], []]
 b := ![[], [18, 144, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [96, 86, 197, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![459826, -86524, 1561]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2062, -388, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [134, 75, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 26, 107], [98, 200, 120], [0, 1]]
 g := ![![[38, 194, 59], [30, 100, 76], [68, 219], [24, 207], [10, 167], [177], [1]], ![[10, 54, 182, 223], [102, 206, 226, 226], [6, 82], [56, 133], [40, 139], [182, 25, 27, 168], [166, 186, 4, 151]], ![[114, 90, 177, 84], [66, 226, 225, 12], [58, 64], [112, 129], [118, 76], [88, 92, 68, 59], [63, 53, 153, 76]]]
 h' := ![![[129, 26, 107], [66, 11, 112], [15, 3, 168], [71, 14, 197], [91, 105, 52], [117, 141, 124], [93, 152], [0, 1]], ![[98, 200, 120], [180, 19, 196], [147, 18, 98], [66, 18, 38], [83, 182, 70], [201, 87, 162], [179, 93, 147], [129, 26, 107]], ![[0, 1], [177, 197, 146], [107, 206, 188], [36, 195, 219], [17, 167, 105], [47, 226, 168], [7, 209, 80], [98, 200, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 2], []]
 b := ![[], [3, 194, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [134, 75, 0, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5076628, -2683140, -335733]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22364, -11820, -1479]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [205, 179, 228, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 102, 187], [71, 126, 42], [0, 1]]
 g := ![![[207, 63, 215], [223, 108], [37, 160, 15], [191, 212], [6, 20], [180, 101, 1], [1]], ![[96, 111, 159, 46], [47, 126], [145, 160, 177, 178], [64, 149], [223, 172], [124, 62, 17, 183], [219, 17, 139, 108]], ![[206, 154, 170, 9], [83, 178], [182, 91, 23, 70], [179, 165], [222, 95], [0, 115, 169, 68], [84, 165, 65, 121]]]
 h' := ![![[159, 102, 187], [182, 74, 98], [201, 195, 197], [1, 22, 123], [189, 114, 21], [198, 92, 97], [24, 50, 1], [0, 1]], ![[71, 126, 42], [226, 157, 80], [48, 53, 144], [218, 153, 147], [133, 50, 148], [55, 178, 114], [31, 45, 87], [159, 102, 187]], ![[0, 1], [34, 227, 51], [65, 210, 117], [92, 54, 188], [190, 65, 60], [154, 188, 18], [168, 134, 141], [71, 126, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 35], []]
 b := ![[], [127, 73, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [205, 179, 228, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188009, 11221, 11221]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-821, 49, 49]
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



lemma PB231I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 230 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 230 (by omega)

def PB231I4 : PrimesBelowBoundCertificateInterval O 193 230 231 where
  m := 6
  g := ![3, 2, 2, 1, 1, 1]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB231I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![12008989]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
