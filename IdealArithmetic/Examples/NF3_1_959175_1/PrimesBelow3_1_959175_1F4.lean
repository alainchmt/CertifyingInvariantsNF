
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![250433494053989, 72849947406914, 10977102719632]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![250433494053989, 72849947406914, 10977102719632]] 
 ![![197, 0, 0], ![0, 197, 0], ![121, 149, 1]] where
  M :=![![![250433494053989, 72849947406914, 10977102719632], ![3073588761496960, 894092782881767, 134722792094196], ![17324396512438960, 5039586975197576, 759369990787571]]]
  hmulB := by decide  
  f := ![![![57884513, 321554, -893800]], ![![-250264000, 11728467, 1536908]], ![![-152005131, 8635925, 665183]]]
  g := ![![![-5471045355439, -7932682019382, 10977102719632], ![-67146543562948, -97358392076921, 134722792094196], ![-378473971435823, -548764170823099, 759369990787571]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [109, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 196], [0, 1]]
 g := ![![[107, 47], [156], [82, 172], [178], [83], [133], [157, 1]], ![[0, 150], [156], [97, 25], [178], [83], [133], [117, 196]]]
 h' := ![![[157, 196], [145, 176], [124, 64], [182, 70], [188, 104], [166, 110], [26, 112], [0, 1]], ![[0, 1], [0, 21], [125, 133], [140, 127], [165, 93], [100, 87], [77, 85], [157, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [46, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [109, 40, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![949, 1574, 353]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212, -259, 353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57884513, -321554, 893800]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-57884513, -321554, 893800]] 
 ![![197, 0, 0], ![97, 1, 0], ![172, 0, 1]] where
  M :=![![![-57884513, -321554, 893800], ![250264000, -11728467, -1536908], ![-340299120, 85172392, -10191559]]]
  hmulB := by decide  
  f := ![![![-250433494053989, -72849947406914, -10977102719632]], ![![-138911866419969, -40408820717525, -6088841400500]], ![![-306593692841244, -89186689995872, -13438739383575]]]
  g := ![![![-915875, -321554, 893800], ![8387175, -11728467, -1536908], ![-34766868, 85172392, -10191559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![250433494053989, 72849947406914, 10977102719632]] ![![-57884513, -321554, 893800]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [145, 151, 180, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 147, 73], [124, 51, 126], [0, 1]]
 g := ![![[186, 159, 193], [104, 111, 28], [138, 32, 126], [72, 112], [58, 1], [126, 162], [1]], ![[148, 76, 115, 34], [154, 16, 164, 48], [181, 130, 132, 55], [133, 114], [112, 125], [194, 70], [147, 43, 163, 171]], ![[49, 168, 75, 178], [193, 108, 107, 144], [86, 20, 115, 139], [155, 66], [159, 90], [153, 61], [26, 27, 168, 28]]]
 h' := ![![[94, 147, 73], [44, 2, 118], [89, 92, 174], [140, 169, 46], [113, 67, 50], [168, 80, 198], [54, 48, 19], [0, 1]], ![[124, 51, 126], [39, 81, 194], [145, 140, 68], [51, 30, 156], [113, 1, 78], [45, 9, 18], [135, 82, 95], [94, 147, 73]], ![[0, 1], [84, 116, 86], [107, 166, 156], [184, 0, 196], [157, 131, 71], [160, 110, 182], [16, 69, 85], [124, 51, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 110], []]
 b := ![[], [155, 91, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [145, 151, 180, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1406333, 1290316, 312430]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7067, 6484, 1570]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25759, 990, -548]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![25759, 990, -548]] 
 ![![211, 0, 0], ![0, 211, 0], ![169, 173, 1]] where
  M :=![![![25759, 990, -548], ![-153440, -1747, 2528], ![430640, -10992, -4275]]]
  hmulB := by decide  
  f := ![![![-167091, -48606, -7324]], ![![-2050720, -596545, -89888]], ![![-1870009, -543977, -81967]]]
  g := ![![![561, 454, -548], ![-2752, -2081, 2528], ![5465, 3453, -4275]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [68, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 210], [0, 1]]
 g := ![![[102, 66], [37, 4], [123], [46], [2, 81], [151], [27, 1]], ![[196, 145], [145, 207], [123], [46], [79, 130], [151], [54, 210]]]
 h' := ![![[27, 210], [16, 53], [35, 2], [176, 171], [75, 149], [31, 9], [63, 28], [0, 1]], ![[0, 1], [181, 158], [89, 209], [151, 40], [89, 62], [63, 202], [186, 183], [27, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [49, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [68, 184, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7892, 114, -3]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, 3, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167091, -48606, -7324]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-167091, -48606, -7324]] 
 ![![211, 0, 0], ![77, 1, 0], ![162, 0, 1]] where
  M :=![![![-167091, -48606, -7324], ![-2050720, -596545, -89888], ![-11558960, -3362448, -506657]]]
  hmulB := by decide  
  f := ![![![25759, 990, -548]], ![![8673, 353, -188]], ![![21818, 708, -441]]]
  g := ![![![22569, -48606, -7324], ![276991, -596545, -89888], ![1561270, -3362448, -506657]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![25759, 990, -548]] ![![-167091, -48606, -7324]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [184, 134, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 149, 148], [154, 73, 75], [0, 1]]
 g := ![![[57, 209, 49], [107, 83, 133], [165, 89, 126], [104, 80, 202], [88, 184, 28], [186, 201], [1]], ![[185, 74, 43, 128], [76, 89, 125, 211], [18, 4, 127, 82], [167, 189, 75, 62], [42, 209, 141, 55], [215, 203], [71, 102, 56, 41]], ![[89, 154, 186, 27], [135, 63, 174, 117], [110, 198, 1, 215], [133, 30, 186, 90], [186, 195, 189, 150], [12, 41], [155, 50, 17, 182]]]
 h' := ![![[216, 149, 148], [159, 181, 216], [191, 73, 53], [42, 98, 55], [87, 130, 176], [78, 115, 171], [39, 89, 147], [0, 1]], ![[154, 73, 75], [161, 8, 186], [75, 102, 178], [153, 189, 10], [211, 53, 199], [194, 0, 67], [196, 88, 42], [216, 149, 148]], ![[0, 1], [27, 34, 44], [128, 48, 215], [171, 159, 158], [145, 40, 71], [58, 108, 208], [217, 46, 34], [154, 73, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 165], []]
 b := ![[], [216, 184, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [184, 134, 76, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4458885, -1595342, -232143]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19995, -7154, -1041]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-51, 89, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-51, 89, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![176, 89, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-51, 89, 1], ![280, 90, 177], ![24640, 4742, -87]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-176, -89, 227]], ![![-1, 0, 1], ![-136, -69, 177], ![176, 55, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [150, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 226], [0, 1]]
 g := ![![[174, 116], [42, 134], [81], [172], [181], [35, 189], [5, 1]], ![[73, 111], [31, 93], [81], [172], [181], [72, 38], [10, 226]]]
 h' := ![![[5, 226], [56, 195], [136, 208], [153, 9], [23, 95], [198, 194], [158, 102], [0, 1]], ![[0, 1], [123, 32], [41, 19], [198, 218], [44, 132], [33, 33], [214, 125], [5, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [75, 197]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [150, 222, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![990, 1210, -193]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 81, -193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![50, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![50, 1, 0]] 
 ![![227, 0, 0], ![50, 1, 0], ![87, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![50, 1, 0], ![0, 51, 2], ![280, 52, 49]]]
  hmulB := by decide  
  f := ![![![6201, 124, 0], ![-28148, 0, 0]], ![![1350, 27, 0], ![-6128, 0, 0]], ![![2381, 22, -1], ![-10808, 114, 0]]]
  g := ![![![1, 0, 0], ![-50, 227, 0], ![-87, 0, 227]], ![![0, 1, 0], ![-12, 51, 2], ![-29, 52, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-51, 89, 1]] ![![227, 0, 0], ![50, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![11350, 227, 0]], ![![-11577, 20203, 227], ![-2270, 4540, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![50, 1, 0]]], ![![![-51, 89, 1]], ![![-10, 20, 1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![70, -112, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![70, -112, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![70, 117, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![70, -112, 1], ![280, 10, -225], ![-31640, -5710, 235]]]
  hmulB := by decide  
  f := ![![![-69, 112, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -117, 229]], ![![0, -1, 1], ![70, 115, -225], ![-210, -145, 235]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [51, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 228], [0, 1]]
 g := ![![[82, 9], [81], [205, 19], [210], [53], [131, 172], [169, 1]], ![[0, 220], [81], [210, 210], [210], [53], [116, 57], [109, 228]]]
 h' := ![![[169, 228], [49, 226], [79, 9], [214, 146], [42, 179], [189, 104], [83, 114], [0, 1]], ![[0, 1], [0, 3], [226, 220], [156, 83], [65, 50], [132, 125], [113, 115], [169, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188]]
 b := ![[], [72, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [51, 60, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111832, 95594, 24635]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7042, -12169, 24635]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-4, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-4, 1, 0]] 
 ![![229, 0, 0], ![225, 1, 0], ![223, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-4, 1, 0], ![0, -3, 2], ![280, 52, -5]]]
  hmulB := by decide  
  f := ![![![697, -174, 0], ![39846, 0, 0]], ![![685, -171, 0], ![39160, 0, 0]], ![![675, -167, -1], ![38588, 115, 0]]]
  g := ![![![1, 0, 0], ![-225, 229, 0], ![-223, 0, 229]], ![![-1, 1, 0], ![1, -3, 2], ![-45, 52, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![70, -112, 1]] ![![229, 0, 0], ![-4, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-916, 229, 0]], ![![16030, -25648, 229], ![0, 458, -229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-4, 1, 0]]], ![![![70, -112, 1]], ![![0, 2, -1]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-10, 103, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-10, 103, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![223, 103, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-10, 103, 1], ![280, 145, 205], ![28560, 5470, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-223, -103, 233]], ![![-1, 0, 1], ![-195, -90, 205], ![180, 50, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [114, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [219, 232], [0, 1]]
 g := ![![[41, 229], [120], [123], [91, 182], [14], [81, 200], [219, 1]], ![[97, 4], [120], [123], [106, 51], [14], [77, 33], [205, 232]]]
 h' := ![![[219, 232], [74, 55], [163, 179], [111, 39], [208, 101], [86, 125], [198, 82], [0, 1]], ![[0, 1], [3, 178], [220, 54], [31, 194], [192, 132], [200, 108], [215, 151], [219, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190]]
 b := ![[], [199, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [114, 14, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![941, 350, 69]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, -29, 69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![28, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![28, 1, 0]] 
 ![![233, 0, 0], ![28, 1, 0], ![60, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![28, 1, 0], ![0, 29, 2], ![280, 52, 27]]]
  hmulB := by decide  
  f := ![![![533, 19, 0], ![-4427, 0, 0]], ![![28, 1, 0], ![-232, 0, 0]], ![![100, -11, -1], ![-830, 117, 0]]]
  g := ![![![1, 0, 0], ![-28, 233, 0], ![-60, 0, 233]], ![![0, 1, 0], ![-4, 29, 2], ![-12, 52, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-10, 103, 1]] ![![233, 0, 0], ![28, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![6524, 233, 0]], ![![-2330, 23999, 233], ![0, 3029, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![28, 1, 0]]], ![![![-10, 103, 1]], ![![0, 13, 1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![78, 36, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![78, 36, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![78, 36, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![78, 36, 1], ![280, 166, 71], ![9800, 1986, 95]]]
  hmulB := by decide  
  f := ![![![-77, -36, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -36, 239]], ![![0, 0, 1], ![-22, -10, 71], ![10, -6, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [152, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 238], [0, 1]]
 g := ![![[119, 58], [60, 176], [58, 31], [175, 54], [8], [207, 116], [76, 1]], ![[225, 181], [52, 63], [24, 208], [216, 185], [8], [180, 123], [152, 238]]]
 h' := ![![[76, 238], [201, 47], [27, 196], [168, 134], [104, 173], [84, 198], [159, 127], [0, 1]], ![[0, 1], [188, 192], [105, 43], [75, 105], [107, 66], [75, 41], [12, 112], [76, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [116, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [152, 163, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1552, 4908, 2128]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-688, -300, 2128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-71, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-71, 1, 0]] 
 ![![239, 0, 0], ![168, 1, 0], ![144, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-71, 1, 0], ![0, -70, 2], ![280, 52, -72]]]
  hmulB := by decide  
  f := ![![![10296, -145, 0], ![34655, 0, 0]], ![![7314, -103, 0], ![24618, 0, 0]], ![![6188, -52, -1], ![20828, 120, 0]]]
  g := ![![![1, 0, 0], ![-168, 239, 0], ![-144, 0, 239]], ![![-1, 1, 0], ![48, -70, 2], ![8, 52, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![78, 36, 1]] ![![239, 0, 0], ![-71, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-16969, 239, 0]], ![![18642, 8604, 239], ![-5258, -2390, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-71, 1, 0]]], ![![![78, 36, 1]], ![![-22, -10, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![105, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![105, 1, 0]] 
 ![![241, 0, 0], ![105, 1, 0], ![219, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![105, 1, 0], ![0, 106, 2], ![280, 52, 104]]]
  hmulB := by decide  
  f := ![![![3466, 33, 0], ![-7953, 0, 0]], ![![1470, 14, 0], ![-3373, 0, 0]], ![![3174, -23, -1], ![-7283, 121, 0]]]
  g := ![![![1, 0, 0], ![-105, 241, 0], ![-219, 0, 241]], ![![0, 1, 0], ![-48, 106, 2], ![-116, 52, 104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-58, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-58, 1, 0]] 
 ![![241, 0, 0], ![183, 1, 0], ![34, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-58, 1, 0], ![0, -57, 2], ![280, 52, -59]]]
  hmulB := by decide  
  f := ![![![11775, -203, 0], ![48923, 0, 0]], ![![8933, -154, 0], ![37115, 0, 0]], ![![1718, -1, -1], ![7138, 121, 0]]]
  g := ![![![1, 0, 0], ![-183, 241, 0], ![-34, 0, 241]], ![![-1, 1, 0], ![43, -57, 2], ![-30, 52, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-47, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-47, 1, 0]] 
 ![![241, 0, 0], ![194, 1, 0], ![124, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-47, 1, 0], ![0, -46, 2], ![280, 52, -48]]]
  hmulB := by decide  
  f := ![![![9871, -210, 0], ![50610, 0, 0]], ![![7944, -169, 0], ![40730, 0, 0]], ![![5128, -86, -1], ![26292, 121, 0]]]
  g := ![![![1, 0, 0], ![-194, 241, 0], ![-124, 0, 241]], ![![-1, 1, 0], ![36, -46, 2], ![-16, 52, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![105, 1, 0]] ![![241, 0, 0], ![-58, 1, 0]]
  ![![241, 0, 0], ![-153, 24, 1]] where
 M := ![![![58081, 0, 0], ![-13978, 241, 0]], ![![25305, 241, 0], ![-6090, 48, 2]]]
 hmul := by decide  
 g := ![![![![241, 0, 0], ![0, 0, 0]], ![![95, -23, -1], ![241, 0, 0]]], ![![![105, 1, 0], ![0, 0, 0]], ![![129, -24, -1], ![243, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-153, 24, 1]] ![![241, 0, 0], ![-47, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-11327, 241, 0]], ![![-36873, 5784, 241], ![7471, -1205, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-47, 1, 0]]], ![![![-153, 24, 1]], ![![31, -5, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-934001, 82020, -1050]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-934001, 82020, -1050]] 
 ![![251, 0, 0], ![151, 1, 0], ![70, 0, 1]] where
  M :=![![![-934001, 82020, -1050], ![-294000, -906581, 165090], ![23259600, 4145340, -1071671]]]
  hmulB := by decide  
  f := ![![![-287202386251, -83545848420, -12588771750]], ![![-186822376151, -54345766841, -8188874340]], ![![-159251587670, -46325551740, -6980380331]]]
  g := ![![![-52771, 82020, -1050], ![498181, -906581, 165090], ![-2102270, 4145340, -1071671]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-84, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-84, 1, 0]] 
 ![![251, 0, 0], ![167, 1, 0], ![28, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-84, 1, 0], ![0, -83, 2], ![280, 52, -85]]]
  hmulB := by decide  
  f := ![![![6469, -77, 0], ![19327, 0, 0]], ![![4369, -52, 0], ![13053, 0, 0]], ![![812, 32, -1], ![2426, 126, 0]]]
  g := ![![![1, 0, 0], ![-167, 251, 0], ![-28, 0, 251]], ![![-1, 1, 0], ![55, -83, 2], ![-24, 52, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-67, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-67, 1, 0]] 
 ![![251, 0, 0], ![184, 1, 0], ![48, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-67, 1, 0], ![0, -66, 2], ![280, 52, -68]]]
  hmulB := by decide  
  f := ![![![8242, -123, 0], ![30873, 0, 0]], ![![6098, -91, 0], ![22842, 0, 0]], ![![1684, 8, -1], ![6308, 126, 0]]]
  g := ![![![1, 0, 0], ![-184, 251, 0], ![-48, 0, 251]], ![![-1, 1, 0], ![48, -66, 2], ![-24, 52, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-934001, 82020, -1050]] ![![251, 0, 0], ![-84, 1, 0]]
  ![![251, 0, 0], ![-67, 34, 1]] where
 M := ![![![-234434251, 20587020, -263550], ![78162084, -7796261, 253290]]]
 hmul := by decide  
 g := ![![![![-870150, 49618, -2003], ![239203, 0, 0]], ![![290038, -20219, 1328], ![-80038, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-67, 34, 1]] ![![251, 0, 0], ![-67, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-16817, 251, 0]], ![![-16817, 8534, 251], ![4769, -2259, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-67, 1, 0]]], ![![![-67, 34, 1]], ![![19, -9, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-109, 123, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-109, 123, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![148, 123, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-109, 123, 1], ![280, 66, 245], ![34160, 6510, -179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-148, -123, 257]], ![![-1, 0, 1], ![-140, -117, 245], ![236, 111, -179]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [98, 254, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 256], [0, 1]]
 g := ![![[97, 139], [50], [120], [221], [168], [153], [9], [1]], ![[0, 118], [50], [120], [221], [168], [153], [9], [1]]]
 h' := ![![[3, 256], [123, 216], [198, 43], [176, 67], [195, 96], [168, 164], [241, 210], [159, 3], [0, 1]], ![[0, 1], [0, 41], [70, 214], [120, 190], [226, 161], [146, 93], [100, 47], [168, 254], [3, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204]]
 b := ![[], [104, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [98, 254, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17410, 7096, 392]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-158, -160, 392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![12, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![12, 1, 0]] 
 ![![257, 0, 0], ![12, 1, 0], ![179, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![12, 1, 0], ![0, 13, 2], ![280, 52, 11]]]
  hmulB := by decide  
  f := ![![![1657, 138, 0], ![-35466, 0, 0]], ![![60, 5, 0], ![-1284, 0, 0]], ![![1147, 89, -1], ![-24550, 129, 0]]]
  g := ![![![1, 0, 0], ![-12, 257, 0], ![-179, 0, 257]], ![![0, 1, 0], ![-2, 13, 2], ![-9, 52, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-109, 123, 1]] ![![257, 0, 0], ![12, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![3084, 257, 0]], ![![-28013, 31611, 257], ![-1028, 1542, 257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![12, 1, 0]]], ![![![-109, 123, 1]], ![![-4, 6, 1]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB278I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB278I4 : PrimesBelowBoundCertificateInterval O 193 257 278 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB278I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0, I257N1]
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
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![241, 241, 241]
    · exact ![251, 251, 251]
    · exact ![66049, 257]
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
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N1, I211N1, I227N1, I229N1, I233N1, I239N1, I241N0, I241N1, I241N2, I251N0, I251N1, I251N2, I257N1]
  Il := ![[I197N1], [], [I211N1], [], [I227N1], [I229N1], [I233N1], [I239N1], [I241N0, I241N1, I241N2], [I251N0, I251N1, I251N2], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
