
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [42, 71, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 20, 40], [26, 176, 157], [0, 1]]
 g := ![![[191, 41, 39], [125, 96], [33, 147, 64], [70, 171], [33, 41], [56, 60], [1]], ![[147, 43, 47, 76], [10, 154], [137, 105, 17, 16], [171, 34], [137, 150], [65, 100], [156, 46, 6, 172]], ![[156, 116, 83, 28], [108, 59], [26, 5, 70, 70], [179, 81], [127, 121], [119, 116], [18, 156, 119, 25]]]
 h' := ![![[55, 20, 40], [118, 19, 32], [190, 118, 117], [19, 190, 8], [2, 32, 34], [3, 59, 89], [155, 126, 81], [0, 1]], ![[26, 176, 157], [181, 122, 88], [73, 50, 96], [78, 91, 143], [103, 95, 172], [12, 130, 97], [56, 57, 187], [55, 20, 40]], ![[0, 1], [152, 56, 77], [74, 29, 181], [116, 113, 46], [99, 70, 188], [36, 8, 11], [75, 14, 126], [26, 176, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189, 75], []]
 b := ![[], [110, 44, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [42, 71, 116, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-433006, 11032, 16548]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2198, 56, 84]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [111, 46, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 187, 77], [192, 11, 122], [0, 1]]
 g := ![![[194, 36, 43], [5, 23, 187], [113, 20, 100], [185, 58], [27, 79], [90, 13], [1]], ![[92, 103, 93, 167], [139, 74, 43, 150], [196, 189, 152, 54], [116, 130], [156, 182], [101, 52], [26, 40, 153, 27]], ![[19, 187, 56, 1], [42, 27, 127, 126], [96, 97, 77, 89], [104, 121], [33, 63], [60, 13], [14, 99, 169, 172]]]
 h' := ![![[157, 187, 77], [42, 39, 178], [193, 170, 171], [184, 152, 189], [53, 180, 156], [142, 52, 26], [88, 153, 150], [0, 1]], ![[192, 11, 122], [142, 111, 185], [80, 125, 46], [48, 129, 52], [136, 49, 54], [61, 109, 111], [39, 112, 98], [157, 187, 77]], ![[0, 1], [88, 49, 35], [158, 103, 181], [30, 117, 157], [119, 169, 188], [198, 38, 62], [93, 133, 150], [192, 11, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 81], []]
 b := ![[], [33, 118, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [111, 46, 49, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![937489, -256312, 34626]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4711, -1288, 174]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [72, 123, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 143, 204], [9, 67, 7], [0, 1]]
 g := ![![[59, 204, 82], [35, 13, 114], [116, 103], [151, 14], [182, 154, 16], [136, 150], [1]], ![[173, 86, 79, 95], [178, 75, 8, 9], [37, 182], [132, 93], [123, 81, 101, 143], [79, 100], [54, 107, 108, 79]], ![[147, 152, 111, 130], [129, 123, 75, 106], [169, 209], [83, 119], [132, 135, 122, 131], [181, 81], [205, 12, 167, 132]]]
 h' := ![![[183, 143, 204], [12, 195, 90], [168, 98, 122], [162, 105, 37], [189, 176, 196], [34, 101, 207], [139, 88, 192], [0, 1]], ![[9, 67, 7], [139, 176, 23], [182, 174, 103], [37, 67, 56], [62, 0, 84], [118, 23, 80], [113, 4, 10], [183, 143, 204]], ![[0, 1], [200, 51, 98], [84, 150, 197], [15, 39, 118], [100, 35, 142], [103, 87, 135], [106, 119, 9], [9, 67, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 95], []]
 b := ![[], [176, 35, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [72, 123, 19, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-224504, 18568, -13715]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1064, 88, -65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![25, 50, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![25, 50, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![25, 50, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![25, 50, 1], ![-176, 94, 100], ![-8712, 862, 44]]]
  hmulB := by decide  
  f := ![![![-24, -50, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -50, 223]], ![![0, 0, 1], ![-12, -22, 100], ![-44, -6, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [200, 216, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 222], [0, 1]]
 g := ![![[10, 126], [104, 17], [94, 144], [4, 37], [184, 78], [55], [7, 1]], ![[0, 97], [0, 206], [210, 79], [40, 186], [61, 145], [55], [14, 222]]]
 h' := ![![[7, 222], [162, 168], [155, 169], [92, 12], [218, 137], [203, 154], [161, 72], [0, 1]], ![[0, 1], [0, 55], [0, 54], [176, 211], [62, 86], [166, 69], [219, 151], [7, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [193, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [200, 216, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-903, -2252, -607]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64, 126, -607]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-100, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-100, 1, 0]] 
 ![![223, 0, 0], ![123, 1, 0], ![179, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-100, 1, 0], ![0, -99, 2], ![-176, 19, -100]]]
  hmulB := by decide  
  f := ![![![16701, -167, 0], ![37241, 0, 0]], ![![9201, -92, 0], ![20517, 0, 0]], ![![13473, -85, -1], ![30043, 112, 0]]]
  g := ![![![1, 0, 0], ![-123, 223, 0], ![-179, 0, 223]], ![![-1, 1, 0], ![53, -99, 2], ![69, 19, -100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![25, 50, 1]] ![![223, 0, 0], ![-100, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-22300, 223, 0]], ![![5575, 11150, 223], ![-2676, -4906, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-100, 1, 0]]], ![![![25, 50, 1]], ![![-12, -22, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-68, 28, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-68, 28, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![159, 28, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-68, 28, 1], ![-176, -21, 56], ![-4840, 444, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-159, -28, 227]], ![![-1, 0, 1], ![-40, -7, 56], ![13, 8, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [203, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 226], [0, 1]]
 g := ![![[41, 104], [179, 144], [177], [169], [81], [20, 189], [76, 1]], ![[0, 123], [0, 83], [177], [169], [81], [83, 38], [152, 226]]]
 h' := ![![[76, 226], [210, 51], [4, 215], [117, 152], [123, 13], [26, 218], [8, 125], [0, 1]], ![[0, 1], [0, 176], [0, 12], [92, 75], [203, 214], [23, 9], [201, 102], [76, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212]]
 b := ![[], [58, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [203, 151, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1117, -862, -274]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![187, 30, -274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-56, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-56, 1, 0]] 
 ![![227, 0, 0], ![171, 1, 0], ![49, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-56, 1, 0], ![0, -55, 2], ![-176, 19, -56]]]
  hmulB := by decide  
  f := ![![![10193, -182, 0], ![41314, 0, 0]], ![![7673, -137, 0], ![31100, 0, 0]], ![![2219, -12, -1], ![8994, 114, 0]]]
  g := ![![![1, 0, 0], ![-171, 227, 0], ![-49, 0, 227]], ![![-1, 1, 0], ![41, -55, 2], ![-3, 19, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-68, 28, 1]] ![![227, 0, 0], ![-56, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-12712, 227, 0]], ![![-15436, 6356, 227], ![3632, -1589, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-56, 1, 0]]], ![![![-68, 28, 1]], ![![16, -7, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3119735411823278197222407535, -631548648986720319065931582, 149630783648111542464576300]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![3119735411823278197222407535, -631548648986720319065931582, 149630783648111542464576300]] 
 ![![229, 0, 0], ![0, 229, 0], ![159, 191, 1]] where
  M :=![![![3119735411823278197222407535, -631548648986720319065931582, 149630783648111542464576300], ![-26335017922067631473765428800, 5331171652150677184983425653, -1263097297973440638131863164], ![124320071182696591892486672832, -25166933291781501799135414458, 5962720301137397504049357235]]]
  hmulB := by decide  
  f := ![![![107000454921067, -719608198470, -2837546662788]], ![![499408212650688, 52367460129625, -1439216396940]], ![![490292523516753, 44208728086271, -2938747523453]]]
  g := ![![![-90268817415836057007184385, -127559075658410589213100458, 149630783648111542464576300], ![761997608976897074188649844, 1076780591987239471913403013, -1263097297973440638131863164], ![-3597172299991919699787603177, -5083172536283949454465339067, 5962720301137397504049357235]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [70, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [205, 228], [0, 1]]
 g := ![![[177, 36], [97], [143, 91], [12], [42], [186, 14], [205, 1]], ![[0, 193], [97], [20, 138], [12], [42], [79, 215], [181, 228]]]
 h' := ![![[205, 228], [85, 223], [66, 28], [208, 70], [210, 87], [33, 27], [77, 48], [0, 1]], ![[0, 1], [0, 6], [81, 201], [131, 159], [183, 142], [72, 202], [70, 181], [205, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164]]
 b := ![[], [68, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [70, 24, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108937, -21928, 9725]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7228, -8207, 9725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107000454921067, 719608198470, 2837546662788]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-107000454921067, 719608198470, 2837546662788]] 
 ![![229, 0, 0], ![76, 1, 0], ![51, 0, 1]] where
  M :=![![![-107000454921067, 719608198470, 2837546662788], ![-499408212650688, -52367460129625, 1439216396940], ![123053063394624, -236031550554414, -53087068328095]]]
  hmulB := by decide  
  f := ![![![-3119735411823278197222407535, 631548648986720319065931582, -149630783648111542464576300]], ![![-920370626098259875611954340, 186316705986201166218460151, -44143415979401906502951684]], ![![-1237670642732243580571307673, 250549844498271781971606660, -59361966232275485457391915]]]
  g := ![![![-1338015536275, 719608198470, 2837546662788], ![14878247689768, -52367460129625, 1439216396940], ![90693848865777, -236031550554414, -53087068328095]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![3119735411823278197222407535, -631548648986720319065931582, 149630783648111542464576300]] ![![-107000454921067, 719608198470, 2837546662788]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4534839594261325916546719, -959191472951065735600826, -316986822201088665992938]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![4534839594261325916546719, -959191472951065735600826, -316986822201088665992938]] 
 ![![233, 0, 0], ![0, 233, 0], ![14, 27, 1]] where
  M :=![![![4534839594261325916546719, -959191472951065735600826, -316986822201088665992938], ![55789680707391605214757088, -2447101500510424472919929, -1918382945902131471201652], ![140922858885691766858366832, 9670202367625553630962850, -1487910027559358737319103]]]
  hmulB := by decide  
  f := ![![![95245571530215836554706610028203555046330951639, -19281190255400816072750241904503708323006149066, 4568230194479634908064622096820229639971975550]], ![![-804008514228415743819373489040360416635067696800, 162760754969928083735184187963284209882792338023, -38562380510801632145500483809007416646012298132]], ![![-71155786011499793436238035811081753670950980286, 14404535831097096388581666728068116239736722571, -3412820196753649267844094092789395348828008175]]]
  g := ![![![38509249378011018199347, 32615676937675228524500, -316986822201088665992938], ![354708334549448265285752, 211799304887755902358475, -1918382945902131471201652], ![694221456100956176741778, 213921773011709182569007, -1487910027559358737319103]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [180, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 232], [0, 1]]
 g := ![![[64, 64], [195], [113], [144, 60], [201], [179, 107], [130, 1]], ![[229, 169], [195], [113], [22, 173], [201], [109, 126], [27, 232]]]
 h' := ![![[130, 232], [50, 225], [151, 112], [176, 87], [97, 35], [167, 30], [133, 177], [0, 1]], ![[0, 1], [175, 8], [32, 121], [69, 146], [220, 198], [106, 203], [76, 56], [130, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [232, 190]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [180, 103, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-538, 194, 128]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -14, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66198231866358804883325, -4401353197765898969516, 728854576312893735500]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-66198231866358804883325, -4401353197765898969516, 728854576312893735500]] 
 ![![233, 0, 0], ![179, 1, 0], ![200, 0, 1]] where
  M :=![![![-66198231866358804883325, -4401353197765898969516, 728854576312893735500], ![-128278405431069297448000, -56751348114179722878341, -8802706395531797939032], ![838777365522332867358816, -147764913473086729144804, -52349994916413823908825]]]
  hmulB := by decide  
  f := ![![![-1670201636412196457420309998264249577459669597, 338109950931724569931242483970209594613720700, -80107299727914211943803514181794268927354012]], ![![-1222606043629486114060626914992724819888697647, 247500218182265476838073263291499512203391975, -58639428109155342481022935925325128535488956]], ![![-1719300948594331615635259167723625321071055432, 348049449056240907579385464538514149725373332, -82462232947748535936108496154837744517382825]]]
  g := ![![![2471558262966344907983, -4401353197765898969516, 728854576312893735500], ![50604095219371075903783, -56751348114179722878341, -8802706395531797939032], ![162054488671620695991604, -147764913473086729144804, -52349994916413823908825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![4534839594261325916546719, -959191472951065735600826, -316986822201088665992938]] ![![-66198231866358804883325, -4401353197765898969516, 728854576312893735500]]
  ![![233, 0, 0]] where
 M := ![![![-443036181915539675783692799150323150279382554083, 81315508794693830585213025534155264338609685814, 28342978035405349876140212414644960918221542782]]]
 hmul := by decide  
 g := ![![![![-1901442840839226076324861798928425537679753451, 348993599977226740709068779116546198878153158, 121643682555387767708756276457703694927989454]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [189, 109, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 113, 133], [6, 125, 106], [0, 1]]
 g := ![![[85, 185, 163], [121, 2, 34], [172, 204, 133], [35, 131, 218], [84, 163], [114, 166, 204], [1]], ![[22, 68, 187, 4], [182, 70, 24, 216], [184, 227, 202, 45], [141, 11, 166, 87], [140, 25], [155, 227, 58, 45], [147, 44, 110, 160]], ![[94, 81, 191, 14], [230, 53, 122, 94], [156, 92, 85, 73], [95, 89, 222, 84], [80, 134], [128, 122, 128, 158], [147, 203, 120, 79]]]
 h' := ![![[187, 113, 133], [75, 72, 138], [235, 10, 150], [77, 107, 206], [238, 151, 74], [203, 47, 101], [50, 130, 193], [0, 1]], ![[6, 125, 106], [28, 192, 58], [3, 164, 4], [4, 191, 68], [4, 105, 175], [37, 110, 234], [104, 130, 68], [187, 113, 133]], ![[0, 1], [136, 214, 43], [58, 65, 85], [231, 180, 204], [138, 222, 229], [139, 82, 143], [157, 218, 217], [6, 125, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 57], []]
 b := ![[], [101, 20, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [189, 109, 46, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1241605, -431156, 44932]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5195, -1804, 188]
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



lemma PB241I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 240 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 240 (by omega)

def PB241I4 : PrimesBelowBoundCertificateInterval O 193 240 241 where
  m := 8
  g := ![1, 1, 1, 2, 2, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239]
  hP := PB241I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
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
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
  β := ![I223N1, I227N1, I229N1, I233N1]
  Il := ![[], [], [], [I223N1], [I227N1], [I229N1], [I233N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
