
import IdealArithmetic.Examples.NF3_1_933107_2.RI3_1_933107_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-41, 86, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-41, 86, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![156, 86, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-41, 86, 1], ![-218, -4, 87], ![-18966, 3001, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-156, -86, 197]], ![![-1, 0, 1], ![-70, -38, 87], ![-162, -21, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [44, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 196], [0, 1]]
 g := ![![[168, 4], [190], [183, 127], [107], [36], [10], [94, 1]], ![[150, 193], [190], [104, 70], [107], [36], [10], [188, 196]]]
 h' := ![![[94, 196], [145, 2], [25, 92], [62, 18], [47, 86], [152, 6], [1, 124], [0, 1]], ![[0, 1], [136, 195], [5, 105], [178, 179], [54, 111], [125, 191], [34, 73], [94, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [136, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [44, 103, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-610, -210, -62]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 26, -62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-87, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-87, 1, 0]] 
 ![![197, 0, 0], ![110, 1, 0], ![114, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-87, 1, 0], ![0, -87, 1], ![-218, 37, -86]]]
  hmulB := by decide  
  f := ![![![9832, -113, 0], ![22261, 0, 0]], ![![5482, -63, 0], ![12412, 0, 0]], ![![5694, -65, 0], ![12892, 1, 0]]]
  g := ![![![1, 0, 0], ![-110, 197, 0], ![-114, 0, 197]], ![![-1, 1, 0], ![48, -87, 1], ![28, 37, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-41, 86, 1]] ![![197, 0, 0], ![-87, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-17139, 197, 0]], ![![-8077, 16942, 197], ![3349, -7486, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-87, 1, 0]]], ![![![-41, 86, 1]], ![![17, -38, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [32, 12, 178, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 173, 166], [21, 25, 33], [0, 1]]
 g := ![![[0, 179, 90], [39, 81, 81], [150, 85, 112], [195, 157], [70, 62], [1, 43], [1]], ![[18, 133, 187, 76], [193, 14, 41, 186], [127, 60, 197, 150], [19, 151], [155, 28], [18, 103], [80, 148, 161, 82]], ![[83, 143, 143, 196], [119, 141, 105, 66], [107, 39, 139, 61], [135, 79], [90, 66], [173, 23], [70, 176, 154, 117]]]
 h' := ![![[0, 173, 166], [145, 103, 182], [175, 109, 9], [101, 156, 149], [157, 100, 82], [196, 176, 96], [167, 187, 21], [0, 1]], ![[21, 25, 33], [192, 44, 156], [115, 21, 11], [169, 5, 169], [141, 85, 143], [153, 140, 174], [27, 75, 125], [0, 173, 166]], ![[0, 1], [147, 52, 60], [108, 69, 179], [170, 38, 80], [50, 14, 173], [187, 82, 128], [56, 136, 53], [21, 25, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 70], []]
 b := ![[], [71, 144, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [32, 12, 178, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1397577, -799582, 94724]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7023, -4018, 476]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -35, -4]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-35, -35, -4]] 
 ![![211, 0, 0], ![0, 211, 0], ![167, 167, 1]] where
  M :=![![![-35, -35, -4], ![872, -183, -39], ![8502, -571, -222]]]
  hmulB := by decide  
  f := ![![![-87, 26, -3]], ![![654, -198, 23]], ![![425, -129, 15]]]
  g := ![![![3, 3, -4], ![35, 30, -39], ![216, 173, -222]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [26, 209, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 210], [0, 1]]
 g := ![![[146, 62], [142, 169], [208], [62], [86, 52], [62], [2, 1]], ![[59, 149], [58, 42], [208], [62], [190, 159], [62], [4, 210]]]
 h' := ![![[2, 210], [106, 22], [171, 13], [127, 182], [85, 189], [37, 91], [159, 189], [0, 1]], ![[0, 1], [150, 189], [197, 198], [69, 29], [41, 22], [8, 120], [115, 22], [2, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [173, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [26, 209, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9036, -174, -44]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 34, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 26, -3]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-87, 26, -3]] 
 ![![211, 0, 0], ![43, 1, 0], ![50, 0, 1]] where
  M :=![![![-87, 26, -3], ![654, -198, 23], ![-5014, 1505, -175]]]
  hmulB := by decide  
  f := ![![![-35, -35, -4]], ![![-3, -8, -1]], ![![32, -11, -2]]]
  g := ![![![-5, 26, -3], ![38, -198, 23], ![-289, 1505, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-35, -35, -4]] ![![-87, 26, -3]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [35, 86, 221, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 25, 108], [214, 197, 115], [0, 1]]
 g := ![![[108, 207, 4], [86, 65, 128], [105, 122, 98], [99, 181, 47], [177, 128, 16], [110, 4], [1]], ![[182, 215, 133, 93], [82, 128, 1, 22], [190, 67, 31, 67], [200, 72, 198, 219], [127, 129, 41, 99], [103, 7], [13, 87, 164, 208]], ![[152, 13, 160, 156], [88, 179, 37, 153], [102, 5, 57, 183], [115, 31, 158, 82], [31, 206, 218, 106], [210, 115], [180, 114, 78, 15]]]
 h' := ![![[11, 25, 108], [112, 217, 2], [116, 208, 103], [103, 40, 105], [49, 70, 50], [51, 211, 219], [188, 137, 2], [0, 1]], ![[214, 197, 115], [119, 222, 192], [31, 51, 162], [27, 14, 29], [191, 123, 16], [219, 71, 146], [207, 6, 26], [11, 25, 108]], ![[0, 1], [203, 7, 29], [38, 187, 181], [13, 169, 89], [121, 30, 157], [85, 164, 81], [107, 80, 195], [214, 197, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 82], []]
 b := ![[], [158, 116, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [35, 86, 221, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1209775, -13826, 41478]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5425, -62, 186]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [220, 115, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 83, 89], [73, 143, 138], [0, 1]]
 g := ![![[76, 66, 132], [180, 192, 59], [178, 23], [20, 70], [216, 70], [2, 43, 101], [1]], ![[66, 152, 85, 134], [6, 192, 192, 9], [3, 26], [111, 176], [202, 47], [71, 144, 120, 21], [187, 157, 184, 134]], ![[180, 104, 194, 191], [64, 170, 155, 93], [213, 73], [1, 212], [33, 48], [121, 42, 59, 15], [153, 200, 115, 93]]]
 h' := ![![[78, 83, 89], [125, 2, 141], [111, 121, 115], [0, 202, 134], [119, 121, 129], [14, 120, 129], [7, 112, 151], [0, 1]], ![[73, 143, 138], [155, 71, 138], [4, 153, 201], [94, 21, 139], [212, 84, 160], [29, 1, 71], [69, 169, 8], [78, 83, 89]], ![[0, 1], [141, 154, 175], [22, 180, 138], [183, 4, 181], [67, 22, 165], [116, 106, 27], [102, 173, 68], [73, 143, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 201], []]
 b := ![[], [32, 16, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [220, 115, 76, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54934, 2270, 2270]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-242, 10, 10]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [61, 133, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 166, 188], [92, 62, 41], [0, 1]]
 g := ![![[75, 110, 144], [214, 45], [41, 86, 37], [145, 168], [141, 183], [107, 183, 20], [1]], ![[31, 72, 164, 117], [164, 147], [75, 9, 84, 123], [102, 125], [138, 184], [127, 131, 16, 59], [30, 209, 3, 8]], ![[77, 147, 171, 89], [76, 91], [73, 205, 49, 156], [89, 209], [159, 132], [96, 128, 85, 182], [199, 217, 221, 221]]]
 h' := ![![[5, 166, 188], [94, 205, 12], [18, 211, 198], [190, 96, 138], [44, 1, 54], [114, 82, 130], [168, 96, 97], [0, 1]], ![[92, 62, 41], [63, 103, 125], [137, 213, 190], [205, 76, 40], [106, 123, 101], [76, 218, 118], [127, 62, 17], [5, 166, 188]], ![[0, 1], [112, 150, 92], [54, 34, 70], [42, 57, 51], [77, 105, 74], [171, 158, 210], [86, 71, 115], [92, 62, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 149], []]
 b := ![[], [39, 143, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [61, 133, 132, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3319813, 284876, 100302]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14497, 1244, 438]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [149, 1, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 153, 69], [100, 79, 164], [0, 1]]
 g := ![![[95, 11, 109], [57, 66], [90, 126], [118, 71, 72], [143, 100], [41, 5, 33], [1]], ![[87, 221, 198, 145], [218, 224], [111, 121], [82, 57, 53, 166], [158, 126], [68, 37, 176, 228], [83, 222, 169, 212]], ![[138, 19, 68, 136], [215, 177], [55, 152], [216, 86, 5, 130], [186, 37], [92, 169, 141, 39], [205, 71, 227, 21]]]
 h' := ![![[58, 153, 69], [217, 10, 153], [136, 224, 149], [126, 183, 91], [167, 147, 189], [182, 212, 223], [84, 232, 158], [0, 1]], ![[100, 79, 164], [86, 106, 195], [114, 17, 199], [24, 121, 11], [112, 132, 143], [11, 104, 91], [73, 143, 64], [58, 153, 69]], ![[0, 1], [147, 117, 118], [93, 225, 118], [42, 162, 131], [182, 187, 134], [220, 150, 152], [175, 91, 11], [100, 79, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199, 229], []]
 b := ![[], [3, 3, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [149, 1, 75, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27028, 699, -233]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116, 3, -1]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-39, 72, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-39, 72, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![200, 72, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-39, 72, 1], ![-218, -2, 73], ![-15914, 2483, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-200, -72, 239]], ![![-1, 0, 1], ![-62, -22, 73], ![-126, -11, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [189, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 238], [0, 1]]
 g := ![![[123, 122], [163, 25], [148, 166], [197, 218], [34], [156, 197], [175, 1]], ![[202, 117], [236, 214], [40, 73], [107, 21], [34], [215, 42], [111, 238]]]
 h' := ![![[175, 238], [24, 220], [230, 234], [51, 40], [187, 165], [152, 150], [146, 83], [0, 1]], ![[0, 1], [45, 19], [72, 5], [120, 199], [143, 74], [112, 89], [92, 156], [175, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [170, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [189, 64, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1555, -512, 285]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245, -88, 285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-73, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-73, 1, 0]] 
 ![![239, 0, 0], ![166, 1, 0], ![168, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-73, 1, 0], ![0, -73, 1], ![-218, 37, -72]]]
  hmulB := by decide  
  f := ![![![16134, -221, 0], ![52819, 0, 0]], ![![11170, -153, 0], ![36568, 0, 0]], ![![11338, -155, 0], ![37118, 1, 0]]]
  g := ![![![1, 0, 0], ![-166, 239, 0], ![-168, 0, 239]], ![![-1, 1, 0], ![50, -73, 1], ![24, 37, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-39, 72, 1]] ![![239, 0, 0], ![-73, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-17447, 239, 0]], ![![-9321, 17208, 239], ![2629, -5258, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-73, 1, 0]]], ![![![-39, 72, 1]], ![![11, -22, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![61, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![61, 1, 0]] 
 ![![241, 0, 0], ![61, 1, 0], ![135, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![61, 1, 0], ![0, 61, 1], ![-218, 37, 62]]]
  hmulB := by decide  
  f := ![![![6711, 110, 0], ![-26510, 0, 0]], ![![1647, 27, 0], ![-6506, 0, 0]], ![![3737, 61, 0], ![-14762, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 241, 0], ![-135, 0, 241]], ![![0, 1, 0], ![-16, 61, 1], ![-45, 37, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![64, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![64, 1, 0]] 
 ![![241, 0, 0], ![64, 1, 0], ![1, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![64, 1, 0], ![0, 64, 1], ![-218, 37, 65]]]
  hmulB := by decide  
  f := ![![![7105, 111, 0], ![-26751, 0, 0]], ![![1856, 29, 0], ![-6988, 0, 0]], ![![-47, -1, 0], ![177, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 241, 0], ![-1, 0, 241]], ![![0, 1, 0], ![-17, 64, 1], ![-11, 37, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![115, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![115, 1, 0]] 
 ![![241, 0, 0], ![115, 1, 0], ![30, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![115, 1, 0], ![0, 115, 1], ![-218, 37, 116]]]
  hmulB := by decide  
  f := ![![![8166, 71, 0], ![-17111, 0, 0]], ![![3910, 34, 0], ![-8193, 0, 0]], ![![860, 7, 0], ![-1802, 1, 0]]]
  g := ![![![1, 0, 0], ![-115, 241, 0], ![-30, 0, 241]], ![![0, 1, 0], ![-55, 115, 1], ![-33, 37, 116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![61, 1, 0]] ![![241, 0, 0], ![64, 1, 0]]
  ![![241, 0, 0], ![48, -116, 1]] where
 M := ![![![58081, 0, 0], ![15424, 241, 0]], ![![14701, 241, 0], ![3904, 125, 1]]]
 hmul := by decide  
 g := ![![![![193, 116, -1], ![241, 0, 0]], ![![16, 117, -1], ![241, 0, 0]]], ![![![13, 117, -1], ![241, 0, 0]], ![![-32, 117, -1], ![242, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![48, -116, 1]] ![![241, 0, 0], ![115, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![27715, 241, 0]], ![![11568, -27956, 241], ![5302, -13255, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![115, 1, 0]]], ![![![48, -116, 1]], ![![22, -55, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3229, -66, 47]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-3229, -66, 47]] 
 ![![251, 0, 0], ![0, 251, 0], ![209, 52, 1]] where
  M :=![![![-3229, -66, 47], ![-10246, -1490, -19], ![4142, -10949, -1509]]]
  hmulB := by decide  
  f := ![![![-8129, 2447, -284]], ![![61912, -18637, 2163]], ![![4179, -1258, 146]]]
  g := ![![![-52, -10, 47], ![-25, -2, -19], ![1273, 269, -1509]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [237, 175, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 250], [0, 1]]
 g := ![![[113, 233], [24, 135], [39], [69, 154], [167, 12], [159, 38], [76, 1]], ![[0, 18], [244, 116], [39], [227, 97], [75, 239], [35, 213], [152, 250]]]
 h' := ![![[76, 250], [85, 22], [233, 117], [213, 87], [79, 144], [218, 152], [60, 17], [0, 1]], ![[0, 1], [0, 229], [89, 134], [48, 164], [230, 107], [224, 99], [97, 234], [76, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [214, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [237, 175, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8439, -3994, 570]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-441, -134, 570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8129, 2447, -284]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-8129, 2447, -284]] 
 ![![251, 0, 0], ![198, 1, 0], ![203, 0, 1]] where
  M :=![![![-8129, 2447, -284], ![61912, -18637, 2163], ![-471534, 141943, -16474]]]
  hmulB := by decide  
  f := ![![![-3229, -66, 47]], ![![-2588, -58, 37]], ![![-2595, -97, 32]]]
  g := ![![![-1733, 2447, -284], ![13199, -18637, 2163], ![-100526, 141943, -16474]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-3229, -66, 47]] ![![-8129, 2447, -284]]
  ![![251, 0, 0]] where
 M := ![![![251, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![15, 1, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![15, 1, 0]] 
 ![![257, 0, 0], ![15, 1, 0], ![32, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![15, 1, 0], ![0, 15, 1], ![-218, 37, 16]]]
  hmulB := by decide  
  f := ![![![1681, 112, 0], ![-28784, 0, 0]], ![![75, 5, 0], ![-1284, 0, 0]], ![![196, 13, 0], ![-3356, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 257, 0], ![-32, 0, 257]], ![![0, 1, 0], ![-1, 15, 1], ![-5, 37, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N0)

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := prime_ideal_of_norm_prime hp257.out _ NI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![107, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![107, 1, 0]] 
 ![![257, 0, 0], ![107, 1, 0], ![116, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![107, 1, 0], ![0, 107, 1], ![-218, 37, 108]]]
  hmulB := by decide  
  f := ![![![8454, 79, 0], ![-20303, 0, 0]], ![![3424, 32, 0], ![-8223, 0, 0]], ![![3790, 35, 0], ![-9102, 1, 0]]]
  g := ![![![1, 0, 0], ![-107, 257, 0], ![-116, 0, 257]], ![![0, 1, 0], ![-45, 107, 1], ![-65, 37, 108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-123, 1, 0]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-123, 1, 0]] 
 ![![257, 0, 0], ![134, 1, 0], ![34, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-123, 1, 0], ![0, -123, 1], ![-218, 37, -122]]]
  hmulB := by decide  
  f := ![![![23371, -190, 0], ![48830, 0, 0]], ![![12178, -99, 0], ![25444, 0, 0]], ![![3134, -25, 0], ![6548, 1, 0]]]
  g := ![![![1, 0, 0], ![-134, 257, 0], ![-34, 0, 257]], ![![-1, 1, 0], ![64, -123, 1], ![-4, 37, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![15, 1, 0]] ![![257, 0, 0], ![107, 1, 0]]
  ![![257, 0, 0], ![63, 122, 1]] where
 M := ![![![66049, 0, 0], ![27499, 257, 0]], ![![3855, 257, 0], ![1605, 122, 1]]]
 hmul := by decide  
 g := ![![![![194, -122, -1], ![257, 0, 0]], ![![44, -121, -1], ![257, 0, 0]]], ![![![-48, -121, -1], ![257, 0, 0]], ![![-57, -122, -1], ![258, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![63, 122, 1]] ![![257, 0, 0], ![-123, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-31611, 257, 0]], ![![16191, 31354, 257], ![-7967, -14906, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-123, 1, 0]]], ![![![63, 122, 1]], ![![-31, -58, 0]]]]
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


lemma PB274I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB274I4 : PrimesBelowBoundCertificateInterval O 193 257 274 where
  m := 11
  g := ![2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1]
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
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![241, 241, 241]
    · exact ![63001, 251]
    · exact ![257, 257, 257]
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
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
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
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
  β := ![I197N1, I211N1, I239N1, I241N0, I241N1, I241N2, I251N1, I257N0, I257N1, I257N2]
  Il := ![[I197N1], [], [I211N1], [], [], [], [], [I239N1], [I241N0, I241N1, I241N2], [I251N1], [I257N0, I257N1, I257N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
