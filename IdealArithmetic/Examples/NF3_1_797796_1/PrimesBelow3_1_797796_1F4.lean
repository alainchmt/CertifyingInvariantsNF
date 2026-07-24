
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [192, 96, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 26, 112], [59, 170, 85], [0, 1]]
 g := ![![[99, 49, 191], [134, 65], [80, 15, 188], [144, 187], [175, 36], [185, 187], [1]], ![[174, 100, 9, 7], [87, 40], [42, 112, 19, 40], [109, 36], [111, 127], [54, 150], [155, 3, 184, 121]], ![[14, 7, 34, 191], [43, 41], [77, 149, 59, 59], [7, 76], [118, 144], [101, 54], [63, 116, 8, 76]]]
 h' := ![![[101, 26, 112], [115, 31, 83], [6, 161, 159], [87, 151, 42], [130, 35, 160], [162, 142, 6], [5, 101, 160], [0, 1]], ![[59, 170, 85], [122, 132, 49], [188, 87, 146], [55, 141, 18], [135, 159, 191], [163, 140, 179], [175, 102, 97], [101, 26, 112]], ![[0, 1], [122, 34, 65], [164, 146, 89], [35, 102, 137], [0, 3, 43], [196, 112, 12], [26, 191, 137], [59, 170, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 23], []]
 b := ![[], [187, 62, 188], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [192, 96, 37, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-449948, -104804, -12214]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2284, -532, -62]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-1, 43, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-1, 43, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![198, 43, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-1, 43, 1], ![710, 116, 86], ![30530, 5386, 116]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-198, -43, 199]], ![![-1, 0, 1], ![-82, -18, 86], ![38, 2, 116]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [154, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 198], [0, 1]]
 g := ![![[162, 125], [45, 130], [168, 31], [26], [5], [1], [126, 1]], ![[191, 74], [107, 69], [94, 168], [26], [5], [1], [53, 198]]]
 h' := ![![[126, 198], [35, 181], [197, 54], [133, 164], [82, 15], [97, 123], [98, 1], [0, 1]], ![[0, 1], [155, 18], [36, 145], [101, 35], [181, 184], [73, 76], [25, 198], [126, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [197, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [154, 73, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8438, 1649, 1274]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1310, -267, 1274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-86, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-86, 1, 0]] 
 ![![199, 0, 0], ![113, 1, 0], ![83, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-86, 1, 0], ![0, -86, 2], ![710, 117, -86]]]
  hmulB := by decide  
  f := ![![![10063, -117, 0], ![23283, 0, 0]], ![![5677, -66, 0], ![13135, 0, 0]], ![![4319, -7, -1], ![9993, 100, 0]]]
  g := ![![![1, 0, 0], ![-113, 199, 0], ![-83, 0, 199]], ![![-1, 1, 0], ![48, -86, 2], ![-27, 117, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-1, 43, 1]] ![![199, 0, 0], ![-86, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-17114, 199, 0]], ![![-199, 8557, 199], ![796, -3582, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-86, 1, 0]]], ![![![-1, 43, 1]], ![![4, -18, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-1, 67, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-1, 67, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![210, 67, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-1, 67, 1], ![710, 116, 134], ![47570, 8194, 116]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-210, -67, 211]], ![![-1, 0, 1], ![-130, -42, 134], ![110, 2, 116]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [44, 169, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 210], [0, 1]]
 g := ![![[47, 24], [104, 69], [46], [24], [161, 171], [180], [42, 1]], ![[0, 187], [48, 142], [46], [24], [169, 40], [180], [84, 210]]]
 h' := ![![[42, 210], [66, 119], [106, 160], [81, 62], [90, 119], [167, 63], [51, 32], [0, 1]], ![[0, 1], [0, 92], [74, 51], [153, 149], [24, 92], [70, 148], [129, 179], [42, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [46, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [44, 169, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8096, 162, 78]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116, -24, 78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![77, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![77, 1, 0]] 
 ![![211, 0, 0], ![77, 1, 0], ![95, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![77, 1, 0], ![0, 77, 2], ![710, 117, 77]]]
  hmulB := by decide  
  f := ![![![4313, 56, 0], ![-11816, 0, 0]], ![![1463, 19, 0], ![-4008, 0, 0]], ![![1901, -14, -1], ![-5208, 106, 0]]]
  g := ![![![1, 0, 0], ![-77, 211, 0], ![-95, 0, 211]], ![![0, 1, 0], ![-29, 77, 2], ![-74, 117, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-1, 67, 1]] ![![211, 0, 0], ![77, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![16247, 211, 0]], ![![-211, 14137, 211], ![633, 5275, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![77, 1, 0]]], ![![![-1, 67, 1]], ![![3, 25, 1]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [126, 177, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 136, 138], [98, 86, 85], [0, 1]]
 g := ![![[178, 126, 47], [4, 94, 43], [21, 25, 105], [144, 181, 136], [78, 13, 199], [122, 8], [1]], ![[141, 215, 194, 33], [187, 34, 117, 131], [43, 5, 206, 139], [109, 36, 160, 179], [145, 13, 179, 4], [178, 83], [118, 157, 122, 17]], ![[56, 42, 96, 20], [76, 0, 159, 122], [54, 76, 98, 23], [73, 43, 185, 154], [132, 187, 101, 122], [181, 133], [68, 105, 57, 206]]]
 h' := ![![[95, 136, 138], [165, 167, 50], [30, 140, 126], [142, 130, 128], [207, 185, 164], [58, 148, 140], [97, 46, 193], [0, 1]], ![[98, 86, 85], [187, 157, 140], [14, 156, 51], [23, 213, 181], [43, 195, 163], [41, 13, 129], [13, 165, 200], [95, 136, 138]], ![[0, 1], [133, 122, 33], [195, 150, 46], [18, 103, 137], [71, 66, 119], [46, 62, 177], [38, 12, 53], [98, 86, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 34], []]
 b := ![[], [170, 127, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [126, 177, 30, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4701286, -1796934, -318444]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21082, -8058, -1428]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [150, 202, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 22, 18], [84, 204, 209], [0, 1]]
 g := ![![[102, 50, 207], [4, 173, 214], [65, 110], [104, 62], [97, 53], [175, 215, 49], [1]], ![[100, 189, 6, 72], [142, 81, 100, 165], [74, 139], [140, 196], [65, 29], [139, 91, 120, 124], [1, 55, 82, 157]], ![[145, 146, 216, 176], [54, 216, 78, 192], [198, 4], [59, 53], [84, 166], [125, 209, 120, 195], [201, 12, 81, 70]]]
 h' := ![![[136, 22, 18], [81, 110, 175], [38, 171, 206], [150, 203, 63], [119, 91, 210], [82, 73, 196], [77, 25, 220], [0, 1]], ![[84, 204, 209], [25, 177, 225], [135, 154, 156], [79, 81, 162], [60, 173, 213], [220, 20, 211], [146, 104, 157], [136, 22, 18]], ![[0, 1], [121, 167, 54], [70, 129, 92], [43, 170, 2], [128, 190, 31], [223, 134, 47], [48, 98, 77], [84, 204, 209]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 195], []]
 b := ![[], [53, 18, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [150, 202, 7, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-492590, -122580, -15890]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2170, -540, -70]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![24, -52, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![24, -52, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![24, 177, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![24, -52, 1], ![710, 141, -104], ![-36920, -5729, 141]]]
  hmulB := by decide  
  f := ![![![-23, 52, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -177, 229]], ![![0, -1, 1], ![14, 81, -104], ![-176, -134, 141]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [72, 219, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 228], [0, 1]]
 g := ![![[108, 225], [27], [225, 212], [185], [132], [38, 97], [10, 1]], ![[68, 4], [27], [55, 17], [185], [132], [92, 132], [20, 228]]]
 h' := ![![[10, 228], [163, 214], [59, 213], [116, 208], [29, 177], [12, 210], [196, 28], [0, 1]], ![[0, 1], [13, 15], [128, 16], [135, 21], [196, 52], [51, 19], [18, 201], [10, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [17, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [72, 219, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27272, 9000, 1060]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -780, 1060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![104, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![104, 1, 0]] 
 ![![229, 0, 0], ![104, 1, 0], ![88, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![104, 1, 0], ![0, 104, 2], ![710, 117, 104]]]
  hmulB := by decide  
  f := ![![![6241, 60, 0], ![-13740, 0, 0]], ![![2808, 27, 0], ![-6182, 0, 0]], ![![2312, -30, -1], ![-5090, 115, 0]]]
  g := ![![![1, 0, 0], ![-104, 229, 0], ![-88, 0, 229]], ![![0, 1, 0], ![-48, 104, 2], ![-90, 117, 104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![24, -52, 1]] ![![229, 0, 0], ![104, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![23816, 229, 0]], ![![5496, -11908, 229], ![3206, -5267, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![104, 1, 0]]], ![![![24, -52, 1]], ![![14, -23, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -10, 2]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-137, -10, 2]] 
 ![![233, 0, 0], ![61, 1, 0], ![120, 0, 1]] where
  M :=![![![-137, -10, 2], ![1420, 97, -20], ![-7100, -460, 97]]]
  hmulB := by decide  
  f := ![![![-209, -50, -6]], ![![-73, -17, -2]], ![![-260, -60, -7]]]
  g := ![![![1, -10, 2], ![-9, 97, -20], ![40, -460, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-33, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-33, 1, 0]] 
 ![![233, 0, 0], ![200, 1, 0], ![38, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-33, 1, 0], ![0, -33, 2], ![710, 117, -33]]]
  hmulB := by decide  
  f := ![![![4324, -131, 0], ![30523, 0, 0]], ![![3664, -111, 0], ![25864, 0, 0]], ![![712, -5, -1], ![5026, 117, 0]]]
  g := ![![![1, 0, 0], ![-200, 233, 0], ![-38, 0, 233]], ![![-1, 1, 0], ![28, -33, 2], ![-92, 117, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-28, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-28, 1, 0]] 
 ![![233, 0, 0], ![205, 1, 0], ![74, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-28, 1, 0], ![0, -28, 2], ![710, 117, -28]]]
  hmulB := by decide  
  f := ![![![869, -31, 0], ![7223, 0, 0]], ![![785, -28, 0], ![6525, 0, 0]], ![![282, 4, -1], ![2344, 117, 0]]]
  g := ![![![1, 0, 0], ![-205, 233, 0], ![-74, 0, 233]], ![![-1, 1, 0], ![24, -28, 2], ![-91, 117, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-137, -10, 2]] ![![233, 0, 0], ![-33, 1, 0]]
  ![![233, 0, 0], ![-191, 14, 1]] where
 M := ![![![-31921, -2330, 466], ![5941, 427, -86]]]
 hmul := by decide  
 g := ![![![![54, -24, 1], ![233, 0, 0]], ![![146, -7, -1], ![147, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-191, 14, 1]] ![![233, 0, 0], ![-28, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-6524, 233, 0]], ![![-44503, 3262, 233], ![6058, -466, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-28, 1, 0]]], ![![![-191, 14, 1]], ![![26, -2, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![50, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![50, 1, 0]] 
 ![![239, 0, 0], ![50, 1, 0], ![184, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![50, 1, 0], ![0, 50, 2], ![710, 117, 50]]]
  hmulB := by decide  
  f := ![![![6501, 130, 0], ![-31070, 0, 0]], ![![1350, 27, 0], ![-6452, 0, 0]], ![![5056, 76, -1], ![-24164, 120, 0]]]
  g := ![![![1, 0, 0], ![-50, 239, 0], ![-184, 0, 239]], ![![0, 1, 0], ![-12, 50, 2], ![-60, 117, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-583, -38, 8]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-583, -38, 8]] 
 ![![239, 0, 0], ![57, 1, 0], ![168, 0, 1]] where
  M :=![![![-583, -38, 8], ![5680, 353, -76], ![-26980, -1606, 353]]]
  hmulB := by decide  
  f := ![![![-2553, -566, -64]], ![![-799, -177, -20]], ![![-3476, -770, -87]]]
  g := ![![![1, -38, 8], ![-7, 353, -76], ![22, -1606, 353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-107, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-107, 1, 0]] 
 ![![239, 0, 0], ![132, 1, 0], ![131, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-107, 1, 0], ![0, -107, 2], ![710, 117, -107]]]
  hmulB := by decide  
  f := ![![![22257, -208, 0], ![49712, 0, 0]], ![![12306, -115, 0], ![27486, 0, 0]], ![![12383, -62, -1], ![27658, 120, 0]]]
  g := ![![![1, 0, 0], ![-132, 239, 0], ![-131, 0, 239]], ![![-1, 1, 0], ![58, -107, 2], ![-3, 117, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![50, 1, 0]] ![![-583, -38, 8]]
  ![![239, 0, 0], ![-9, -66, 1]] where
 M := ![![![-139337, -9082, 1912]], ![![-23470, -1547, 324]]]
 hmul := by decide  
 g := ![![![![-574, 28, 7], ![239, 0, 0]]], ![![![-95, 17, 1], ![85, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-9, -66, 1]] ![![239, 0, 0], ![-107, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-25573, 239, 0]], ![![-2151, -15774, 239], ![1673, 7170, -239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-107, 1, 0]]], ![![![-9, -66, 1]], ![![7, 30, -1]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-88, 48, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-88, 48, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![153, 48, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-88, 48, 1], ![710, 29, 96], ![34080, 5971, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -48, 241]], ![![-1, 0, 1], ![-58, -19, 96], ![123, 19, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [108, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [228, 240], [0, 1]]
 g := ![![[105, 212], [48], [79], [192], [140, 72], [5, 106], [228, 1]], ![[0, 29], [48], [79], [192], [168, 169], [73, 135], [215, 240]]]
 h' := ![![[228, 240], [147, 104], [149, 17], [103, 101], [63, 34], [183, 132], [199, 61], [0, 1]], ![[0, 1], [0, 137], [169, 224], [236, 140], [103, 207], [154, 109], [129, 180], [228, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [143, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [108, 13, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4164, -314, 124]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -26, 124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-96, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-96, 1, 0]] 
 ![![241, 0, 0], ![145, 1, 0], ![212, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-96, 1, 0], ![0, -96, 2], ![710, 117, -96]]]
  hmulB := by decide  
  f := ![![![15361, -160, 0], ![38560, 0, 0]], ![![9313, -97, 0], ![23378, 0, 0]], ![![13652, -94, -1], ![34270, 121, 0]]]
  g := ![![![1, 0, 0], ![-145, 241, 0], ![-212, 0, 241]], ![![-1, 1, 0], ![56, -96, 2], ![17, 117, -96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-88, 48, 1]] ![![241, 0, 0], ![-96, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-23136, 241, 0]], ![![-21208, 11568, 241], ![9158, -4579, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-96, 1, 0]]], ![![![-88, 48, 1]], ![![38, -19, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-61, -84, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-61, -84, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![190, 167, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-61, -84, 1], ![710, 56, -168], ![-59640, -9473, 56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-190, -167, 251]], ![![-1, -1, 1], ![130, 112, -168], ![-280, -75, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [39, 229, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 250], [0, 1]]
 g := ![![[244, 103], [23, 101], [94], [143, 209], [64, 222], [116, 237], [22, 1]], ![[0, 148], [237, 150], [94], [223, 42], [179, 29], [59, 14], [44, 250]]]
 h' := ![![[22, 250], [107, 75], [112, 193], [196, 211], [14, 65], [245, 67], [146, 194], [0, 1]], ![[0, 1], [0, 176], [91, 58], [69, 40], [189, 186], [213, 184], [147, 57], [22, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [72, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [39, 229, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2879, 2117, 928]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-691, -609, 928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-83, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-83, 1, 0]] 
 ![![251, 0, 0], ![168, 1, 0], ![195, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-83, 1, 0], ![0, -83, 2], ![710, 117, -83]]]
  hmulB := by decide  
  f := ![![![13447, -162, 0], ![40662, 0, 0]], ![![9048, -109, 0], ![27360, 0, 0]], ![![10431, -84, -1], ![31542, 126, 0]]]
  g := ![![![1, 0, 0], ![-168, 251, 0], ![-195, 0, 251]], ![![-1, 1, 0], ![54, -83, 2], ![-11, 117, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-61, -84, 1]] ![![251, 0, 0], ![-83, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-20833, 251, 0]], ![![-15311, -21084, 251], ![5773, 7028, -251]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-83, 1, 0]]], ![![![-61, -84, 1]], ![![23, 28, -1]]]]
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
  g := ![1, 2, 2, 1, 1, 2, 3, 3, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB253I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1, I239N2]
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
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![233, 233, 233]
    · exact ![239, 239, 239]
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
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N1, I211N1, I229N1, I233N0, I233N1, I233N2, I239N0, I239N1, I239N2, I241N1, I251N1]
  Il := ![[], [I199N1], [I211N1], [], [], [I229N1], [I233N0, I233N1, I233N2], [I239N0, I239N1, I239N2], [I241N1], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
