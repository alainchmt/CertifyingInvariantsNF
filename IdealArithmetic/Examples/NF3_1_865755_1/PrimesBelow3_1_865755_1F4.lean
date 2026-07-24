
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [127, 143, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 27, 31], [153, 169, 166], [0, 1]]
 g := ![![[40, 150, 182], [174, 157], [144, 98, 96], [136, 16], [162, 37], [170, 4], [1]], ![[151, 40, 56, 35], [54, 33], [87, 145, 169, 86], [21, 143], [17, 42], [121, 76], [51, 96, 135, 44]], ![[162, 69, 111, 122], [181, 25], [55, 37, 48, 149], [24, 137], [120, 4], [117, 55], [71, 108, 134, 153]]]
 h' := ![![[42, 27, 31], [70, 101, 24], [33, 18, 123], [123, 109, 117], [181, 21, 4], [55, 78, 148], [70, 54, 195], [0, 1]], ![[153, 169, 166], [171, 190, 95], [79, 18, 69], [52, 105, 103], [143, 177, 145], [23, 87, 47], [40, 77, 154], [42, 27, 31]], ![[0, 1], [91, 103, 78], [134, 161, 5], [78, 180, 174], [34, 196, 48], [156, 32, 2], [162, 66, 45], [153, 169, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 151], []]
 b := ![[], [8, 82, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [127, 143, 2, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2864577, -715504, -218670]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14541, -3632, -1110]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![48, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![48, 1, 0]] 
 ![![199, 0, 0], ![48, 1, 0], ![127, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![48, 1, 0], ![2, 49, 5], ![279, 39, 47]]]
  hmulB := by decide  
  f := ![![![28981, 774635, 79050], ![10945, -3146190, 0]], ![![6954, 186823, 19065], ![2787, -758787, 0]], ![![18493, 494365, 50449], ![6995, -2007870, 0]]]
  g := ![![![1, 0, 0], ![-48, 199, 0], ![-127, 0, 199]], ![![0, 1, 0], ![-15, 49, 5], ![-38, 39, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![72, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![72, 1, 0]] 
 ![![199, 0, 0], ![72, 1, 0], ![183, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![72, 1, 0], ![2, 73, 5], ![279, 39, 71]]]
  hmulB := by decide  
  f := ![![![-1497, -65185, -4465], ![-796, 177707, 0]], ![![-574, -23578, -1615], ![-198, 64277, 0]], ![![-1377, -59944, -4106], ![-731, 163419, 0]]]
  g := ![![![1, 0, 0], ![-72, 199, 0], ![-183, 0, 199]], ![![0, 1, 0], ![-31, 73, 5], ![-78, 39, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![79, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![79, 1, 0]] 
 ![![199, 0, 0], ![79, 1, 0], ![10, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![79, 1, 0], ![2, 80, 5], ![279, 39, 78]]]
  hmulB := by decide  
  f := ![![![-24412, -1226081, -76635], ![-15721, 3050073, 0]], ![![-9719, -486689, -30420], ![-6168, 1210716, 0]], ![![-1297, -61613, -3851], ![-613, 153270, 0]]]
  g := ![![![1, 0, 0], ![-79, 199, 0], ![-10, 0, 199]], ![![0, 1, 0], ![-32, 80, 5], ![-18, 39, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![48, 1, 0]] ![![199, 0, 0], ![72, 1, 0]]
  ![![199, 0, 0], ![15, 64, 1]] where
 M := ![![![39601, 0, 0], ![14328, 199, 0]], ![![9552, 199, 0], ![3458, 121, 5]]]
 hmul := by decide  
 g := ![![![![184, -64, -1], ![199, 0, 0]], ![![57, -63, -1], ![199, 0, 0]]], ![![![33, -63, -1], ![199, 0, 0]], ![![17, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![15, 64, 1]] ![![199, 0, 0], ![79, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![15721, 199, 0]], ![![2985, 12736, 199], ![1592, 5174, 398]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![79, 1, 0]]], ![![![15, 64, 1]], ![![8, 26, 2]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [173, 209, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 185, 110], [173, 25, 101], [0, 1]]
 g := ![![[178, 179, 93], [98, 110, 5], [91, 136], [67, 64], [182, 58, 79], [44, 43], [1]], ![[166, 37, 86, 112], [57, 143, 90, 162], [51, 139], [44, 83], [115, 203, 19, 77], [36, 64], [152, 189, 113, 12]], ![[58, 53, 180, 69], [50, 150, 189, 55], [1, 81], [146, 59], [16, 22, 29, 109], [32, 101], [160, 183, 90, 199]]]
 h' := ![![[12, 185, 110], [137, 134, 127], [191, 128, 146], [113, 102, 145], [164, 116, 203], [162, 186, 135], [38, 2, 185], [0, 1]], ![[173, 25, 101], [160, 17, 191], [76, 97, 6], [167, 144, 75], [129, 181, 111], [126, 110, 203], [119, 52, 203], [12, 185, 110]], ![[0, 1], [67, 60, 104], [42, 197, 59], [2, 176, 202], [183, 125, 108], [19, 126, 84], [160, 157, 34], [173, 25, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 39], []]
 b := ![[], [118, 13, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [173, 209, 26, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20533465, 8558160, 3302572]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97315, 40560, 15652]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-36, 44, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-36, 44, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![187, 44, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-36, 44, 1], ![367, 47, 219], ![12180, 1764, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-187, -44, 223]], ![![-1, 0, 1], ![-182, -43, 219], ![89, 16, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [41, 159, 1] where
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
 g := ![![[216, 136], [190, 4], [209, 49], [49, 60], [0, 15], [120], [64, 1]], ![[0, 87], [0, 219], [0, 174], [98, 163], [68, 208], [120], [128, 222]]]
 h' := ![![[64, 222], [15, 59], [128, 221], [221, 7], [0, 27], [14, 125], [52, 41], [0, 1]], ![[0, 1], [0, 164], [0, 2], [0, 216], [167, 196], [209, 98], [0, 182], [64, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [108, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [41, 159, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3053647, 1515376, 689736]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-564695, -129296, 689736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![4, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![4, 1, 0]] 
 ![![223, 0, 0], ![4, 1, 0], ![41, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![4, 1, 0], ![2, 5, 5], ![279, 39, 3]]]
  hmulB := by decide  
  f := ![![![-22167, -55438, -55440], ![-446, 2472624, 0]], ![![-396, -990, -990], ![1, 44154, 0]], ![![-4077, -10193, -10193], ![-1, 454608, 0]]]
  g := ![![![1, 0, 0], ![-4, 223, 0], ![-41, 0, 223]], ![![0, 1, 0], ![-1, 5, 5], ![0, 39, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-36, 44, 1]] ![![223, 0, 0], ![4, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![892, 223, 0]], ![![-8028, 9812, 223], ![223, 223, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![4, 1, 0]]], ![![![-36, 44, 1]], ![![1, 1, 1]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [2, 55, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 139, 215], [203, 87, 12], [0, 1]]
 g := ![![[162, 161, 28], [223, 154, 171], [157, 97], [32, 97], [54, 19], [130, 91, 113], [1]], ![[24, 164, 200, 168], [112, 128, 73, 15], [34, 85], [71, 78], [202, 33], [66, 91, 86, 6], [11, 181, 141, 88]], ![[114, 40, 7, 214], [181, 178, 27, 139], [71, 90], [205, 221], [83, 92], [144, 104], [195, 102, 108, 139]]]
 h' := ![![[130, 139, 215], [8, 93, 74], [33, 31, 25], [44, 111, 209], [73, 81, 18], [194, 163, 143], [225, 172, 106], [0, 1]], ![[203, 87, 12], [159, 28, 101], [186, 77, 214], [77, 198, 53], [30, 158, 140], [52, 157, 43], [72, 26, 121], [130, 139, 215]], ![[0, 1], [176, 106, 52], [63, 119, 215], [146, 145, 192], [130, 215, 69], [110, 134, 41], [87, 29], [203, 87, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201, 58], []]
 b := ![[], [72, 14, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [2, 55, 121, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27703534, -8014916, -2424360]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-122042, -35308, -10680]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [120, 7, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 166, 210], [207, 62, 19], [0, 1]]
 g := ![![[68, 168, 151], [184, 225], [3, 170, 228], [68, 168], [115, 209], [49, 216, 180], [1]], ![[84, 60, 65, 16], [43, 57], [63, 0, 42, 181], [203, 228], [182, 61], [147, 169, 46, 130], [20, 39, 8, 11]], ![[53, 133, 17, 132], [216, 51], [62, 161, 69, 25], [22, 61], [228, 212], [169, 115, 52, 132], [52, 164, 54, 218]]]
 h' := ![![[84, 166, 210], [119, 45, 193], [98, 106, 15], [72, 46, 122], [149, 11, 175], [74, 45, 155], [109, 222, 62], [0, 1]], ![[207, 62, 19], [190, 7, 119], [147, 191, 61], [81, 193, 49], [204, 135, 107], [212, 208, 53], [171, 101, 84], [84, 166, 210]], ![[0, 1], [68, 177, 146], [180, 161, 153], [38, 219, 58], [56, 83, 176], [60, 205, 21], [58, 135, 83], [207, 62, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 121], []]
 b := ![[], [127, 203, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [120, 7, 167, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2337632, -386552, -53815]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10208, -1688, -235]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14030, -807, 525]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-14030, -807, 525]] 
 ![![233, 0, 0], ![0, 233, 0], ![11, 89, 1]] where
  M :=![![![-14030, -807, 525], ![144861, 5638, -4560], ![-275553, -6273, 7252]]]
  hmulB := by decide  
  f := ![![![52712, 10983, 3090]], ![![884076, 184205, 51825]], ![![352061, 73355, 20638]]]
  g := ![![![-85, -204, 525], ![837, 1766, -4560], ![-1525, -2797, 7252]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [232, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 232], [0, 1]]
 g := ![![[122, 232], [169], [205], [199, 51], [159], [101, 30], [122, 1]], ![[0, 1], [169], [205], [130, 182], [159], [33, 203], [11, 232]]]
 h' := ![![[122, 232], [140, 144], [196, 220], [199, 111], [108, 135], [101, 208], [122, 206], [0, 1]], ![[0, 1], [0, 89], [8, 13], [227, 122], [35, 98], [80, 25], [90, 27], [122, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [92, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [232, 111, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78778, 16716, 4641]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, -1701, 4641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52712, -10983, -3090]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-52712, -10983, -3090]] 
 ![![233, 0, 0], ![22, 1, 0], ![39, 0, 1]] where
  M :=![![![-52712, -10983, -3090], ![-884076, -184205, -51825], ![-2767617, -576657, -162239]]]
  hmulB := by decide  
  f := ![![![14030, 807, -525]], ![![703, 52, -30]], ![![3531, 162, -119]]]
  g := ![![![1328, -10983, -3090], ![22273, -184205, -51825], ![69726, -576657, -162239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-14030, -807, 525]] ![![-52712, -10983, -3090]]
  ![![233, 0, 0]] where
 M := ![![![-233, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![46, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![46, 1, 0]] 
 ![![239, 0, 0], ![46, 1, 0], ![46, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![46, 1, 0], ![2, 47, 5], ![279, 39, 45]]]
  hmulB := by decide  
  f := ![![![-2403, -58654, -6240], ![-478, 298272, 0]], ![![-480, -11280, -1200], ![1, 57360, 0]], ![![-460, -11289, -1201], ![-105, 57408, 0]]]
  g := ![![![1, 0, 0], ![-46, 239, 0], ![-46, 0, 239]], ![![0, 1, 0], ![-10, 47, 5], ![-15, 39, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![70, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![70, 1, 0]] 
 ![![239, 0, 0], ![70, 1, 0], ![58, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![70, 1, 0], ![2, 71, 5], ![279, 39, 69]]]
  hmulB := by decide  
  f := ![![![-56979, -2296030, -161700], ![-26290, 7729260, 0]], ![![-16702, -672409, -47355], ![-7647, 2263569, 0]], ![![-13858, -557196, -39241], ![-6276, 1875720, 0]]]
  g := ![![![1, 0, 0], ![-70, 239, 0], ![-58, 0, 239]], ![![0, 1, 0], ![-22, 71, 5], ![-27, 39, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-116, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-116, 1, 0]] 
 ![![239, 0, 0], ![123, 1, 0], ![57, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-116, 1, 0], ![2, -115, 5], ![279, 39, -117]]]
  hmulB := by decide  
  f := ![![![36233, -2910296, 126540], ![-29636, -6048612, 0]], ![![18625, -1497696, 65120], ![-15295, -3112736, 0]], ![![8719, -694088, 30179], ![-6908, -1442556, 0]]]
  g := ![![![1, 0, 0], ![-123, 239, 0], ![-57, 0, 239]], ![![-1, 1, 0], ![58, -115, 5], ![9, 39, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![46, 1, 0]] ![![239, 0, 0], ![70, 1, 0]]
  ![![239, 0, 0], ![23, -120, 1]] where
 M := ![![![57121, 0, 0], ![16730, 239, 0]], ![![10994, 239, 0], ![3222, 117, 5]]]
 hmul := by decide  
 g := ![![![![216, 120, -1], ![239, 0, 0]], ![![47, 121, -1], ![239, 0, 0]]], ![![![23, 121, -1], ![239, 0, 0]], ![![13, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![23, -120, 1]] ![![239, 0, 0], ![-116, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-27724, 239, 0]], ![![5497, -28680, 239], ![-2629, 13862, -717]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-116, 1, 0]]], ![![![23, -120, 1]], ![![-11, 58, -3]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![53, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![53, 1, 0]] 
 ![![241, 0, 0], ![53, 1, 0], ![151, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![53, 1, 0], ![2, 54, 5], ![279, 39, 52]]]
  hmulB := by decide  
  f := ![![![12746, 371285, 34380], ![4579, -1657116, 0]], ![![2812, 81644, 7560], ![965, -364392, 0]], ![![7994, 232631, 21541], ![2833, -1038276, 0]]]
  g := ![![![1, 0, 0], ![-53, 241, 0], ![-151, 0, 241]], ![![0, 1, 0], ![-15, 54, 5], ![-40, 39, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![73, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![73, 1, 0]] 
 ![![241, 0, 0], ![73, 1, 0], ![125, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![73, 1, 0], ![2, 74, 5], ![279, 39, 72]]]
  hmulB := by decide  
  f := ![![![49350, 2093213, 141440], ![23859, -6817408, 0]], ![![14946, 634002, 42840], ![7231, -2064888, 0]], ![![25568, 1085691, 73361], ![12469, -3536000, 0]]]
  g := ![![![1, 0, 0], ![-73, 241, 0], ![-125, 0, 241]], ![![0, 1, 0], ![-25, 74, 5], ![-48, 39, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6611, -438, 14]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![6611, -438, 14]] 
 ![![241, 0, 0], ![115, 1, 0], ![128, 0, 1]] where
  M :=![![![6611, -438, 14], ![3030, 6719, -2204], ![-123546, -16410, 7595]]]
  hmulB := by decide  
  f := ![![![-14863165, -3096870, -871286]], ![![-8126749, -1693279, -476394]], ![![-11132234, -2319498, -652577]]]
  g := ![![![229, -438, 14], ![-2023, 6719, -2204], ![3284, -16410, 7595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![53, 1, 0]] ![![241, 0, 0], ![73, 1, 0]]
  ![![-14863165, -3096870, -871286]] where
 M := ![![![58081, 0, 0], ![17593, 241, 0]], ![![12773, 241, 0], ![3871, 127, 5]]]
 hmul := by decide  
 g := ![![![![1593251, -105558, 3374]], ![![485633, -25255, -1182]]], ![![![353413, -16495, -1462]], ![![105221, -3835, -779]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-14863165, -3096870, -871286]] ![![6611, -438, 14]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![89, 1, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![89, 1, 0]] 
 ![![251, 0, 0], ![89, 1, 0], ![55, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![89, 1, 0], ![2, 90, 5], ![279, 39, 88]]]
  hmulB := by decide  
  f := ![![![-10272, -554377, -30800], ![-5773, 1546160, 0]], ![![-3656, -196552, -10920], ![-2007, 548184, 0]], ![![-2248, -121477, -6749], ![-1273, 338800, 0]]]
  g := ![![![1, 0, 0], ![-89, 251, 0], ![-55, 0, 251]], ![![0, 1, 0], ![-33, 90, 5], ![-32, 39, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-50, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-50, 1, 0]] 
 ![![251, 0, 0], ![201, 1, 0], ![163, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-50, 1, 0], ![2, -49, 5], ![279, 39, -51]]]
  hmulB := by decide  
  f := ![![![-2189, 57327, -5850], ![753, 293670, 0]], ![![-1721, 45861, -4680], ![754, 234936, 0]], ![![-1407, 37228, -3799], ![562, 190710, 0]]]
  g := ![![![1, 0, 0], ![-201, 251, 0], ![-163, 0, 251]], ![![-1, 1, 0], ![36, -49, 5], ![3, 39, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-39, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-39, 1, 0]] 
 ![![251, 0, 0], ![212, 1, 0], ![206, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-39, 1, 0], ![2, -38, 5], ![279, 39, -40]]]
  hmulB := by decide  
  f := ![![![36306, -714215, 93980], ![-8283, -4717796, 0]], ![![30659, -603222, 79375], ![-7027, -3984625, 0]], ![![29778, -586168, 77131], ![-6920, -3871976, 0]]]
  g := ![![![1, 0, 0], ![-212, 251, 0], ![-206, 0, 251]], ![![-1, 1, 0], ![28, -38, 5], ![1, 39, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![89, 1, 0]] ![![251, 0, 0], ![-50, 1, 0]]
  ![![251, 0, 0], ![14, 8, 1]] where
 M := ![![![63001, 0, 0], ![-12550, 251, 0]], ![![22339, 251, 0], ![-4448, 40, 5]]]
 hmul := by decide  
 g := ![![![![237, -8, -1], ![251, 0, 0]], ![![-50, 1, 0], ![0, 0, 0]]], ![![![75, -7, -1], ![251, 0, 0]], ![![-18, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![14, 8, 1]] ![![251, 0, 0], ![-39, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-9789, 251, 0]], ![![3514, 2008, 251], ![-251, -251, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-39, 1, 0]]], ![![![14, 8, 1]], ![![-1, -1, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-95, -127, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-95, -127, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![162, 130, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-95, -127, 1], ![25, -183, -636], ![-35529, -4905, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-162, -130, 257]], ![![-1, -1, 1], ![401, 321, -636], ![-183, -55, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [93, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 256], [0, 1]]
 g := ![![[96, 50], [84], [157], [121], [49], [239], [120], [1]], ![[105, 207], [84], [157], [121], [49], [239], [120], [1]]]
 h' := ![![[67, 256], [253, 214], [94, 220], [139, 97], [37, 246], [15, 250], [59, 204], [164, 67], [0, 1]], ![[0, 1], [199, 43], [185, 37], [213, 160], [71, 11], [60, 7], [106, 53], [27, 190], [67, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [219, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [93, 190, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9076, 1991, 642]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-440, -317, 642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![122, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![122, 1, 0]] 
 ![![257, 0, 0], ![122, 1, 0], ![186, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![122, 1, 0], ![2, 123, 5], ![279, 39, 121]]]
  hmulB := by decide  
  f := ![![![-1019, -77734, -3160], ![-514, 162424, 0]], ![![-478, -36899, -1500], ![-256, 77100, 0]], ![![-756, -56259, -2287], ![-333, 117552, 0]]]
  g := ![![![1, 0, 0], ![-122, 257, 0], ![-186, 0, 257]], ![![0, 1, 0], ![-62, 123, 5], ![-105, 39, 121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-95, -127, 1]] ![![257, 0, 0], ![122, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![31354, 257, 0]], ![![-24415, -32639, 257], ![-11565, -15677, -514]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![122, 1, 0]]], ![![![-95, -127, 1]], ![![-45, -61, -2]]]]
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


lemma PB264I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB264I4 : PrimesBelowBoundCertificateInterval O 193 257 264 where
  m := 11
  g := ![1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB264I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
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
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![239, 239, 239]
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
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
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
  β := ![I199N0, I199N1, I199N2, I223N1, I233N1, I239N0, I239N1, I239N2, I241N0, I241N1, I241N2, I251N0, I251N1, I251N2, I257N1]
  Il := ![[], [I199N0, I199N1, I199N2], [], [I223N1], [], [], [I233N1], [I239N0, I239N1, I239N2], [I241N0, I241N1, I241N2], [I251N0, I251N1, I251N2], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
