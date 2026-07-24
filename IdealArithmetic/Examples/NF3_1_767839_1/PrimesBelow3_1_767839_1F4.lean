
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![9, 61, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![9, 61, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![9, 61, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![9, 61, 1], ![155, -22, 61], ![9455, -1736, -22]]]
  hmulB := by decide  
  f := ![![![-8, -61, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -61, 197]], ![![0, 0, 1], ![-2, -19, 61], ![49, -2, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [132, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 196], [0, 1]]
 g := ![![[144, 100], [107], [45, 169], [156], [107], [90], [101, 1]], ![[0, 97], [107], [172, 28], [156], [107], [90], [5, 196]]]
 h' := ![![[101, 196], [172, 10], [167, 111], [185, 184], [17, 133], [96, 86], [64, 22], [0, 1]], ![[0, 1], [0, 187], [149, 86], [54, 13], [54, 64], [114, 111], [119, 175], [101, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [74, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [132, 96, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442, -3, -126]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 39, -126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-61, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-61, 1, 0]] 
 ![![197, 0, 0], ![136, 1, 0], ![22, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-61, 1, 0], ![0, -61, 1], ![155, -31, -61]]]
  hmulB := by decide  
  f := ![![![3783, -62, 0], ![12214, 0, 0]], ![![2624, -43, 0], ![8472, 0, 0]], ![![446, -7, 0], ![1440, 1, 0]]]
  g := ![![![1, 0, 0], ![-136, 197, 0], ![-22, 0, 197]], ![![-1, 1, 0], ![42, -61, 1], ![29, -31, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![9, 61, 1]] ![![197, 0, 0], ![-61, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-12017, 197, 0]], ![![1773, 12017, 197], ![-394, -3743, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-61, 1, 0]]], ![![![9, 61, 1]], ![![-2, -19, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [45, 197, 189, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 61, 112], [179, 137, 87], [0, 1]]
 g := ![![[132, 152, 63], [179, 48, 169], [99, 3, 116], [183, 52], [29, 20], [45, 100], [1]], ![[194, 186, 130, 45], [89, 103, 10, 116], [56, 129, 196, 2], [167, 66], [156, 46], [44, 4], [98, 16, 166, 187]], ![[110, 119, 37, 166], [121, 163, 128, 78], [171, 198, 125, 183], [170, 104], [110, 125], [119, 144], [170, 48, 12, 12]]]
 h' := ![![[30, 61, 112], [104, 147, 62], [122, 155, 186], [106, 79, 135], [88, 153, 101], [0, 186, 152], [154, 2, 10], [0, 1]], ![[179, 137, 87], [5, 18, 83], [1, 120, 57], [82, 101, 80], [154, 131, 128], [72, 114, 65], [103, 1, 2], [30, 61, 112]], ![[0, 1], [161, 34, 54], [43, 123, 155], [35, 19, 183], [116, 114, 169], [84, 98, 181], [71, 196, 187], [179, 137, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 53], []]
 b := ![[], [109, 79, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [45, 197, 189, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![560981, 23482, -35223]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2819, 118, -177]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [24, 112, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 145, 205], [157, 65, 6], [0, 1]]
 g := ![![[179, 66, 45], [183, 183, 114], [83, 52], [32, 69], [144, 102, 14], [145, 20], [1]], ![[127, 205, 200, 160], [10, 80, 124, 67], [11, 16], [61, 180], [196, 178, 139, 177], [52, 208], [7, 71, 63, 206]], ![[0, 167, 207, 107], [206, 154, 91, 125], [134, 163], [109, 150], [186, 76, 45, 82], [196, 73], [88, 103, 40, 5]]]
 h' := ![![[135, 145, 205], [39, 158, 195], [123, 71, 122], [146, 105, 120], [131, 171, 51], [50, 50, 15], [187, 99, 81], [0, 1]], ![[157, 65, 6], [104, 3, 122], [126, 204, 119], [50, 187, 207], [44, 184, 179], [84, 148, 42], [158, 16, 29], [135, 145, 205]], ![[0, 1], [0, 50, 105], [184, 147, 181], [92, 130, 95], [78, 67, 192], [162, 13, 154], [151, 96, 101], [157, 65, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197, 160], []]
 b := ![[], [15, 25, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [24, 112, 130, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![244127, -5697, 5697]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1157, -27, 27]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![87, 112, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![87, 112, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![87, 112, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![87, 112, 1], ![155, 56, 112], ![17360, -3317, 56]]]
  hmulB := by decide  
  f := ![![![-86, -112, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -112, 223]], ![![0, 0, 1], ![-43, -56, 112], ![56, -43, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [9, 202, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 222], [0, 1]]
 g := ![![[72, 124], [199, 33], [186, 30], [55, 98], [21, 203], [196], [21, 1]], ![[0, 99], [0, 190], [147, 193], [106, 125], [47, 20], [196], [42, 222]]]
 h' := ![![[21, 222], [216, 149], [110, 16], [174, 91], [34, 105], [61, 42], [34, 209], [0, 1]], ![[0, 1], [0, 74], [0, 207], [78, 132], [9, 118], [51, 181], [186, 14], [21, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [43, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [9, 202, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-718, 1785, -890]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![344, 455, -890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![111, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![111, 1, 0]] 
 ![![223, 0, 0], ![111, 1, 0], ![167, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![111, 1, 0], ![0, 111, 1], ![155, -31, 111]]]
  hmulB := by decide  
  f := ![![![4996, 45, 0], ![-10035, 0, 0]], ![![2442, 22, 0], ![-4905, 0, 0]], ![![3830, 34, 0], ![-7693, 1, 0]]]
  g := ![![![1, 0, 0], ![-111, 223, 0], ![-167, 0, 223]], ![![0, 1, 0], ![-56, 111, 1], ![-67, -31, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![87, 112, 1]] ![![223, 0, 0], ![111, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![24753, 223, 0]], ![![19401, 24976, 223], ![9812, 12488, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![111, 1, 0]]], ![![![87, 112, 1]], ![![44, 56, 1]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [156, 73, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 163, 134], [2, 63, 93], [0, 1]]
 g := ![![[52, 136, 136], [161, 79, 213], [40, 27], [24, 212], [33, 59], [164, 6, 212], [1]], ![[48, 164, 220, 175], [134, 110, 14, 49], [36, 161], [157, 213], [44, 81], [31, 155, 7, 11], [128, 7, 74, 131]], ![[205, 212, 80, 224], [170, 31, 137, 91], [98, 57], [92, 159], [23, 113], [119, 209, 32, 148], [141, 199, 84, 96]]]
 h' := ![![[60, 163, 134], [81, 204, 131], [30, 62, 101], [145, 125, 77], [22, 201, 165], [67, 78, 115], [71, 154, 62], [0, 1]], ![[2, 63, 93], [108, 194, 177], [21, 58, 143], [125, 133, 36], [151, 186, 101], [146, 100, 218], [131, 21, 26], [60, 163, 134]], ![[0, 1], [10, 56, 146], [107, 107, 210], [58, 196, 114], [91, 67, 188], [156, 49, 121], [31, 52, 139], [2, 63, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 29], []]
 b := ![[], [149, 156, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [156, 73, 165, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41541, 21565, -6356]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![183, 95, -28]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![106, 103, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![106, 103, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![106, 103, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![106, 103, 1], ![155, 75, 103], ![15965, -3038, 75]]]
  hmulB := by decide  
  f := ![![![-105, -103, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -103, 229]], ![![0, 0, 1], ![-47, -46, 103], ![35, -47, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [38, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 228], [0, 1]]
 g := ![![[43, 193], [196], [98, 158], [213], [5], [88, 49], [198, 1]], ![[14, 36], [196], [9, 71], [213], [5], [172, 180], [167, 228]]]
 h' := ![![[198, 228], [45, 184], [169, 215], [201, 58], [76, 199], [91, 163], [33, 7], [0, 1]], ![[0, 1], [66, 45], [145, 14], [6, 171], [90, 30], [76, 66], [45, 222], [198, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [118, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [38, 31, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5960, -396, 363]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-142, -165, 363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-103, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-103, 1, 0]] 
 ![![229, 0, 0], ![126, 1, 0], ![154, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-103, 1, 0], ![0, -103, 1], ![155, -31, -103]]]
  hmulB := by decide  
  f := ![![![22970, -223, 0], ![51067, 0, 0]], ![![12670, -123, 0], ![28168, 0, 0]], ![![15600, -151, 0], ![34682, 1, 0]]]
  g := ![![![1, 0, 0], ![-126, 229, 0], ![-154, 0, 229]], ![![-1, 1, 0], ![56, -103, 1], ![87, -31, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![106, 103, 1]] ![![229, 0, 0], ![-103, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-23587, 229, 0]], ![![24274, 23587, 229], ![-10763, -10534, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-103, 1, 0]]], ![![![106, 103, 1]], ![![-47, -46, 0]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [77, 184, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 223, 15], [185, 9, 218], [0, 1]]
 g := ![![[44, 86, 181], [49, 201], [192, 208], [196, 217, 144], [72, 13], [74, 63, 219], [1]], ![[7, 126, 131, 76], [65, 9], [216, 152], [96, 86, 160, 32], [191, 85], [30, 46, 164, 167], [206, 9, 150, 113]], ![[110, 71, 8, 133], [228, 30], [222, 217], [195, 148, 125, 109], [144, 159], [168, 72, 117, 217], [15, 147, 107, 120]]]
 h' := ![![[107, 223, 15], [31, 25, 119], [141, 158, 203], [53, 99, 212], [100, 189, 12], [127, 44, 53], [156, 49, 59], [0, 1]], ![[185, 9, 218], [179, 162, 48], [72, 0, 3], [45, 116, 131], [85, 41, 147], [146, 186, 205], [144, 53, 101], [107, 223, 15]], ![[0, 1], [170, 46, 66], [22, 75, 27], [177, 18, 123], [158, 3, 74], [166, 3, 208], [93, 131, 73], [185, 9, 218]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 46], []]
 b := ![[], [107, 144, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [77, 184, 174, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-222049, 71065, -2330]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-953, 305, -10]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [179, 77, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 221, 68], [179, 17, 171], [0, 1]]
 g := ![![[222, 117, 88], [7, 33, 170], [199, 236, 17], [187, 97, 54], [215, 155], [1, 94, 80], [1]], ![[197, 34, 109, 88], [161, 25, 129, 183], [114, 140, 3, 27], [131, 126, 43, 50], [220, 127], [27, 172, 103, 22], [52, 26, 234, 147]], ![[186, 237, 210, 38], [81, 5, 122, 52], [75, 170, 51, 137], [178, 94, 120, 233], [31, 204], [233, 89, 209, 141], [137, 183, 234, 92]]]
 h' := ![![[175, 221, 68], [181, 107, 142], [229, 201, 109], [226, 106, 223], [9, 75, 66], [60, 81, 148], [60, 162, 115], [0, 1]], ![[179, 17, 171], [88, 83, 130], [146, 97, 225], [137, 20, 5], [126, 18, 8], [166, 67, 137], [52, 76, 65], [175, 221, 68]], ![[0, 1], [159, 49, 206], [65, 180, 144], [66, 113, 11], [48, 146, 165], [229, 91, 193], [150, 1, 59], [179, 17, 171]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180, 116], []]
 b := ![[], [186, 75, 167], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [179, 77, 124, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211754, -2868, -5736]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![886, -12, -24]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-97, 63, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-97, 63, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![144, 63, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-97, 63, 1], ![155, -128, 63], ![9765, -1798, -128]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-144, -63, 241]], ![![-1, 0, 1], ![-37, -17, 63], ![117, 26, -128]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [29, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 240], [0, 1]]
 g := ![![[65, 133], [151], [107], [36], [238, 121], [186, 96], [43, 1]], ![[0, 108], [151], [107], [36], [139, 120], [217, 145], [86, 240]]]
 h' := ![![[43, 240], [196, 186], [113, 67], [18, 182], [87, 6], [149, 230], [199, 133], [0, 1]], ![[0, 1], [0, 55], [102, 174], [132, 59], [104, 235], [158, 11], [134, 108], [43, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199]]
 b := ![[], [90, 220]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [29, 198, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5771, -160, 380]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -100, 380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-63, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-63, 1, 0]] 
 ![![241, 0, 0], ![178, 1, 0], ![128, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-63, 1, 0], ![0, -63, 1], ![155, -31, -63]]]
  hmulB := by decide  
  f := ![![![7309, -116, 0], ![27956, 0, 0]], ![![5482, -87, 0], ![20968, 0, 0]], ![![3860, -61, 0], ![14764, 1, 0]]]
  g := ![![![1, 0, 0], ![-178, 241, 0], ![-128, 0, 241]], ![![-1, 1, 0], ![46, -63, 1], ![57, -31, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-97, 63, 1]] ![![241, 0, 0], ![-63, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-15183, 241, 0]], ![![-23377, 15183, 241], ![6266, -4097, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-63, 1, 0]]], ![![![-97, 63, 1]], ![![26, -17, 0]]]]
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


lemma PB248I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 247 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 247 (by omega)

def PB248I4 : PrimesBelowBoundCertificateInterval O 193 247 248 where
  m := 9
  g := ![2, 1, 1, 2, 1, 2, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB248I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0]
    · exact ![I241N0, I241N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![13651919]
    · exact ![58081, 241]
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
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
  β := ![I197N1, I223N1, I229N1, I241N1]
  Il := ![[I197N1], [], [], [I223N1], [], [I229N1], [], [], [I241N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
