
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![4, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![4, 1, 0]] 
 ![![197, 0, 0], ![4, 1, 0], ![187, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![4, 1, 0], ![0, 5, 2], ![-754, 117, 4]]]
  hmulB := by decide  
  f := ![![![577, 144, 0], ![-28368, 0, 0]], ![![4, 1, 0], ![-196, 0, 0]], ![![551, 135, -1], ![-27090, 99, 0]]]
  g := ![![![1, 0, 0], ![-4, 197, 0], ![-187, 0, 197]], ![![0, 1, 0], ![-2, 5, 2], ![-10, 117, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-326327, 65610, -7536]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-326327, 65610, -7536]] 
 ![![197, 0, 0], ![62, 1, 0], ![17, 0, 1]] where
  M :=![![![-326327, 65610, -7536], ![5682144, -1142429, 131220], ![-52311012, 10517442, -1208039]]]
  hmulB := by decide  
  f := ![![![-47491, 4122, 744]], ![![-17794, 1519, 276]], ![![-18451, 1380, 265]]]
  g := ![![![-21655, 65610, -7536], ![377066, -1142429, 131220], ![-3471349, 10517442, -1208039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-67, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-67, 1, 0]] 
 ![![197, 0, 0], ![130, 1, 0], ![153, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-67, 1, 0], ![0, -66, 2], ![-754, 117, -67]]]
  hmulB := by decide  
  f := ![![![3485, -52, 0], ![10244, 0, 0]], ![![2346, -35, 0], ![6896, 0, 0]], ![![2759, -8, -1], ![8110, 99, 0]]]
  g := ![![![1, 0, 0], ![-130, 197, 0], ![-153, 0, 197]], ![![-1, 1, 0], ![42, -66, 2], ![-29, 117, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![4, 1, 0]] ![![-326327, 65610, -7536]]
  ![![197, 0, 0], ![-73, -65, 1]] where
 M := ![![![-64286419, 12925170, -1484592]], ![![4376836, -879989, 101076]]]
 hmul := by decide  
 g := ![![![![-296762, 91935, -7941], ![79785, 0, 0]]], ![![![20252, -6217, 540], ![-5304, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-73, -65, 1]] ![![197, 0, 0], ![-67, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-13199, 197, 0]], ![![-14381, -12805, 197], ![4137, 4334, -197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-67, 1, 0]]], ![![![-73, -65, 1]], ![![21, 22, -1]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![61, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![61, 1, 0]] 
 ![![199, 0, 0], ![61, 1, 0], ![99, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![61, 1, 0], ![0, 62, 2], ![-754, 117, 61]]]
  hmulB := by decide  
  f := ![![![3051, 50, 0], ![-9950, 0, 0]], ![![915, 15, 0], ![-2984, 0, 0]], ![![1535, -6, -1], ![-5006, 100, 0]]]
  g := ![![![1, 0, 0], ![-61, 199, 0], ![-99, 0, 199]], ![![0, 1, 0], ![-20, 62, 2], ![-70, 117, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-31, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-31, 1, 0]] 
 ![![199, 0, 0], ![168, 1, 0], ![132, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-31, 1, 0], ![0, -30, 2], ![-754, 117, -31]]]
  hmulB := by decide  
  f := ![![![4093, -132, 0], ![26268, 0, 0]], ![![3442, -111, 0], ![22090, 0, 0]], ![![2700, -72, -1], ![17328, 100, 0]]]
  g := ![![![1, 0, 0], ![-168, 199, 0], ![-132, 0, 199]], ![![-1, 1, 0], ![24, -30, 2], ![-82, 117, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![61, 1, 0]] ![![199, 0, 0], ![-31, 1, 0]]
  ![![199, 0, 0], ![-50, -84, 1]] where
 M := ![![![39601, 0, 0], ![-6169, 199, 0]], ![![12139, 199, 0], ![-1891, 31, 2]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![19, 85, -1], ![199, 0, 0]]], ![![![61, 1, 0], ![0, 0, 0]], ![![-9, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-50, -84, 1]] ![![199, 0, 0], ![-31, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-6169, 199, 0]], ![![-9950, -16716, 199], ![796, 2587, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-31, 1, 0]]], ![![![-50, -84, 1]], ![![4, 13, -1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-138, 96, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-138, 96, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![73, 96, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-138, 96, 1], ![-754, 75, 192], ![-72007, 10855, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -96, 211]], ![![-1, 0, 1], ![-70, -87, 192], ![-334, 61, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [75, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 210], [0, 1]]
 g := ![![[67, 44], [128, 199], [53], [73], [206, 62], [117], [39, 1]], ![[95, 167], [82, 12], [53], [73], [92, 149], [117], [78, 210]]]
 h' := ![![[39, 210], [106, 39], [107, 58], [110, 105], [164, 101], [84, 22], [29, 180], [0, 1]], ![[0, 1], [150, 172], [48, 153], [196, 106], [94, 110], [98, 189], [86, 31], [39, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [182, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [75, 172, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5580, -2329, 545]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-215, -259, 545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![19, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![19, 1, 0]] 
 ![![211, 0, 0], ![19, 1, 0], ![21, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![19, 1, 0], ![0, 20, 2], ![-754, 117, 19]]]
  hmulB := by decide  
  f := ![![![1711, 90, 0], ![-18990, 0, 0]], ![![133, 7, 0], ![-1476, 0, 0]], ![![153, -2, -1], ![-1698, 106, 0]]]
  g := ![![![1, 0, 0], ![-19, 211, 0], ![-21, 0, 211]], ![![0, 1, 0], ![-2, 20, 2], ![-16, 117, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-138, 96, 1]] ![![211, 0, 0], ![19, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![4009, 211, 0]], ![![-29118, 20256, 211], ![-3376, 1899, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![19, 1, 0]]], ![![![-138, 96, 1]], ![![-16, 9, 1]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [18, 79, 181, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 16, 109], [103, 206, 114], [0, 1]]
 g := ![![[214, 60, 153], [119, 37, 19], [100, 37, 82], [119, 156, 63], [21, 214, 127], [106, 203], [1]], ![[154, 73, 72, 162], [109, 28, 187, 211], [209, 187, 81, 25], [139, 107, 216, 124], [129, 88, 113, 19], [154, 120], [31, 184, 34, 68]], ![[59, 79, 78, 20], [79, 175, 208, 23], [158, 28, 173, 176], [145, 207, 140, 206], [210, 157, 184, 207], [11, 199], [128, 175, 3, 155]]]
 h' := ![![[162, 16, 109], [88, 1, 162], [207, 70, 165], [88, 220, 159], [68, 147, 78], [200, 182, 57], [205, 144, 42], [0, 1]], ![[103, 206, 114], [191, 134, 31], [85, 183, 142], [19, 10, 92], [133, 121, 202], [124, 38, 137], [144, 22, 41], [162, 16, 109]], ![[0, 1], [181, 88, 30], [213, 193, 139], [50, 216, 195], [98, 178, 166], [4, 3, 29], [176, 57, 140], [103, 206, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 138], []]
 b := ![[], [146, 188, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [18, 79, 181, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16779635, -5903479, 1199294]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![75245, -26473, 5378]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![339732, 41302, 2367]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![339732, 41302, 2367]] 
 ![![227, 0, 0], ![0, 227, 0], ![191, 42, 1]] where
  M :=![![![339732, 41302, 2367], ![-1784718, 657973, 82604], ![-30249349, 3939975, 616671]]]
  hmulB := by decide  
  f := ![![![353723229, -71118171, 8168671]], ![![-6159177934, 1238339565, -142236342]], ![![-592165844, 119058485, -13675121]]]
  g := ![![![-495, -256, 2367], ![-77366, -12385, 82604], ![-652130, -96741, 616671]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [52, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [173, 226], [0, 1]]
 g := ![![[132, 122], [90, 185], [144], [89], [103], [13, 78], [173, 1]], ![[127, 105], [88, 42], [144], [89], [103], [114, 149], [119, 226]]]
 h' := ![![[173, 226], [87, 203], [137, 171], [208, 215], [117, 166], [5, 28], [84, 140], [0, 1]], ![[0, 1], [21, 24], [210, 56], [175, 12], [6, 61], [82, 199], [15, 87], [173, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [202, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [52, 54, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1069, -377, 191]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-156, -37, 191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-353723229, 71118171, -8168671]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-353723229, 71118171, -8168671]] 
 ![![227, 0, 0], ![143, 1, 0], ![146, 0, 1]] where
  M :=![![![-353723229, 71118171, -8168671], ![6159177934, -1238339565, 142236342], ![-56702689901, 11400414974, -1309457736]]]
  hmulB := by decide  
  f := ![![![-339732, -41302, -2367]], ![![-206154, -28917, -1855]], ![![-85249, -43921, -4239]]]
  g := ![![![-41105708, 71118171, -8168671], ![715749911, -1238339565, 142236342], ![-6589344501, 11400414974, -1309457736]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![339732, 41302, 2367]] ![![-353723229, 71118171, -8168671]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![10, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![10, 1, 0]] 
 ![![229, 0, 0], ![10, 1, 0], ![174, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![10, 1, 0], ![0, 11, 2], ![-754, 117, 10]]]
  hmulB := by decide  
  f := ![![![211, 21, 0], ![-4809, 0, 0]], ![![-10, -1, 0], ![230, 0, 0]], ![![166, 11, -1], ![-3784, 115, 0]]]
  g := ![![![1, 0, 0], ![-10, 229, 0], ![-174, 0, 229]], ![![0, 1, 0], ![-2, 11, 2], ![-16, 117, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-990, 26, 9]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-990, 26, 9]] 
 ![![229, 0, 0], ![81, 1, 0], ![114, 0, 1]] where
  M :=![![![-990, 26, 9], ![-6786, 89, 52], ![-16211, -351, 63]]]
  hmulB := by decide  
  f := ![![![-23859, 4797, -551]], ![![-6625, 1332, -153]], ![![-28579, 5746, -660]]]
  g := ![![![-18, 26, 9], ![-87, 89, 52], ![22, -351, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-92, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-92, 1, 0]] 
 ![![229, 0, 0], ![137, 1, 0], ![165, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-92, 1, 0], ![0, -91, 2], ![-754, 117, -92]]]
  hmulB := by decide  
  f := ![![![15549, -169, 0], ![38701, 0, 0]], ![![9385, -102, 0], ![23359, 0, 0]], ![![11197, -76, -1], ![27869, 115, 0]]]
  g := ![![![1, 0, 0], ![-137, 229, 0], ![-165, 0, 229]], ![![-1, 1, 0], ![53, -91, 2], ![-7, 117, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![10, 1, 0]] ![![-990, 26, 9]]
  ![![229, 0, 0], ![-53, 46, 1]] where
 M := ![![![-226710, 5954, 2061]], ![![-16686, 349, 142]]]
 hmul := by decide  
 g := ![![![![-937, -20, 8], ![229, 0, 0]]], ![![![-40, -27, 0], ![142, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-53, 46, 1]] ![![229, 0, 0], ![-92, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-21068, 229, 0]], ![![-12137, 10534, 229], ![4122, -4122, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-92, 1, 0]]], ![![![-53, 46, 1]], ![![18, -18, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-119, 11, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-119, 11, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![114, 11, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-119, 11, 1], ![-754, 9, 22], ![-7917, 910, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -11, 233]], ![![-1, 0, 1], ![-14, -1, 22], ![-33, 4, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [110, 204, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 232], [0, 1]]
 g := ![![[112, 197], [102], [152], [192, 225], [129], [53, 92], [29, 1]], ![[0, 36], [102], [152], [193, 8], [129], [158, 141], [58, 232]]]
 h' := ![![[29, 232], [125, 68], [188, 58], [83, 131], [48, 218], [228, 96], [72, 32], [0, 1]], ![[0, 1], [0, 165], [6, 175], [154, 102], [79, 15], [216, 137], [68, 201], [29, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [82, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [110, 204, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5340, -7493, 1903]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-954, -122, 1903]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-22, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-22, 1, 0]] 
 ![![233, 0, 0], ![211, 1, 0], ![2, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-22, 1, 0], ![0, -21, 2], ![-754, 117, -22]]]
  hmulB := by decide  
  f := ![![![1519, -69, 0], ![16077, 0, 0]], ![![1365, -62, 0], ![14447, 0, 0]], ![![34, 9, -1], ![360, 117, 0]]]
  g := ![![![1, 0, 0], ![-211, 233, 0], ![-2, 0, 233]], ![![-1, 1, 0], ![19, -21, 2], ![-109, 117, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-119, 11, 1]] ![![233, 0, 0], ![-22, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-5126, 233, 0]], ![![-27727, 2563, 233], ![1864, -233, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-22, 1, 0]]], ![![![-119, 11, 1]], ![![8, -1, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173583, -16591, -2885]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![173583, -16591, -2885]] 
 ![![239, 0, 0], ![0, 239, 0], ![10, 34, 1]] where
  M :=![![![173583, -16591, -2885], ![2175290, -180553, -33182], ![11421969, -853502, -163962]]]
  hmulB := by decide  
  f := ![![![-5367898, 1079248, -123963]], ![![93468102, -18792321, 2158496]], ![![9471755, -1904353, 218735]]]
  g := ![![![847, 341, -2885], ![10490, 3965, -33182], ![54651, 19754, -163962]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [139, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 238], [0, 1]]
 g := ![![[77, 60], [181, 174], [77, 18], [87, 193], [60], [58, 33], [52, 1]], ![[90, 179], [147, 65], [57, 221], [85, 46], [60], [101, 206], [104, 238]]]
 h' := ![![[52, 238], [175, 119], [52, 202], [96, 181], [58, 77], [64, 120], [181, 175], [0, 1]], ![[0, 1], [149, 120], [40, 37], [187, 58], [238, 162], [90, 119], [199, 64], [52, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [142, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [139, 187, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5516, -2359, 500]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -81, 500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5367898, -1079248, 123963]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![5367898, -1079248, 123963]] 
 ![![239, 0, 0], ![171, 1, 0], ![112, 0, 1]] where
  M :=![![![5367898, -1079248, 123963], ![-93468102, 18792321, -2158496], ![860487043, -173006067, 19871569]]]
  hmulB := by decide  
  f := ![![![-173583, 16591, 2885]], ![![-133297, 12626, 2203]], ![![-129135, 11346, 2038]]]
  g := ![![![736550, -1079248, 123963], ![-12825119, 18792321, -2158496], ![118070748, -173006067, 19871569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![173583, -16591, -2885]] ![![5367898, -1079248, 123963]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [125, 206, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 83, 122], [193, 157, 119], [0, 1]]
 g := ![![[124, 12, 221], [82, 194], [235, 174], [124, 221], [25, 156, 166], [87, 164, 193], [1]], ![[69, 204, 90, 235], [], [62, 32], [101, 212], [123, 91, 178, 58], [11, 162, 92, 217], [103, 105, 202, 154]], ![[100, 107, 156, 67], [225, 194], [154, 196], [7, 18], [95, 14, 78, 162], [42, 92, 195, 59], [138, 228, 213, 87]]]
 h' := ![![[165, 83, 122], [193, 115, 71], [171, 10, 26], [229, 149, 74], [8, 109, 71], [211, 98, 155], [116, 35, 117], [0, 1]], ![[193, 157, 119], [229, 100, 113], [62, 63], [231, 62, 153], [18, 84, 104], [157, 67, 141], [24, 56, 226], [165, 83, 122]], ![[0, 1], [232, 26, 57], [94, 168, 215], [8, 30, 14], [94, 48, 66], [199, 76, 186], [129, 150, 139], [193, 157, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198, 11], []]
 b := ![[], [221, 29, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [125, 206, 124, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![635372882, -477521497, 122891202]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2636402, -1981417, 509922]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [166, 99, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 198, 52], [231, 52, 199], [0, 1]]
 g := ![![[127, 98, 94], [106, 131, 13], [56, 198], [131, 11, 25], [58, 208, 195], [178, 242, 73], [1]], ![[8, 242, 152, 195], [117, 232, 60, 1], [], [161, 138, 227, 69], [62, 165, 147, 15], [215, 243, 54, 205], [95, 141, 167, 48]], ![[110, 59, 219, 235], [142, 54, 25, 24], [87, 198], [112, 64, 171, 148], [116, 159, 124, 109], [233, 98, 56, 143], [140, 175, 4, 203]]]
 h' := ![![[2, 198, 52], [225, 9, 211], [240, 106, 55], [91, 82, 169], [161, 21, 5], [70, 133, 114], [85, 152, 233], [0, 1]], ![[231, 52, 199], [217, 215, 145], [174, 82, 89], [26, 185], [18, 181, 97], [134, 65, 43], [51, 187, 191], [2, 198, 52]], ![[0, 1], [51, 27, 146], [57, 63, 107], [145, 235, 82], [54, 49, 149], [179, 53, 94], [135, 163, 78], [231, 52, 199]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 188], []]
 b := ![[], [59, 188, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [166, 99, 18, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-252506, -10291, 14307]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1006, -41, 57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

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


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [221, 154, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 47, 216], [137, 209, 41], [0, 1]]
 g := ![![[143, 147, 231], [101, 141], [223, 62], [111, 223], [185, 46], [136, 89], [145, 1], []], ![[229, 113, 93, 251], [114, 140], [69, 199], [248, 231], [175, 32], [6, 68], [155, 248], [110, 139]], ![[22, 153, 215, 138], [214, 248], [182, 124], [201, 67], [74, 178], [207, 114], [249, 153], [28, 139]]]
 h' := ![![[8, 47, 216], [154, 201, 105], [87, 246, 107], [119, 69, 24], [122, 9, 123], [245, 113, 118], [80, 65, 54], [0, 0, 1], [0, 1]], ![[137, 209, 41], [232, 108, 83], [92, 158, 198], [101, 51, 131], [164, 255, 152], [17, 154, 240], [217, 242, 140], [169, 124, 209], [8, 47, 216]], ![[0, 1], [217, 205, 69], [123, 110, 209], [32, 137, 102], [136, 250, 239], [175, 247, 156], [113, 207, 63], [245, 133, 47], [137, 209, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237, 127], []]
 b := ![[], [135, 116, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [221, 154, 112, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19678490, -8687885, 1950630]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76570, -33805, 7590]
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



lemma PB274I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB274I4 : PrimesBelowBoundCertificateInterval O 193 257 274 where
  m := 11
  g := ![3, 3, 2, 1, 2, 3, 2, 2, 1, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0]
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
    · exact ![197, 197, 197]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![229, 229, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![15813251]
    · exact ![16974593]
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
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N0, I197N1, I197N2, I199N0, I199N1, I211N1, I227N1, I229N0, I229N1, I229N2, I233N1, I239N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N0, I199N1, I199N1], [I211N1], [], [I227N1], [I229N0, I229N1, I229N2], [I233N1], [I239N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
