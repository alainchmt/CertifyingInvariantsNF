
import IdealArithmetic.Examples.NF3_1_936091_1.RI3_1_936091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![52, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![52, 1, 0]] 
 ![![197, 0, 0], ![52, 1, 0], ![54, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![52, 1, 0], ![0, 52, 1], ![-194, 17, 53]]]
  hmulB := by decide  
  f := ![![![3017, 58, 0], ![-11426, 0, 0]], ![![780, 15, 0], ![-2954, 0, 0]], ![![742, 14, 0], ![-2810, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 197, 0], ![-54, 0, 197]], ![![0, 1, 0], ![-14, 52, 1], ![-20, 17, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![63, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![63, 1, 0]] 
 ![![197, 0, 0], ![63, 1, 0], ![168, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![63, 1, 0], ![0, 63, 1], ![-194, 17, 64]]]
  hmulB := by decide  
  f := ![![![5293, 84, 0], ![-16548, 0, 0]], ![![1701, 27, 0], ![-5318, 0, 0]], ![![4494, 71, 0], ![-14050, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 197, 0], ![-168, 0, 197]], ![![0, 1, 0], ![-21, 63, 1], ![-61, 17, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![81, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![81, 1, 0]] 
 ![![197, 0, 0], ![81, 1, 0], ![137, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![81, 1, 0], ![0, 81, 1], ![-194, 17, 82]]]
  hmulB := by decide  
  f := ![![![4861, 60, 0], ![-11820, 0, 0]], ![![2025, 25, 0], ![-4924, 0, 0]], ![![3355, 41, 0], ![-8158, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 197, 0], ![-137, 0, 197]], ![![0, 1, 0], ![-34, 81, 1], ![-65, 17, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![52, 1, 0]] ![![197, 0, 0], ![63, 1, 0]]
  ![![197, 0, 0], ![-73, -82, 1]] where
 M := ![![![38809, 0, 0], ![12411, 197, 0]], ![![10244, 197, 0], ![3276, 115, 1]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![63, 1, 0], ![0, 0, 0]]], ![![![52, 1, 0], ![0, 0, 0]], ![![17, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-73, -82, 1]] ![![197, 0, 0], ![81, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![15957, 197, 0]], ![![-14381, -16154, 197], ![-6107, -6698, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![81, 1, 0]]], ![![![-73, -82, 1]], ![![-31, -34, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [149, 31, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 138, 128], [93, 60, 71], [0, 1]]
 g := ![![[81, 42, 114], [25, 63, 70], [178, 86, 114], [79, 131], [125, 124], [152, 102], [1]], ![[171, 173, 128, 178], [111, 184, 107, 33], [167, 26, 140, 81], [4, 51], [50, 98], [139, 89], [4, 188, 5, 90]], ![[94, 64, 4, 105], [131, 95, 16, 24], [146, 158, 10, 84], [68, 26], [52, 121], [149, 25], [5, 108, 195, 109]]]
 h' := ![![[70, 138, 128], [56, 27, 121], [144, 88, 104], [50, 190, 121], [94, 48, 23], [150, 74, 70], [50, 168, 163], [0, 1]], ![[93, 60, 71], [42, 46, 169], [153, 3, 191], [103, 53, 138], [163, 91, 161], [38, 54, 140], [124, 116, 41], [70, 138, 128]], ![[0, 1], [157, 126, 108], [132, 108, 103], [186, 155, 139], [13, 60, 15], [0, 71, 188], [50, 114, 194], [93, 60, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 127], []]
 b := ![[], [80, 91, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [149, 31, 36, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40397, 1194, 1194]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-203, 6, 6]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-40, -70, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-40, -70, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![171, 141, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-40, -70, 1], ![-194, -23, -69], ![13386, -1367, -92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-171, -141, 211]], ![![-1, -1, 1], ![55, 46, -69], ![138, 55, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [205, 183, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 210], [0, 1]]
 g := ![![[75, 199], [104, 65], [20], [37], [200, 49], [173], [28, 1]], ![[161, 12], [25, 146], [20], [37], [95, 162], [173], [56, 210]]]
 h' := ![![[28, 210], [202, 153], [207, 109], [147, 81], [145, 44], [144, 204], [168, 157], [0, 1]], ![[0, 1], [55, 58], [94, 102], [94, 130], [111, 167], [159, 7], [133, 54], [28, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [93, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [205, 183, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![605, -2159, 697]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-562, -476, 697]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![69, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![69, 1, 0]] 
 ![![211, 0, 0], ![69, 1, 0], ![92, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![69, 1, 0], ![0, 69, 1], ![-194, 17, 70]]]
  hmulB := by decide  
  f := ![![![3037, 44, 0], ![-9284, 0, 0]], ![![897, 13, 0], ![-2742, 0, 0]], ![![1334, 19, 0], ![-4078, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 211, 0], ![-92, 0, 211]], ![![0, 1, 0], ![-23, 69, 1], ![-37, 17, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-40, -70, 1]] ![![211, 0, 0], ![69, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![14559, 211, 0]], ![![-8440, -14770, 211], ![-2954, -4853, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![69, 1, 0]]], ![![![-40, -70, 1]], ![![-14, -23, 0]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [63, 10, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 100, 76], [214, 122, 147], [0, 1]]
 g := ![![[53, 88, 202], [93, 210, 32], [100, 137, 218], [52, 22, 164], [110, 60, 119], [33, 9], [1]], ![[2, 120, 168, 144], [148, 32, 19, 66], [73, 149, 177, 175], [174, 177, 141, 183], [120, 52, 60, 65], [113, 121], [94, 162, 200, 112]], ![[160, 180, 148, 61], [125, 65, 217, 215], [117, 163, 80, 165], [206, 67, 132, 57], [147, 195, 8, 137], [14, 196], [90, 171, 89, 111]]]
 h' := ![![[6, 100, 76], [162, 126, 47], [167, 36, 60], [69, 167, 202], [206, 112, 68], [106, 140, 66], [160, 213, 220], [0, 1]], ![[214, 122, 147], [77, 124, 146], [97, 109, 21], [123, 93, 95], [93, 167, 83], [7, 58, 183], [92, 100, 212], [6, 100, 76]], ![[0, 1], [21, 196, 30], [138, 78, 142], [191, 186, 149], [127, 167, 72], [174, 25, 197], [68, 133, 14], [214, 122, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 187], []]
 b := ![[], [149, 110, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [63, 10, 3, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-328033, 58872, -15610]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1471, 264, -70]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [49, 90, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [152, 78, 43], [201, 148, 184], [0, 1]]
 g := ![![[210, 95, 7], [14, 125, 171], [214, 78], [83, 131], [156, 44], [182, 72, 213], [1]], ![[132, 118, 222, 48], [2, 8, 105, 169], [188, 112], [191, 155], [215, 181], [17, 88, 197, 47], [13, 187, 149, 57]], ![[52, 164, 212, 86], [19, 127, 91, 199], [100, 89], [14, 26], [182, 166], [18, 220, 101, 119], [136, 217, 206, 170]]]
 h' := ![![[152, 78, 43], [222, 118, 190], [100, 130, 25], [215, 130, 87], [213, 156, 178], [162, 199, 80], [178, 137, 126], [0, 1]], ![[201, 148, 184], [122, 16, 52], [199, 90, 210], [51, 136, 79], [199, 86, 137], [92, 160, 194], [162, 213, 23], [152, 78, 43]], ![[0, 1], [122, 93, 212], [181, 7, 219], [108, 188, 61], [106, 212, 139], [25, 95, 180], [49, 104, 78], [201, 148, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161, 186], []]
 b := ![[], [199, 62, 191], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [49, 90, 101, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-985861, -4086, 12258]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4343, -18, 54]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [13, 80, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 126, 215], [109, 102, 14], [0, 1]]
 g := ![![[64, 154, 167], [110, 91], [94, 52, 130], [71, 56], [15, 158], [80, 95, 151], [1]], ![[71, 148, 206, 161], [60, 71], [118, 133, 180, 217], [166, 37], [130, 37], [155, 39, 215, 97], [89, 34, 206, 4]], ![[226, 98, 197, 187], [201, 176], [26, 31, 143, 49], [96, 161], [85, 217], [126, 181, 45, 15], [184, 58, 122, 225]]]
 h' := ![![[84, 126, 215], [148, 124, 204], [152, 34, 70], [131, 46, 151], [67, 55, 96], [105, 91, 171], [216, 149, 193], [0, 1]], ![[109, 102, 14], [198, 182, 65], [156, 27, 23], [159, 156, 102], [213, 202, 91], [23, 226, 138], [40, 0, 196], [84, 126, 215]], ![[0, 1], [210, 152, 189], [126, 168, 136], [65, 27, 205], [54, 201, 42], [181, 141, 149], [161, 80, 69], [109, 102, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 200], []]
 b := ![[], [150, 223, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [13, 80, 36, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40533, 1145, 1145]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, 5, 5]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15033, 2026, 684]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-15033, 2026, 684]] 
 ![![233, 0, 0], ![0, 233, 0], ![210, 129, 1]] where
  M :=![![![-15033, 2026, 684], ![-132696, -3405, 2710], ![-525740, -86626, -695]]]
  hmulB := by decide  
  f := ![![![1017695, -248258, 33560]], ![![-6510640, 1588215, -214698]], ![![-2508606, 611953, -82725]]]
  g := ![![![-681, -370, 684], ![-3012, -1515, 2710], ![-1630, 13, -695]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [159, 208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 232], [0, 1]]
 g := ![![[205, 85], [85], [148], [109, 210], [204], [], [25, 1]], ![[0, 148], [85], [148], [0, 23], [204], [], [50, 232]]]
 h' := ![![[25, 232], [232, 28], [0, 28], [144, 162], [184, 207], [0, 196], [219], [0, 1]], ![[0, 1], [0, 205], [1, 205], [0, 71], [0, 26], [7, 37], [219], [25, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191]]
 b := ![[], [146, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [159, 208, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7198, 4459, 627]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-596, -328, 627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1017695, 248258, -33560]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-1017695, 248258, -33560]] 
 ![![233, 0, 0], ![103, 1, 0], ![109, 0, 1]] where
  M :=![![![-1017695, 248258, -33560], ![6510640, -1588215, 214698], ![-41651412, 10160506, -1373517]]]
  hmulB := by decide  
  f := ![![![15033, -2026, -684]], ![![7215, -881, -314]], ![![9289, -576, -317]]]
  g := ![![![-98413, 248258, -33560], ![629591, -1588215, 214698], ![-4027769, 10160506, -1373517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-15033, 2026, 684]] ![![-1017695, 248258, -33560]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-107, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-107, 1, 0]] 
 ![![239, 0, 0], ![132, 1, 0], ![23, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-107, 1, 0], ![0, -107, 1], ![-194, 17, -106]]]
  hmulB := by decide  
  f := ![![![22257, -208, 0], ![49712, 0, 0]], ![![12306, -115, 0], ![27486, 0, 0]], ![![2295, -21, 0], ![5126, 1, 0]]]
  g := ![![![1, 0, 0], ![-132, 239, 0], ![-23, 0, 239]], ![![-1, 1, 0], ![59, -107, 1], ![0, 17, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-89, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-89, 1, 0]] 
 ![![239, 0, 0], ![150, 1, 0], ![205, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-89, 1, 0], ![0, -89, 1], ![-194, 17, -88]]]
  hmulB := by decide  
  f := ![![![11749, -132, 0], ![31548, 0, 0]], ![![7388, -83, 0], ![19838, 0, 0]], ![![10091, -113, 0], ![27096, 1, 0]]]
  g := ![![![1, 0, 0], ![-150, 239, 0], ![-205, 0, 239]], ![![-1, 1, 0], ![55, -89, 1], ![64, 17, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-44, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-44, 1, 0]] 
 ![![239, 0, 0], ![195, 1, 0], ![215, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-44, 1, 0], ![0, -44, 1], ![-194, 17, -43]]]
  hmulB := by decide  
  f := ![![![9373, -213, 0], ![50907, 0, 0]], ![![7657, -174, 0], ![41587, 0, 0]], ![![8413, -191, 0], ![45693, 1, 0]]]
  g := ![![![1, 0, 0], ![-195, 239, 0], ![-215, 0, 239]], ![![-1, 1, 0], ![35, -44, 1], ![24, 17, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-107, 1, 0]] ![![239, 0, 0], ![-89, 1, 0]]
  ![![239, 0, 0], ![-37, 43, 1]] where
 M := ![![![57121, 0, 0], ![-21271, 239, 0]], ![![-25573, 239, 0], ![9523, -196, 1]]]
 hmul := by decide  
 g := ![![![![239, 0, 0], ![0, 0, 0]], ![![-52, -42, -1], ![239, 0, 0]]], ![![![-70, -42, -1], ![239, 0, 0]], ![![40, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-37, 43, 1]] ![![239, 0, 0], ![-44, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-10516, 239, 0]], ![![-8843, 10277, 239], ![1434, -1912, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-44, 1, 0]]], ![![![-37, 43, 1]], ![![6, -8, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [212, 101, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 163, 181], [28, 77, 60], [0, 1]]
 g := ![![[56, 66, 79], [32, 77], [199, 164], [171, 141], [122, 32, 164], [101, 104, 20], [1]], ![[66, 186, 11, 182], [235, 87], [232, 67], [0, 134], [236, 138, 155, 123], [134, 173, 132, 201], [15, 110, 207, 177]], ![[168, 17, 73, 240], [151, 232], [163, 40], [102, 9], [47, 53, 3, 90], [204, 157, 178, 239], [83, 187, 79, 64]]]
 h' := ![![[178, 163, 181], [234, 51, 101], [149, 196, 42], [43, 77, 37], [164, 97, 158], [37, 163, 204], [29, 140, 206], [0, 1]], ![[28, 77, 60], [147, 161, 138], [70, 27, 150], [50, 32, 157], [110, 195, 80], [93, 46, 144], [64, 56, 232], [178, 163, 181]], ![[0, 1], [157, 29, 2], [184, 18, 49], [6, 132, 47], [120, 190, 3], [46, 32, 134], [18, 45, 44], [28, 77, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 177], []]
 b := ![[], [91, 114, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [212, 101, 35, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31089, 3615, -1205]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, 15, -5]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![62, -77, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![62, -77, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![62, 174, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![62, -77, 1], ![-194, 79, -76], ![14744, -1486, 3]]]
  hmulB := by decide  
  f := ![![![-61, 77, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -174, 251]], ![![0, -1, 1], ![18, 53, -76], ![58, -8, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [137, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 250], [0, 1]]
 g := ![![[206, 179], [228, 181], [173], [48, 152], [19, 205], [224, 197], [141, 1]], ![[94, 72], [147, 70], [173], [145, 99], [59, 46], [140, 54], [31, 250]]]
 h' := ![![[141, 250], [139, 207], [134, 92], [201, 115], [158, 34], [185, 177], [10, 166], [0, 1]], ![[0, 1], [210, 44], [54, 159], [101, 136], [183, 217], [42, 74], [73, 85], [141, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [149, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [137, 110, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1415, -530, 297]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79, -208, 297]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![76, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![76, 1, 0]] 
 ![![251, 0, 0], ![76, 1, 0], ![248, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![76, 1, 0], ![0, 76, 1], ![-194, 17, 77]]]
  hmulB := by decide  
  f := ![![![6157, 81, 0], ![-20331, 0, 0]], ![![1900, 25, 0], ![-6274, 0, 0]], ![![6104, 80, 0], ![-20156, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 251, 0], ![-248, 0, 251]], ![![0, 1, 0], ![-24, 76, 1], ![-82, 17, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![62, -77, 1]] ![![251, 0, 0], ![76, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![19076, 251, 0]], ![![15562, -19327, 251], ![4518, -5773, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![76, 1, 0]]], ![![![62, -77, 1]], ![![18, -23, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-13, 93, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-13, 93, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![244, 93, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-13, 93, 1], ![-194, 4, 94], ![-18236, 1404, 98]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-244, -93, 257]], ![![-1, 0, 1], ![-90, -34, 94], ![-164, -30, 98]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [195, 220, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 256], [0, 1]]
 g := ![![[212, 29], [227], [208], [44], [4], [196], [84], [1]], ![[0, 228], [227], [208], [44], [4], [196], [84], [1]]]
 h' := ![![[37, 256], [61, 172], [181, 22], [188, 145], [95, 72], [238, 2], [57, 243], [62, 37], [0, 1]], ![[0, 1], [0, 85], [224, 235], [156, 112], [189, 185], [55, 255], [53, 14], [146, 220], [37, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [117, 209]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [195, 220, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7623, -3628, 580]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-521, -224, 580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-94, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-94, 1, 0]] 
 ![![257, 0, 0], ![163, 1, 0], ![159, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-94, 1, 0], ![0, -94, 1], ![-194, 17, -93]]]
  hmulB := by decide  
  f := ![![![22561, -240, 0], ![61680, 0, 0]], ![![14383, -153, 0], ![39322, 0, 0]], ![![13947, -148, 0], ![38130, 1, 0]]]
  g := ![![![1, 0, 0], ![-163, 257, 0], ![-159, 0, 257]], ![![-1, 1, 0], ![59, -94, 1], ![46, 17, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-13, 93, 1]] ![![257, 0, 0], ![-94, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-24158, 257, 0]], ![![-3341, 23901, 257], ![1028, -8738, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-94, 1, 0]]], ![![![-13, 93, 1]], ![![4, -34, 0]]]]
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


lemma PB274I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB274I4 : PrimesBelowBoundCertificateInterval O 193 257 274 where
  m := 11
  g := ![3, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
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
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![239, 239, 239]
    · exact ![13997521]
    · exact ![63001, 251]
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
      exact NI197N2
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
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N0, I197N1, I197N2, I211N1, I233N1, I239N0, I239N1, I239N2, I251N1, I257N1]
  Il := ![[I197N0, I197N1, I197N2], [], [I211N1], [], [], [], [I233N1], [I239N0, I239N1, I239N2], [], [I251N1], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
