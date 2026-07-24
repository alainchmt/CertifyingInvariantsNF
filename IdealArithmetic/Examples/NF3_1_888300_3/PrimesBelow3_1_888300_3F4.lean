
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-46, -33, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-46, -33, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![151, 164, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-46, -33, 1], ![730, 104, -33], ![-24090, -4220, 104]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-151, -164, 197]], ![![-1, -1, 1], ![29, 28, -33], ![-202, -108, 104]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [158, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 196], [0, 1]]
 g := ![![[80, 101], [191], [163, 171], [121], [178], [174], [165, 1]], ![[0, 96], [191], [10, 26], [121], [178], [174], [133, 196]]]
 h' := ![![[165, 196], [14, 62], [53, 114], [146, 163], [130, 186], [110, 93], [131, 78], [0, 1]], ![[0, 1], [0, 135], [148, 83], [52, 34], [88, 11], [89, 104], [196, 119], [165, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [16, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [158, 32, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1618, 998, 119]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83, -94, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![33, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![33, 1, 0]] 
 ![![197, 0, 0], ![33, 1, 0], ![93, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![33, 1, 0], ![0, 33, 1], ![730, 150, 33]]]
  hmulB := by decide  
  f := ![![![133, 4, 0], ![-788, 0, 0]], ![![-33, -1, 0], ![198, 0, 0]], ![![39, 1, 0], ![-230, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 197, 0], ![-93, 0, 197]], ![![0, 1, 0], ![-6, 33, 1], ![-37, 150, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-46, -33, 1]] ![![197, 0, 0], ![33, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![6501, 197, 0]], ![![-9062, -6501, 197], ![-788, -985, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![33, 1, 0]]], ![![![-46, -33, 1]], ![![-4, -5, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [178, 114, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 164, 137], [72, 34, 62], [0, 1]]
 g := ![![[153, 24, 145], [65, 126, 90], [9, 17, 103], [197, 47], [123, 165], [134, 52], [1]], ![[73, 102, 86, 97], [134, 182, 167, 77], [111, 45, 96, 181], [6, 43], [44, 91], [77, 35], [175, 30, 63, 74]], ![[178, 74, 194, 81], [84, 130, 166, 47], [151, 23, 157, 72], [78, 20], [117, 91], [122, 151], [51, 71, 146, 125]]]
 h' := ![![[29, 164, 137], [171, 112, 44], [189, 170, 182], [21, 110, 74], [62, 28, 68], [71, 132, 168], [21, 85, 101], [0, 1]], ![[72, 34, 62], [94, 167, 124], [4, 146, 26], [16, 120, 74], [41, 108, 178], [50, 58, 115], [5, 34, 154], [29, 164, 137]], ![[0, 1], [35, 119, 31], [39, 82, 190], [102, 168, 51], [97, 63, 152], [174, 9, 115], [0, 80, 143], [72, 34, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [186, 79], []]
 b := ![[], [121, 135, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [178, 114, 98, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7637421, 5176388, 701873]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38379, 26012, 3527]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-134, 4, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-134, 4, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![77, 4, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-134, 4, 1], ![730, 16, 4], ![2920, 1330, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -4, 211]], ![![-1, 0, 1], ![2, 0, 4], ![8, 6, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [146, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 210], [0, 1]]
 g := ![![[78, 64], [64, 96], [53], [82], [87, 209], [73], [6, 1]], ![[40, 147], [7, 115], [53], [82], [75, 2], [73], [12, 210]]]
 h' := ![![[6, 210], [151, 203], [139, 27], [131, 106], [169, 90], [72, 93], [179, 101], [0, 1]], ![[0, 1], [103, 8], [90, 184], [134, 105], [76, 121], [208, 118], [152, 110], [6, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [10, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [146, 205, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10338, 507, 74]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, 1, 74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-4, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-4, 1, 0]] 
 ![![211, 0, 0], ![207, 1, 0], ![195, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-4, 1, 0], ![0, -4, 1], ![730, 150, -4]]]
  hmulB := by decide  
  f := ![![![221, -55, 0], ![11605, 0, 0]], ![![217, -54, 0], ![11395, 0, 0]], ![![205, -51, 0], ![10765, 1, 0]]]
  g := ![![![1, 0, 0], ![-207, 211, 0], ![-195, 0, 211]], ![![-1, 1, 0], ![3, -4, 1], ![-140, 150, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-134, 4, 1]] ![![211, 0, 0], ![-4, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-844, 211, 0]], ![![-28274, 844, 211], ![1266, 0, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-4, 1, 0]]], ![![![-134, 4, 1]], ![![6, 0, 0]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [157, 179, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 76, 24], [105, 146, 199], [0, 1]]
 g := ![![[147, 178, 210], [184, 108, 120], [145, 98, 213], [85, 85, 9], [75, 134, 55], [104, 25], [1]], ![[148, 124, 83, 174], [110, 191, 195, 10], [88, 123, 51, 114], [34, 18, 191, 180], [167, 73, 141, 157], [195, 128], [25, 73, 214, 221]], ![[27, 144, 157, 63], [20, 96, 196, 41], [194, 19, 85, 188], [144, 94, 7, 135], [132, 14, 176, 115], [155, 15], [139, 61, 65, 2]]]
 h' := ![![[113, 76, 24], [102, 198, 136], [204, 24, 182], [35, 136, 92], [44, 96, 3], [70, 215, 72], [66, 44, 218], [0, 1]], ![[105, 146, 199], [5, 167, 78], [21, 199, 165], [143, 53, 194], [117, 181, 66], [138, 119, 62], [176, 187, 103], [113, 76, 24]], ![[0, 1], [82, 81, 9], [94, 0, 99], [54, 34, 160], [53, 169, 154], [150, 112, 89], [63, 215, 125], [105, 146, 199]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 125], []]
 b := ![[], [150, 57, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [157, 179, 5, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11465768, -5266368, -578908]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51416, -23616, -2596]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-103, -71, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-103, -71, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![124, 156, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-103, -71, 1], ![730, 47, -71], ![-51830, -9920, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -156, 227]], ![![-1, -1, 1], ![42, 49, -71], ![-254, -76, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [15, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 226], [0, 1]]
 g := ![![[67, 225], [25, 139], [75], [73], [3], [217, 78], [130, 1]], ![[34, 2], [162, 88], [75], [73], [3], [142, 149], [33, 226]]]
 h' := ![![[130, 226], [79, 15], [165, 162], [137, 23], [209, 181], [150, 50], [93, 87], [0, 1]], ![[0, 1], [213, 212], [114, 65], [176, 204], [131, 46], [67, 177], [53, 140], [130, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [122, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [15, 97, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1475, 933, 54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -33, 54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![71, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![71, 1, 0]] 
 ![![227, 0, 0], ![71, 1, 0], ![180, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![71, 1, 0], ![0, 71, 1], ![730, 150, 71]]]
  hmulB := by decide  
  f := ![![![995, 14, 0], ![-3178, 0, 0]], ![![213, 3, 0], ![-680, 0, 0]], ![![804, 11, 0], ![-2568, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 227, 0], ![-180, 0, 227]], ![![0, 1, 0], ![-23, 71, 1], ![-100, 150, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-103, -71, 1]] ![![227, 0, 0], ![71, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![16117, 227, 0]], ![![-23381, -16117, 227], ![-6583, -4994, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![71, 1, 0]]], ![![![-103, -71, 1]], ![![-29, -22, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![14, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![14, 1, 0]] 
 ![![229, 0, 0], ![14, 1, 0], ![33, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![14, 1, 0], ![0, 14, 1], ![730, 150, 14]]]
  hmulB := by decide  
  f := ![![![2269, 162, 0], ![-37098, 0, 0]], ![![126, 9, 0], ![-2060, 0, 0]], ![![309, 22, 0], ![-5052, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 229, 0], ![-33, 0, 229]], ![![0, 1, 0], ![-1, 14, 1], ![-8, 150, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![64, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![64, 1, 0]] 
 ![![229, 0, 0], ![64, 1, 0], ![26, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![64, 1, 0], ![0, 64, 1], ![730, 150, 64]]]
  hmulB := by decide  
  f := ![![![3585, 56, 0], ![-12824, 0, 0]], ![![960, 15, 0], ![-3434, 0, 0]], ![![402, 6, 0], ![-1438, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 229, 0], ![-26, 0, 229]], ![![0, 1, 0], ![-18, 64, 1], ![-46, 150, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-309, -35, 4]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-309, -35, 4]] 
 ![![229, 0, 0], ![151, 1, 0], ![99, 0, 1]] where
  M :=![![![-309, -35, 4], ![2920, 291, -35], ![-25550, -2330, 291]]]
  hmulB := by decide  
  f := ![![![-3131, -865, -61]], ![![-2259, -624, -44]], ![![-4111, -1135, -80]]]
  g := ![![![20, -35, 4], ![-164, 291, -35], ![1299, -2330, 291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![14, 1, 0]] ![![229, 0, 0], ![64, 1, 0]]
  ![![-3131, -865, -61]] where
 M := ![![![52441, 0, 0], ![14656, 229, 0]], ![![3206, 229, 0], ![896, 78, 1]]]
 hmul := by decide  
 g := ![![![![-70761, -8015, 916]], ![![-16856, -1949, 221]]], ![![![-1406, -199, 21]], ![![-326, -48, 5]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-3131, -865, -61]] ![![-309, -35, 4]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [144, 39, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 189, 110], [67, 43, 123], [0, 1]]
 g := ![![[199, 156, 15], [88, 214], [214, 85], [171, 64, 178], [57, 226], [163, 156, 7], [1]], ![[89, 109, 194, 104], [99, 175], [38, 232], [108, 58, 132, 26], [76, 71], [156, 120, 42, 131], [170, 135, 72, 104]], ![[119, 72, 73, 16], [24, 23], [52, 175], [68, 46, 99, 157], [16, 217], [32, 172, 116, 231], [120, 149, 209, 129]]]
 h' := ![![[3, 189, 110], [130, 61, 134], [57, 70, 100], [74, 64, 28], [173, 102, 90], [61, 70, 172], [89, 194, 70], [0, 1]], ![[67, 43, 123], [90, 208, 123], [191, 198, 117], [49, 87, 89], [131, 0, 178], [103, 107, 184], [12, 3, 118], [3, 189, 110]], ![[0, 1], [52, 197, 209], [53, 198, 16], [28, 82, 116], [33, 131, 198], [163, 56, 110], [155, 36, 45], [67, 43, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 217], []]
 b := ![[], [197, 168, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [144, 39, 163, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16386657, 4395312, 311754]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70329, 18864, 1338]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-171, 74, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-171, 74, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![68, 74, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-171, 74, 1], ![730, -21, 74], ![54020, 11830, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -74, 239]], ![![-1, 0, 1], ![-18, -23, 74], ![232, 56, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [83, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [172, 238], [0, 1]]
 g := ![![[44, 72], [154, 64], [152, 110], [215, 135], [68], [143, 61], [172, 1]], ![[0, 167], [168, 175], [191, 129], [13, 104], [68], [119, 178], [105, 238]]]
 h' := ![![[172, 238], [124, 116], [51, 231], [80, 50], [200, 59], [81, 207], [64, 104], [0, 1]], ![[0, 1], [0, 123], [109, 8], [76, 189], [71, 180], [74, 32], [27, 135], [172, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [12, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [83, 67, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4363, 25, 94]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45, -29, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-74, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-74, 1, 0]] 
 ![![239, 0, 0], ![165, 1, 0], ![21, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-74, 1, 0], ![0, -74, 1], ![730, 150, -74]]]
  hmulB := by decide  
  f := ![![![4589, -62, 0], ![14818, 0, 0]], ![![3183, -43, 0], ![10278, 0, 0]], ![![467, -6, 0], ![1508, 1, 0]]]
  g := ![![![1, 0, 0], ![-165, 239, 0], ![-21, 0, 239]], ![![-1, 1, 0], ![51, -74, 1], ![-94, 150, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-171, 74, 1]] ![![239, 0, 0], ![-74, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-17686, 239, 0]], ![![-40869, 17686, 239], ![13384, -5497, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-74, 1, 0]]], ![![![-171, 74, 1]], ![![56, -23, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1961, 540, 38]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![1961, 540, 38]] 
 ![![241, 0, 0], ![0, 241, 0], ![96, 103, 1]] where
  M :=![![![1961, 540, 38], ![27740, 7661, 540], ![394200, 108740, 7661]]]
  hmulB := by decide  
  f := ![![![-119, -20, 2]], ![![1460, 181, -20]], ![![516, 63, -7]]]
  g := ![![![-7, -14, 38], ![-100, -199, 540], ![-1416, -2823, 7661]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [73, 236, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 240], [0, 1]]
 g := ![![[165, 41], [123], [119], [122], [123, 61], [47, 135], [5, 1]], ![[129, 200], [123], [119], [122], [187, 180], [240, 106], [10, 240]]]
 h' := ![![[5, 240], [38, 139], [231, 72], [240, 141], [179, 134], [184, 213], [117, 193], [0, 1]], ![[0, 1], [10, 102], [109, 169], [222, 100], [126, 107], [44, 28], [118, 48], [5, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [213, 204]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [73, 236, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2993, 3756, 1073]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-415, -443, 1073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -20, 2]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-119, -20, 2]] 
 ![![241, 0, 0], ![138, 1, 0], ![236, 0, 1]] where
  M :=![![![-119, -20, 2], ![1460, 181, -20], ![-14600, -1540, 181]]]
  hmulB := by decide  
  f := ![![![1961, 540, 38]], ![![1238, 341, 24]], ![![3556, 980, 69]]]
  g := ![![![9, -20, 2], ![-78, 181, -20], ![644, -1540, 181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![1961, 540, 38]] ![![-119, -20, 2]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [25, 230, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 250, 200], [101, 0, 51], [0, 1]]
 g := ![![[30, 243, 7], [146, 93, 60], [213, 243], [44, 73, 211], [161, 209, 108], [231, 234, 23], [1]], ![[99, 62, 186, 102], [47, 188, 152, 87], [151, 122], [236, 44, 73, 29], [125, 39, 174, 47], [90, 72, 171, 224], [83, 245, 238, 128]], ![[4, 100, 68, 214], [109, 109, 12, 110], [151, 31], [192, 216, 73, 21], [143, 29, 128, 36], [196, 91, 163, 41], [22, 104, 242, 123]]]
 h' := ![![[3, 250, 200], [115, 51, 42], [126, 218, 173], [155, 184, 69], [242, 168, 100], [249, 128, 205], [226, 21, 104], [0, 1]], ![[101, 0, 51], [111, 127, 160], [211, 61, 177], [216, 216, 154], [169, 208, 217], [40, 191, 249], [211, 109, 184], [3, 250, 200]], ![[0, 1], [121, 73, 49], [73, 223, 152], [121, 102, 28], [191, 126, 185], [238, 183, 48], [149, 121, 214], [101, 0, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 70], []]
 b := ![[], [108, 178, 213], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [25, 230, 147, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14073319, -1139540, 291160]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56069, -4540, 1160]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-161, -62, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-161, -62, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![96, 195, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-161, -62, 1], ![730, -11, -62], ![-45260, -8570, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -195, 257]], ![![-1, -1, 1], ![26, 47, -62], ![-172, -25, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [84, 239, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 256], [0, 1]]
 g := ![![[165, 205], [16], [241], [2], [11], [104], [67], [1]], ![[0, 52], [16], [241], [2], [11], [104], [67], [1]]]
 h' := ![![[18, 256], [63, 125], [76, 4], [187, 64], [163, 60], [148, 36], [143, 238], [173, 18], [0, 1]], ![[0, 1], [0, 132], [148, 253], [54, 193], [215, 197], [25, 221], [58, 19], [240, 239], [18, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [127, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [84, 239, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1900, 165, 416]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -315, 416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![62, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![62, 1, 0]] 
 ![![257, 0, 0], ![62, 1, 0], ![11, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![62, 1, 0], ![0, 62, 1], ![730, 150, 62]]]
  hmulB := by decide  
  f := ![![![8309, 134, 0], ![-34438, 0, 0]], ![![1922, 31, 0], ![-7966, 0, 0]], ![![263, 4, 0], ![-1090, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 257, 0], ![-11, 0, 257]], ![![0, 1, 0], ![-15, 62, 1], ![-36, 150, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-161, -62, 1]] ![![257, 0, 0], ![62, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![15934, 257, 0]], ![![-41377, -15934, 257], ![-9252, -3855, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![62, 1, 0]]], ![![![-161, -62, 1]], ![![-36, -15, 0]]]]
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


lemma PB267I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB267I4 : PrimesBelowBoundCertificateInterval O 193 257 267 where
  m := 11
  g := ![2, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB267I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0]
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
    · exact ![229, 229, 229]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![15813251]
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
      exact NI229N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N1, I211N1, I227N1, I229N0, I229N1, I229N2, I239N1, I241N1, I257N1]
  Il := ![[I197N1], [], [I211N1], [], [I227N1], [I229N0, I229N1, I229N2], [], [I239N1], [I241N1], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
