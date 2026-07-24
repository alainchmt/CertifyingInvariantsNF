
import IdealArithmetic.Examples.NF3_1_780300_2.RI3_1_780300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-84, 67, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-84, 67, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![113, 67, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-84, 67, 1], ![170, -84, 134], ![11390, 85, -84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -67, 197]], ![![-1, 0, 1], ![-76, -46, 134], ![106, 29, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [20, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 196], [0, 1]]
 g := ![![[96, 55], [158], [47, 104], [161], [107], [60], [50, 1]], ![[88, 142], [158], [125, 93], [161], [107], [60], [100, 196]]]
 h' := ![![[50, 196], [47, 152], [45, 54], [104, 33], [127, 84], [10, 111], [182, 116], [0, 1]], ![[0, 1], [161, 45], [184, 143], [178, 164], [190, 113], [44, 86], [72, 81], [50, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [22, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [20, 147, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![360, -62, -145]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, 49, -145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![63, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![63, 1, 0]] 
 ![![197, 0, 0], ![63, 1, 0], ![84, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![63, 1, 0], ![0, 63, 2], ![170, 0, 63]]]
  hmulB := by decide  
  f := ![![![5293, 84, 0], ![-16548, 0, 0]], ![![1701, 27, 0], ![-5318, 0, 0]], ![![2184, 3, -1], ![-6828, 99, 0]]]
  g := ![![![1, 0, 0], ![-63, 197, 0], ![-84, 0, 197]], ![![0, 1, 0], ![-21, 63, 2], ![-26, 0, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-84, 67, 1]] ![![197, 0, 0], ![63, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![12411, 197, 0]], ![![-16548, 13199, 197], ![-5122, 4137, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![63, 1, 0]]], ![![![-84, 67, 1]], ![![-26, 21, 1]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [99, 78, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [197, 161, 17], [198, 37, 182], [0, 1]]
 g := ![![[195, 60, 94], [79, 54, 36], [171, 96, 25], [21, 100], [186, 5], [43, 9], [1]], ![[78, 41, 79, 156], [117, 60, 60, 152], [160, 166, 90, 135], [47, 57], [26, 161], [25, 145], [16, 105, 75, 137]], ![[193, 74, 180, 56], [160, 126, 20, 63], [131, 100, 159, 161], [126, 79], [22, 172], [129, 20], [160, 138, 53, 62]]]
 h' := ![![[197, 161, 17], [139, 31, 166], [185, 113, 6], [104, 37, 5], [81, 26, 10], [171, 55, 76], [100, 121, 196], [0, 1]], ![[198, 37, 182], [47, 90, 102], [73, 161, 153], [125, 18, 18], [20, 69, 16], [112, 13, 165], [0, 40, 155], [197, 161, 17]], ![[0, 1], [14, 78, 130], [71, 124, 40], [33, 144, 176], [186, 104, 173], [37, 131, 157], [79, 38, 47], [198, 37, 182]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 166], []]
 b := ![[], [196, 9, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [99, 78, 3, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![387453, 5970, -8955]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1947, 30, -45]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![52, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![52, 1, 0]] 
 ![![211, 0, 0], ![52, 1, 0], ![125, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![52, 1, 0], ![0, 52, 2], ![170, 0, 52]]]
  hmulB := by decide  
  f := ![![![2965, 57, 0], ![-12027, 0, 0]], ![![676, 13, 0], ![-2742, 0, 0]], ![![1723, 7, -1], ![-6989, 106, 0]]]
  g := ![![![1, 0, 0], ![-52, 211, 0], ![-125, 0, 211]], ![![0, 1, 0], ![-14, 52, 2], ![-30, 0, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![64, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![64, 1, 0]] 
 ![![211, 0, 0], ![64, 1, 0], ![62, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![64, 1, 0], ![0, 64, 2], ![170, 0, 64]]]
  hmulB := by decide  
  f := ![![![5249, 82, 0], ![-17302, 0, 0]], ![![1600, 25, 0], ![-5274, 0, 0]], ![![1546, -8, -1], ![-5096, 106, 0]]]
  g := ![![![1, 0, 0], ![-64, 211, 0], ![-62, 0, 211]], ![![0, 1, 0], ![-20, 64, 2], ![-18, 0, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![95, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![95, 1, 0]] 
 ![![211, 0, 0], ![95, 1, 0], ![24, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![95, 1, 0], ![0, 95, 2], ![170, 0, 95]]]
  hmulB := by decide  
  f := ![![![1711, 18, 0], ![-3798, 0, 0]], ![![665, 7, 0], ![-1476, 0, 0]], ![![164, -46, -1], ![-364, 106, 0]]]
  g := ![![![1, 0, 0], ![-95, 211, 0], ![-24, 0, 211]], ![![0, 1, 0], ![-43, 95, 2], ![-10, 0, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![52, 1, 0]] ![![211, 0, 0], ![64, 1, 0]]
  ![![211, 0, 0], ![-24, 58, 1]] where
 M := ![![![44521, 0, 0], ![13504, 211, 0]], ![![10972, 211, 0], ![3328, 116, 2]]]
 hmul := by decide  
 g := ![![![![211, 0, 0], ![0, 0, 0]], ![![64, 1, 0], ![0, 0, 0]]], ![![![52, 1, 0], ![0, 0, 0]], ![![16, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-24, 58, 1]] ![![211, 0, 0], ![95, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![20045, 211, 0]], ![![-5064, 12238, 211], ![-2110, 5486, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![95, 1, 0]]], ![![![-24, 58, 1]], ![![-10, 26, 1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [39, 87, 192, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 137, 106], [105, 85, 117], [0, 1]]
 g := ![![[162, 182, 56], [189, 54, 119], [194, 106, 109], [76, 196, 29], [74, 42, 78], [90, 69], [1]], ![[77, 214, 53, 135], [47, 106, 55, 132], [196, 97, 83, 130], [9, 41, 126, 47], [155, 54, 7, 38], [212, 128], [77, 200, 167, 196]], ![[203, 213, 119, 195], [4, 90, 194, 140], [90, 22, 165, 191], [97, 89, 45, 158], [211, 178, 88, 22], [218, 116], [49, 212, 21, 27]]]
 h' := ![![[149, 137, 106], [211, 216, 111], [16, 161, 157], [158, 185, 46], [13, 53, 67], [18, 56, 154], [184, 136, 31], [0, 1]], ![[105, 85, 117], [187, 59, 219], [183, 110, 83], [206, 150, 105], [35, 189, 163], [20, 84, 71], [86, 116, 103], [149, 137, 106]], ![[0, 1], [182, 171, 116], [174, 175, 206], [123, 111, 72], [174, 204, 216], [77, 83, 221], [128, 194, 89], [105, 85, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 187], []]
 b := ![[], [213, 12, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [39, 87, 192, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![504649, -12711, 12711]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2263, -57, 57]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-92, -33, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-92, -33, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![135, 194, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-92, -33, 1], ![170, -92, -66], ![-5610, 85, -92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-135, -194, 227]], ![![-1, -1, 1], ![40, 56, -66], ![30, 79, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [21, 208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 226], [0, 1]]
 g := ![![[118, 173], [137, 172], [188], [144], [30], [120, 57], [19, 1]], ![[0, 54], [0, 55], [188], [144], [30], [68, 170], [38, 226]]]
 h' := ![![[19, 226], [74, 20], [216, 132], [140, 85], [126, 12], [204, 22], [55, 113], [0, 1]], ![[0, 1], [0, 207], [0, 95], [166, 142], [127, 215], [168, 205], [159, 114], [19, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [14, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [21, 208, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-790, 975, -628]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![370, 541, -628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![66, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![66, 1, 0]] 
 ![![227, 0, 0], ![66, 1, 0], ![92, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![66, 1, 0], ![0, 66, 2], ![170, 0, 66]]]
  hmulB := by decide  
  f := ![![![4489, 68, 0], ![-15436, 0, 0]], ![![1254, 19, 0], ![-4312, 0, 0]], ![![1792, -6, -1], ![-6162, 114, 0]]]
  g := ![![![1, 0, 0], ![-66, 227, 0], ![-92, 0, 227]], ![![0, 1, 0], ![-20, 66, 2], ![-26, 0, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-92, -33, 1]] ![![227, 0, 0], ![66, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![14982, 227, 0]], ![![-20884, -7491, 227], ![-5902, -2270, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![66, 1, 0]]], ![![![-92, -33, 1]], ![![-26, -10, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [134, 177, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 146, 6], [208, 82, 223], [0, 1]]
 g := ![![[87, 188, 213], [175, 153], [112, 88, 11], [32, 17], [153, 173], [185], [1]], ![[113, 139, 136, 179], [124, 56], [209, 133, 93, 74], [208, 118], [43, 51], [198, 135, 78, 114], [50, 102, 196, 216]], ![[150, 200, 30, 191], [40, 16], [189, 31, 106, 66], [153, 138], [226, 202], [97, 30, 94, 115], [181, 120, 154, 13]]]
 h' := ![![[21, 146, 6], [152, 119, 199], [106, 144, 100], [58, 136, 34], [37, 202, 186], [171, 96, 33], [95, 52], [0, 1]], ![[208, 82, 223], [100, 113, 86], [107, 90, 133], [187, 61, 169], [218, 72, 205], [207, 50, 76], [42, 35, 83], [21, 146, 6]], ![[0, 1], [61, 226, 173], [200, 224, 225], [30, 32, 26], [193, 184, 67], [132, 83, 120], [148, 142, 146], [208, 82, 223]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 13], []]
 b := ![[], [124, 217, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [134, 177, 0, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14656, -687, -687]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -3, -3]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![76, -51, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![76, -51, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![76, 182, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![76, -51, 1], ![170, 76, -102], ![-8670, 85, 76]]]
  hmulB := by decide  
  f := ![![![-75, 51, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -182, 233]], ![![0, -1, 1], ![34, 80, -102], ![-62, -59, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [99, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 232], [0, 1]]
 g := ![![[], [], [81], [], [113], [0, 15], [0, 1]], ![[], [], [81], [], [113], [0, 218], [0, 232]]]
 h' := ![![[0, 232], [89], [136], [0, 9], [230], [0, 146], [0, 134], [0, 1]], ![[0, 1], [89], [136], [0, 224], [230], [0, 87], [0, 99], [0, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193]]
 b := ![[], [0, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [99, 0, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6560, 123, 724]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-208, -565, 724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![102, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![102, 1, 0]] 
 ![![233, 0, 0], ![102, 1, 0], ![157, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![102, 1, 0], ![0, 102, 2], ![170, 0, 102]]]
  hmulB := by decide  
  f := ![![![1429, 14, 0], ![-3262, 0, 0]], ![![510, 5, 0], ![-1164, 0, 0]], ![![941, -42, -1], ![-2148, 117, 0]]]
  g := ![![![1, 0, 0], ![-102, 233, 0], ![-157, 0, 233]], ![![0, 1, 0], ![-46, 102, 2], ![-68, 0, 102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![76, -51, 1]] ![![233, 0, 0], ![102, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![23766, 233, 0]], ![![17708, -11883, 233], ![7922, -5126, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![102, 1, 0]]], ![![![76, -51, 1]], ![![34, -22, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-26, -86, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-26, -86, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![213, 153, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-26, -86, 1], ![170, -26, -172], ![-14620, 85, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-213, -153, 239]], ![![-1, -1, 1], ![154, 110, -172], ![-38, 17, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [229, 229, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 238], [0, 1]]
 g := ![![[1, 17], [67, 40], [199, 127], [126, 150], [155], [78, 150], [10, 1]], ![[171, 222], [228, 199], [35, 112], [192, 89], [155], [144, 89], [20, 238]]]
 h' := ![![[10, 238], [192, 223], [78, 76], [65, 137], [22, 110], [63, 91], [100, 110], [0, 1]], ![[0, 1], [32, 16], [121, 163], [1, 102], [166, 129], [17, 148], [5, 129], [10, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [222, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [229, 229, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1019, 766, -209]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![182, 137, -209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-67, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-67, 1, 0]] 
 ![![239, 0, 0], ![172, 1, 0], ![26, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-67, 1, 0], ![0, -67, 2], ![170, 0, -67]]]
  hmulB := by decide  
  f := ![![![10989, -164, 0], ![39196, 0, 0]], ![![7974, -119, 0], ![28442, 0, 0]], ![![1316, 14, -1], ![4694, 120, 0]]]
  g := ![![![1, 0, 0], ![-172, 239, 0], ![-26, 0, 239]], ![![-1, 1, 0], ![48, -67, 2], ![8, 0, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-26, -86, 1]] ![![239, 0, 0], ![-67, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-16013, 239, 0]], ![![-6214, -20554, 239], ![1912, 5736, -239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-67, 1, 0]]], ![![![-26, -86, 1]], ![![8, 24, -1]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [222, 185, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 185, 71], [80, 55, 170], [0, 1]]
 g := ![![[148, 106, 187], [234, 48], [213, 29], [168, 24], [91, 2, 235], [3], [1]], ![[195, 90, 216, 234], [144, 36], [122, 239], [58, 1], [96, 100, 191, 22], [34, 56, 199, 78], [25, 147, 227, 26]], ![[102, 98, 187, 167], [18, 47], [108, 24], [121, 133], [235, 174, 18, 68], [93, 213, 222, 163], [218, 119, 74, 215]]]
 h' := ![![[161, 185, 71], [138, 27, 118], [130, 177, 17], [136, 194, 149], [42, 189, 54], [57, 47, 200], [19, 56], [0, 1]], ![[80, 55, 170], [126, 34, 213], [139, 12, 6], [183, 46, 38], [173, 29, 1], [146, 213, 118], [118, 238, 120], [161, 185, 71]], ![[0, 1], [111, 180, 151], [97, 52, 218], [148, 1, 54], [175, 23, 186], [196, 222, 164], [161, 188, 121], [80, 55, 170]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 20], []]
 b := ![[], [57, 87, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [222, 185, 0, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![116162, 1205, 2410]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![482, 5, 10]
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



lemma PB250I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 249 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 249 (by omega)

def PB250I4 : PrimesBelowBoundCertificateInterval O 193 249 250 where
  m := 9
  g := ![2, 1, 3, 1, 2, 1, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB250I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
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
    · exact ![211, 211, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
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
      exact NI211N2
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
  β := ![I197N1, I211N0, I211N1, I211N2, I227N1, I233N1, I239N1]
  Il := ![[I197N1], [], [I211N0, I211N1, I211N2], [], [I227N1], [], [I233N1], [I239N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
