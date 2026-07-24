
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![24, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![24, 1, 0]] 
 ![![197, 0, 0], ![24, 1, 0], ![146, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![24, 1, 0], ![2, 25, 4], ![149, -27, 23]]]
  hmulB := by decide  
  f := ![![![35377, 452366, 72384], ![6698, -3564912, 0]], ![![4288, 55095, 8816], ![986, -434188, 0]], ![![26218, 335256, 53645], ![4968, -2642016, 0]]]
  g := ![![![1, 0, 0], ![-24, 197, 0], ![-146, 0, 197]], ![![0, 1, 0], ![-6, 25, 4], ![-13, -27, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-522989, 161210, -61034]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-522989, 161210, -61034]] 
 ![![197, 0, 0], ![48, 1, 0], ![102, 0, 1]] where
  M :=![![![-522989, 161210, -61034], ![-8771646, 1286139, 705874], ![29391282, -7038166, 963719]]]
  hmulB := by decide  
  f := ![![![-6207534978025, -274206283654, -192292155266]], ![![-1660718896686, -73359160837, -51444448894]], ![![-3335551240404, -147341756882, -103326093093]]]
  g := ![![![-10333, 161210, -61034], ![-723378, 1286139, 705874], ![1365096, -7038166, 963719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-72, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-72, 1, 0]] 
 ![![197, 0, 0], ![125, 1, 0], ![3, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-72, 1, 0], ![2, -71, 4], ![149, -27, -73]]]
  hmulB := by decide  
  f := ![![![1453, -61766, 3480], ![-788, -171390, 0]], ![![961, -39190, 2208], ![-393, -108744, 0]], ![![51, -941, 53], ![67, -2610, 0]]]
  g := ![![![1, 0, 0], ![-125, 197, 0], ![-3, 0, 197]], ![![-1, 1, 0], ![45, -71, 4], ![19, -27, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![24, 1, 0]] ![![-522989, 161210, -61034]]
  ![![197, 0, 0], ![-7, -31, 1]] where
 M := ![![![-103028833, 31758370, -12023698]], ![![-21323382, 5155179, -758942]]]
 hmul := by decide  
 g := ![![![![-523234, 160125, -60999], ![-6895, 0, 0]]], ![![![-108244, 26153, -3852], ![-98, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-7, -31, 1]] ![![197, 0, 0], ![-72, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-14184, 197, 0]], ![![-1379, -6107, 197], ![591, 2167, -197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-72, 1, 0]]], ![![![-7, -31, 1]], ![![3, 11, -1]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [47, 5, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 173, 79], [124, 25, 120], [0, 1]]
 g := ![![[178, 114, 131], [172, 139, 58], [51, 89, 140], [70, 57], [53, 90], [173, 123], [1]], ![[164, 156, 171, 40], [45, 110, 123, 184], [174, 80, 10, 125], [49, 172], [20, 66], [112, 157], [21, 107, 79, 116]], ![[131, 5, 93, 69], [5, 136, 16, 150], [11, 173, 185, 95], [99, 79], [6, 182], [0, 161], [144, 40, 103, 83]]]
 h' := ![![[191, 173, 79], [75, 51, 176], [190, 190, 156], [38, 124, 109], [12, 7, 16], [48, 192, 17], [152, 194, 116], [0, 1]], ![[124, 25, 120], [4, 186, 71], [122, 145, 5], [183, 19, 183], [59, 64, 157], [2, 120, 71], [93, 23, 117], [191, 173, 79]], ![[0, 1], [80, 161, 151], [126, 63, 38], [127, 56, 106], [197, 128, 26], [9, 86, 111], [3, 181, 165], [124, 25, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 94], []]
 b := ![[], [123, 110, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [47, 5, 83, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1037984, 425860, -234820]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5216, 2140, -1180]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-43, 77, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-43, 77, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![168, 77, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-43, 77, 1], ![303, 7, 307], ![11385, -2035, -147]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-168, -77, 211]], ![![-1, 0, 1], ![-243, -112, 307], ![171, 44, -147]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [48, 164, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 210], [0, 1]]
 g := ![![[21, 208], [135, 34], [55], [25], [98, 37], [69], [47, 1]], ![[91, 3], [45, 177], [55], [25], [149, 174], [69], [94, 210]]]
 h' := ![![[47, 210], [61, 29], [198, 178], [112, 107], [149, 206], [69, 167], [65, 51], [0, 1]], ![[0, 1], [158, 182], [124, 33], [77, 104], [125, 5], [111, 44], [141, 160], [47, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [181, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [48, 164, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1820, 1100, 165]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, -55, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-96, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-96, 1, 0]] 
 ![![211, 0, 0], ![115, 1, 0], ![147, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-96, 1, 0], ![2, -95, 4], ![149, -27, -97]]]
  hmulB := by decide  
  f := ![![![7809, -493973, 20800], ![-5697, -1097200, 0]], ![![4229, -269215, 11336], ![-3164, -597974, 0]], ![![5409, -344142, 14491], ![-4038, -764400, 0]]]
  g := ![![![1, 0, 0], ![-115, 211, 0], ![-147, 0, 211]], ![![-1, 1, 0], ![49, -95, 4], ![83, -27, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-43, 77, 1]] ![![211, 0, 0], ![-96, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-20256, 211, 0]], ![![-9073, 16247, 211], ![4431, -7385, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-96, 1, 0]]], ![![![-43, 77, 1]], ![![21, -35, 1]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [59, 25, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 43, 157], [198, 179, 66], [0, 1]]
 g := ![![[10, 176, 148], [30, 142, 143], [132, 186, 32], [173, 174, 188], [167, 36, 65], [2, 17], [1]], ![[220, 213, 159, 137], [141, 77, 19, 40], [117, 174, 81, 167], [116, 95, 42, 51], [131, 49, 174, 6], [139, 127], [208, 178, 217, 174]], ![[64, 150, 22, 94], [104, 12, 172, 148], [136, 125, 163, 33], [136, 53, 2, 126], [183, 221, 24, 30], [165, 9], [217, 100, 95, 49]]]
 h' := ![![[79, 43, 157], [14, 81, 172], [17, 146, 139], [51, 24, 163], [182, 46, 100], [18, 113, 180], [164, 198, 54], [0, 1]], ![[198, 179, 66], [89, 145, 20], [20, 98, 81], [82, 122, 164], [160, 1, 146], [45, 7, 9], [202, 190, 166], [79, 43, 157]], ![[0, 1], [198, 220, 31], [189, 202, 3], [174, 77, 119], [57, 176, 200], [153, 103, 34], [116, 58, 3], [198, 179, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 138], []]
 b := ![[], [188, 54, 144], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [59, 25, 169, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36539754646, 11854387424, -5348616644]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-163855402, 53158688, -23984828]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [78, 226, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [192, 36, 64], [177, 190, 163], [0, 1]]
 g := ![![[15, 62, 100], [212, 204, 219], [61, 71], [59, 26], [114, 89], [137, 194, 188], [1]], ![[10, 33, 126, 169], [122, 54, 98, 97], [145, 75], [152, 40], [142, 176], [57, 183, 68, 214], [120, 2, 25, 186]], ![[84, 75, 124, 51], [62, 196, 104, 202], [226, 44], [164, 121], [15, 36], [209, 21, 179, 197], [10, 56, 172, 41]]]
 h' := ![![[192, 36, 64], [35, 94, 217], [178, 98, 30], [13, 66, 170], [23, 138, 88], [210, 169, 61], [149, 1, 142], [0, 1]], ![[177, 190, 163], [147, 166, 30], [162, 16, 168], [24, 105, 204], [168, 99, 128], [11, 199, 160], [202, 150, 31], [192, 36, 64]], ![[0, 1], [21, 194, 207], [61, 113, 29], [133, 56, 80], [101, 217, 11], [131, 86, 6], [205, 76, 54], [177, 190, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 16], []]
 b := ![[], [104, 96, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [78, 226, 85, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2650452, 846710, -331874]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11676, 3730, -1462]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![9, 72, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![9, 72, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![9, 72, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![9, 72, 1], ![293, 54, 287], ![10640, -1900, -90]]]
  hmulB := by decide  
  f := ![![![-8, -72, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -72, 229]], ![![0, 0, 1], ![-10, -90, 287], ![50, 20, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [100, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 228], [0, 1]]
 g := ![![[198, 71], [184], [40, 138], [46], [14], [156, 126], [123, 1]], ![[0, 158], [184], [68, 91], [46], [14], [82, 103], [17, 228]]]
 h' := ![![[123, 228], [148, 23], [122, 111], [212, 67], [71, 59], [201, 181], [66, 144], [0, 1]], ![[0, 1], [0, 206], [35, 118], [209, 162], [0, 170], [22, 48], [145, 85], [123, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [215, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [100, 106, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![207, 740, -1580]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63, 500, -1580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-58, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-58, 1, 0]] 
 ![![229, 0, 0], ![171, 1, 0], ![90, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-58, 1, 0], ![2, -57, 4], ![149, -27, -59]]]
  hmulB := by decide  
  f := ![![![-7045, 222287, -15600], ![2977, 893100, 0]], ![![-5243, 165974, -11648], ![2291, 666848, 0]], ![![-2786, 87362, -6131], ![1102, 351000, 0]]]
  g := ![![![1, 0, 0], ![-171, 229, 0], ![-90, 0, 229]], ![![-1, 1, 0], ![41, -57, 4], ![44, -27, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![9, 72, 1]] ![![229, 0, 0], ![-58, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-13282, 229, 0]], ![![2061, 16488, 229], ![-229, -4122, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-58, 1, 0]]], ![![![9, 72, 1]], ![![-1, -18, 1]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [115, 184, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 147, 161], [150, 85, 72], [0, 1]]
 g := ![![[190, 138, 123], [94, 144], [206, 224], [138, 74, 197], [84, 38], [189, 24, 29], [1]], ![[170, 74, 183, 215], [77, 58], [129, 207], [224, 156, 223, 184], [221, 16], [167, 175, 232, 31], [9, 93, 89, 18]], ![[126, 190, 65, 8], [99, 105], [95, 196], [15, 36, 217, 72], [186, 229], [212, 91, 6, 117], [92, 18, 203, 215]]]
 h' := ![![[52, 147, 161], [154, 30, 194], [53, 179, 221], [207, 112, 34], [55, 155, 165], [167, 154, 51], [118, 49, 202], [0, 1]], ![[150, 85, 72], [209, 13, 117], [26, 47, 72], [132, 92, 185], [108, 75, 69], [142, 177, 4], [6, 201, 128], [52, 147, 161]], ![[0, 1], [41, 190, 155], [230, 7, 173], [196, 29, 14], [75, 3, 232], [31, 135, 178], [133, 216, 136], [150, 85, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191, 184], []]
 b := ![[], [187, 68, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [115, 184, 31, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![315835461, -117307578, 68592870]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1355517, -503466, 294390]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![3, 63, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![3, 63, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![3, 63, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![3, 63, 1], ![275, 39, 251], ![9299, -1657, -87]]]
  hmulB := by decide  
  f := ![![![-2, -63, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -63, 239]], ![![0, 0, 1], ![-2, -66, 251], ![40, 16, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [232, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [192, 238], [0, 1]]
 g := ![![[164, 34], [222, 81], [197, 116], [233, 50], [211], [45, 162], [192, 1]], ![[0, 205], [0, 158], [3, 123], [34, 189], [211], [79, 77], [145, 238]]]
 h' := ![![[192, 238], [120, 89], [184, 9], [197, 112], [83, 17], [76, 188], [149, 65], [0, 1]], ![[0, 1], [0, 150], [0, 230], [191, 127], [1, 222], [83, 51], [201, 174], [192, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [219, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [232, 47, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-198, 144, -66]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, 18, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-12, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-12, 1, 0]] 
 ![![239, 0, 0], ![227, 1, 0], ![87, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-12, 1, 0], ![2, -11, 4], ![149, -27, -13]]]
  hmulB := by decide  
  f := ![![![14407, -79493, 28908], ![-956, -1727253, 0]], ![![13681, -75500, 27456], ![-955, -1640496, 0]], ![![5247, -28937, 10523], ![-296, -628749, 0]]]
  g := ![![![1, 0, 0], ![-227, 239, 0], ![-87, 0, 239]], ![![-1, 1, 0], ![9, -11, 4], ![31, -27, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![3, 63, 1]] ![![239, 0, 0], ![-12, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-2868, 239, 0]], ![![717, 15057, 239], ![239, -717, 239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-12, 1, 0]]], ![![![3, 63, 1]], ![![1, -3, 1]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-96, -12, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-96, -12, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![145, 229, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-96, -12, 1], ![125, -135, -49], ![-1876, 368, -111]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-145, -229, 241]], ![![-1, -1, 1], ![30, 46, -49], ![59, 107, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [121, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 240], [0, 1]]
 g := ![![[233, 2], [166], [100], [212], [161, 180], [176, 180], [4, 1]], ![[0, 239], [166], [100], [212], [158, 61], [173, 61], [8, 240]]]
 h' := ![![[4, 240], [153, 22], [85, 155], [48, 10], [40, 104], [153, 136], [239, 136], [0, 1]], ![[0, 1], [0, 219], [223, 86], [88, 231], [215, 137], [215, 105], [60, 105], [4, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [138, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [121, 237, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1489, 3530, -254]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159, 256, -254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![49, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![49, 1, 0]] 
 ![![241, 0, 0], ![49, 1, 0], ![111, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![49, 1, 0], ![2, 50, 4], ![149, -27, 48]]]
  hmulB := by decide  
  f := ![![![11278, 300285, 24024], ![3615, -1447446, 0]], ![![2295, 61047, 4884], ![724, -294261, 0]], ![![5168, 138305, 11065], ![1795, -666666, 0]]]
  g := ![![![1, 0, 0], ![-49, 241, 0], ![-111, 0, 241]], ![![0, 1, 0], ![-12, 50, 4], ![-16, -27, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-96, -12, 1]] ![![241, 0, 0], ![49, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![11809, 241, 0]], ![![-23136, -2892, 241], ![-4579, -723, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![49, 1, 0]]], ![![![-96, -12, 1]], ![![-19, -3, 0]]]]
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


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [24, 56, 224, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [194, 171, 134], [84, 79, 117], [0, 1]]
 g := ![![[222, 58, 227], [95, 64, 22], [233, 156], [0, 193, 49], [97, 157, 152], [173, 93, 227], [1]], ![[193, 84, 245, 129], [247, 125, 200, 193], [51, 174], [75, 133, 24, 162], [247, 62, 185, 247], [95, 222, 47, 162], [117, 58, 214, 18]], ![[61, 237, 140, 249], [101, 62, 248, 209], [233, 67], [111, 110, 143, 197], [100, 196, 65, 117], [204, 143, 7, 9], [44, 106, 134, 233]]]
 h' := ![![[194, 171, 134], [230, 52, 224], [181, 25, 140], [0, 129, 77], [182, 9, 244], [115, 202, 217], [227, 195, 27], [0, 1]], ![[84, 79, 117], [185, 135, 66], [47, 151, 103], [247, 12, 26], [119, 189, 151], [2, 88, 35], [249, 185, 151], [194, 171, 134]], ![[0, 1], [80, 64, 212], [22, 75, 8], [43, 110, 148], [185, 53, 107], [15, 212, 250], [41, 122, 73], [84, 79, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 148], []]
 b := ![[], [220, 106, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [24, 56, 224, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16185986, 6712995, -3706015]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64486, 26745, -14765]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![57, 126, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![57, 126, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![57, 126, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![57, 126, 1], ![401, 156, 503], ![18686, -3358, -96]]]
  hmulB := by decide  
  f := ![![![-56, -126, -1], ![257, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -126, 257]], ![![0, 0, 1], ![-110, -246, 503], ![94, 34, -96]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [2, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [192, 256], [0, 1]]
 g := ![![[161, 129], [21], [184], [49], [49], [242], [113], [1]], ![[0, 128], [21], [184], [49], [49], [242], [113], [1]]]
 h' := ![![[192, 256], [151, 30], [129, 110], [92, 236], [31, 250], [227, 7], [35, 111], [255, 192], [0, 1]], ![[0, 1], [0, 227], [175, 147], [172, 21], [229, 7], [29, 250], [16, 146], [111, 65], [192, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [134, 186]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [2, 65, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7508, -690, -1266]
  a := ![-2, -6, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![310, 618, -1266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![11, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![11, 1, 0]] 
 ![![257, 0, 0], ![11, 1, 0], ![96, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![11, 1, 0], ![2, 12, 4], ![149, -27, 10]]]
  hmulB := by decide  
  f := ![![![34684, 208683, 69564], ![2313, -4469487, 0]], ![![1477, 8927, 2976], ![258, -191208, 0]], ![![12949, 77951, 25985], ![1025, -1669536, 0]]]
  g := ![![![1, 0, 0], ![-11, 257, 0], ![-96, 0, 257]], ![![0, 1, 0], ![-2, 12, 4], ![-2, -27, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![57, 126, 1]] ![![257, 0, 0], ![11, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![2827, 257, 0]], ![![14649, 32382, 257], ![1028, 1542, 514]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![11, 1, 0]]], ![![![57, 126, 1]], ![![4, 6, 2]]]]
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


lemma PB268I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB268I4 : PrimesBelowBoundCertificateInterval O 193 257 268 where
  m := 11
  g := ![3, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB268I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
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
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![52441, 229]
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
      exact NI229N1
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
  β := ![I197N0, I197N1, I197N2, I211N1, I229N1, I239N1, I241N1, I257N1]
  Il := ![[I197N0, I197N1, I197N2], [], [I211N1], [], [], [I229N1], [], [I239N1], [I241N1], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
