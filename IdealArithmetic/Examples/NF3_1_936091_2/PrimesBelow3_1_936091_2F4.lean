
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [120, 193, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 143, 82], [191, 53, 115], [0, 1]]
 g := ![![[99, 168, 55], [130, 47], [178, 182, 96], [53, 28], [181, 181], [187, 22], [1]], ![[77, 41, 21, 18], [87, 59], [142, 99, 73, 94], [96, 182], [43, 144], [133, 127], [161, 10, 68, 162]], ![[140, 149, 177, 11], [165, 25], [52, 62, 155, 123], [83, 81], [8, 163], [5, 161], [87, 111, 51, 35]]]
 h' := ![![[137, 143, 82], [124, 76, 152], [113, 152, 21], [195, 122, 80], [137, 22, 182], [37, 103, 56], [77, 4, 131], [0, 1]], ![[191, 53, 115], [56, 69, 104], [152, 128, 181], [102, 46, 60], [183, 6, 24], [157, 185, 185], [95, 152, 179], [137, 143, 82]], ![[0, 1], [130, 52, 138], [128, 114, 192], [152, 29, 57], [159, 169, 188], [118, 106, 153], [179, 41, 84], [191, 53, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 12], []]
 b := ![[], [31, 89, 144], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [120, 193, 66, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![334900, -47280, -193060]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1700, -240, -980]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![79, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![79, 1, 0]] 
 ![![199, 0, 0], ![79, 1, 0], ![73, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![79, 1, 0], ![-2, 81, 5], ![102, -33, 78]]]
  hmulB := by decide  
  f := ![![![18570, -806453, -49780], ![3383, 1981244, 0]], ![![7351, -320119, -19760], ![1394, 786448, 0]], ![![6774, -295835, -18261], ![1337, 726788, 0]]]
  g := ![![![1, 0, 0], ![-79, 199, 0], ![-73, 0, 199]], ![![0, 1, 0], ![-34, 81, 5], ![-15, -33, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-57, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-57, 1, 0]] 
 ![![199, 0, 0], ![142, 1, 0], ![89, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-57, 1, 0], ![-2, -55, 5], ![102, -33, -58]]]
  hmulB := by decide  
  f := ![![![27718, 792019, -72000], ![-3781, 2865600, 0]], ![![19753, 565139, -51375], ![-2785, 2044725, 0]], ![![12428, 354219, -32201], ![-1581, 1281600, 0]]]
  g := ![![![1, 0, 0], ![-142, 199, 0], ![-89, 0, 199]], ![![-1, 1, 0], ![37, -55, 5], ![50, -33, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-23, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-23, 1, 0]] 
 ![![199, 0, 0], ![176, 1, 0], ![102, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-23, 1, 0], ![-2, -21, 5], ![102, -33, -24]]]
  hmulB := by decide  
  f := ![![![10312, 108993, -25950], ![-597, 1032810, 0]], ![![9135, 96392, -22950], ![-397, 913410, 0]], ![![5303, 55865, -13301], ![-155, 529380, 0]]]
  g := ![![![1, 0, 0], ![-176, 199, 0], ![-102, 0, 199]], ![![-1, 1, 0], ![16, -21, 5], ![42, -33, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![79, 1, 0]] ![![199, 0, 0], ![-57, 1, 0]]
  ![![199, 0, 0], ![94, -35, 1]] where
 M := ![![![39601, 0, 0], ![-11343, 199, 0]], ![![15721, 199, 0], ![-4505, 24, 5]]]
 hmul := by decide  
 g := ![![![![105, 35, -1], ![199, 0, 0]], ![![-57, 1, 0], ![0, 0, 0]]], ![![![-15, 36, -1], ![199, 0, 0]], ![![-25, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![94, -35, 1]] ![![199, 0, 0], ![-23, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-4577, 199, 0]], ![![18706, -6965, 199], ![-1990, 796, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-23, 1, 0]]], ![![![94, -35, 1]], ![![-10, 4, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![58, 15, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![58, 15, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![58, 15, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![58, 15, 1], ![72, 55, 74], ![1482, -468, 11]]]
  hmulB := by decide  
  f := ![![![-57, -15, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -15, 211]], ![![0, 0, 1], ![-20, -5, 74], ![4, -3, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [69, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 210], [0, 1]]
 g := ![![[43, 52], [115, 199], [143], [44], [47, 43], [83], [198, 1]], ![[0, 159], [60, 12], [143], [44], [121, 168], [83], [185, 210]]]
 h' := ![![[198, 210], [83, 120], [24, 153], [94, 96], [133, 39], [36, 26], [53, 100], [0, 1]], ![[0, 1], [0, 91], [145, 58], [112, 115], [48, 172], [120, 185], [19, 111], [198, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [79, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [69, 13, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1995, 2318, -4600]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1255, 338, -4600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-74, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-74, 1, 0]] 
 ![![211, 0, 0], ![137, 1, 0], ![200, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-74, 1, 0], ![-2, -72, 5], ![102, -33, -75]]]
  hmulB := by decide  
  f := ![![![-3529, -135075, 9380], ![633, -395836, 0]], ![![-2287, -87698, 6090], ![423, -256998, 0]], ![![-3284, -128034, 8891], ![774, -375200, 0]]]
  g := ![![![1, 0, 0], ![-137, 211, 0], ![-200, 0, 211]], ![![-1, 1, 0], ![42, -72, 5], ![93, -33, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![58, 15, 1]] ![![211, 0, 0], ![-74, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-15614, 211, 0]], ![![12238, 3165, 211], ![-4220, -1055, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-74, 1, 0]]], ![![![58, 15, 1]], ![![-20, -5, 0]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [210, 111, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 1, 102], [170, 221, 121], [0, 1]]
 g := ![![[171, 38, 220], [65, 104, 7], [16, 108, 41], [51, 127, 28], [118, 184, 196], [27, 32], [1]], ![[84, 3, 195, 75], [103, 145, 220, 207], [84, 41, 9, 92], [166, 24, 46, 142], [35, 79, 106, 219], [39, 28], [98, 30, 33, 174]], ![[57, 188, 63, 115], [14, 214, 13, 136], [89, 156, 57, 124], [139, 180, 214, 162], [28, 122, 60, 29], [179, 56], [95, 167, 198, 49]]]
 h' := ![![[216, 1, 102], [176, 160, 79], [208, 110, 197], [217, 64, 34], [196, 122, 171], [74, 108, 14], [13, 112, 163], [0, 1]], ![[170, 221, 121], [108, 138, 106], [12, 137, 122], [202, 63, 216], [44, 176, 60], [21, 42, 61], [39, 140, 171], [216, 1, 102]], ![[0, 1], [164, 148, 38], [82, 199, 127], [190, 96, 196], [9, 148, 215], [130, 73, 148], [207, 194, 112], [170, 221, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 142], []]
 b := ![[], [133, 158, 191], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [210, 111, 60, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17151392502, -3017853648, -8477676824]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76912074, -13532976, -38016488]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![15, 1, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![15, 1, 0]] 
 ![![227, 0, 0], ![15, 1, 0], ![221, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![15, 1, 0], ![-2, 17, 5], ![102, -33, 14]]]
  hmulB := by decide  
  f := ![![![23897, -203630, -59890], ![908, 2719006, 0]], ![![1567, -13448, -3955], ![228, 179557, 0]], ![![23276, -198247, -58307], ![723, 2647138, 0]]]
  g := ![![![1, 0, 0], ![-15, 227, 0], ![-221, 0, 227]], ![![0, 1, 0], ![-6, 17, 5], ![-11, -33, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![98, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![98, 1, 0]] 
 ![![227, 0, 0], ![98, 1, 0], ![128, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![98, 1, 0], ![-2, 100, 5], ![102, -33, 97]]]
  hmulB := by decide  
  f := ![![![70249, -3806460, -190320], ![13620, 8640528, 0]], ![![30316, -1643226, -82160], ![5903, 3730064, 0]], ![![39604, -2146374, -107317], ![7698, 4872192, 0]]]
  g := ![![![1, 0, 0], ![-98, 227, 0], ![-128, 0, 227]], ![![0, 1, 0], ![-46, 100, 5], ![-40, -33, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![113, 1, 0]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![227, 0, 0], ![113, 1, 0]] 
 ![![227, 0, 0], ![113, 1, 0], ![170, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![113, 1, 0], ![-2, 115, 5], ![102, -33, 112]]]
  hmulB := by decide  
  f := ![![![73878, -4709321, -204750], ![16117, 9295650, 0]], ![![36700, -2344196, -101920], ![8173, 4627168, 0]], ![![55245, -3526805, -153337], ![12235, 6961500, 0]]]
  g := ![![![1, 0, 0], ![-113, 227, 0], ![-170, 0, 227]], ![![0, 1, 0], ![-61, 115, 5], ![-67, -33, 112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![15, 1, 0]] ![![227, 0, 0], ![98, 1, 0]]
  ![![227, 0, 0], ![112, 23, 1]] where
 M := ![![![51529, 0, 0], ![22246, 227, 0]], ![![3405, 227, 0], ![1468, 115, 5]]]
 hmul := by decide  
 g := ![![![![115, -23, -1], ![227, 0, 0]], ![![-14, -22, -1], ![227, 0, 0]]], ![![![-97, -22, -1], ![227, 0, 0]], ![![4, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![112, 23, 1]] ![![227, 0, 0], ![113, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![25651, 227, 0]], ![![25424, 5221, 227], ![12712, 2724, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![113, 1, 0]]], ![![![112, 23, 1]], ![![56, 12, 1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [63, 134, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 212, 57], [48, 16, 172], [0, 1]]
 g := ![![[10, 11, 16], [55, 81], [181, 142, 224], [192, 181], [190, 71], [106, 57, 33], [1]], ![[207, 175, 126, 64], [137, 218], [37, 208, 135, 57], [185, 181], [202, 9], [0, 18, 62, 225], [51, 87, 56, 161]], ![[47, 138, 198, 158], [92, 80], [198, 160, 109, 132], [67, 37], [160, 218], [138, 28, 206, 203], [223, 60, 44, 68]]]
 h' := ![![[57, 212, 57], [118, 180, 225], [47, 215, 220], [179, 74, 37], [162, 18, 69], [192, 143, 206], [166, 95, 105], [0, 1]], ![[48, 16, 172], [90, 129, 120], [146, 28, 203], [175, 216, 1], [36, 159, 69], [25, 162, 226], [154, 148, 225], [57, 212, 57]], ![[0, 1], [63, 149, 113], [135, 215, 35], [174, 168, 191], [161, 52, 91], [169, 153, 26], [134, 215, 128], [48, 16, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 188], []]
 b := ![[], [97, 92, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [63, 134, 124, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3053486, 1846656, -2464956]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13334, 8064, -10764]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14987, -5216, 532]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![14987, -5216, 532]] 
 ![![233, 0, 0], ![0, 233, 0], ![160, 41, 1]] where
  M :=![![![14987, -5216, 532], ![64696, -13001, -26612], ![-557568, 186492, 3179]]]
  hmulB := by decide  
  f := ![![![-21122725, -496976, -625428]], ![![-62799704, -1477553, -1859452]], ![![-25644184, -603357, -759305]]]
  g := ![![![-301, -116, 532], ![18552, 4627, -26612], ![-4576, 241, 3179]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [55, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 232], [0, 1]]
 g := ![![[64, 161], [133], [208], [134, 226], [117], [222, 98], [208, 1]], ![[0, 72], [133], [208], [76, 7], [117], [102, 135], [183, 232]]]
 h' := ![![[208, 232], [40, 188], [150, 42], [86, 212], [71, 172], [139, 74], [210, 104], [0, 1]], ![[0, 1], [0, 45], [32, 191], [145, 21], [198, 61], [153, 159], [173, 129], [208, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [115, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [55, 25, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1951, -384, -930]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![647, 162, -930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21122725, 496976, 625428]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![21122725, 496976, 625428]] 
 ![![233, 0, 0], ![29, 1, 0], ![146, 0, 1]] where
  M :=![![![21122725, 496976, 625428], ![62799704, 1477553, 1859452], ![20671008, 486348, 612053]]]
  hmulB := by decide  
  f := ![![![-14987, 5216, -532]], ![![-2143, 705, 48]], ![![-6998, 2468, -347]]]
  g := ![![![-363099, 496976, 625428], ![-1079525, 1477553, 1859452], ![-355334, 486348, 612053]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![14987, -5216, 532]] ![![21122725, 496976, 625428]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![13, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![13, 1, 0]] 
 ![![239, 0, 0], ![13, 1, 0], ![104, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![13, 1, 0], ![-2, 15, 5], ![102, -33, 12]]]
  hmulB := by decide  
  f := ![![![-42819, 321544, 107180], ![-956, -5123204, 0]], ![![-2330, 17475, 5825], ![1, -278435, 0]], ![![-18642, 139918, 46639], ![-242, -2229344, 0]]]
  g := ![![![1, 0, 0], ![-13, 239, 0], ![-104, 0, 239]], ![![0, 1, 0], ![-3, 15, 5], ![-3, -33, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![46, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![46, 1, 0]] 
 ![![239, 0, 0], ![46, 1, 0], ![36, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![46, 1, 0], ![-2, 48, 5], ![102, -33, 45]]]
  hmulB := by decide  
  f := ![![![-5049, 122305, 12740], ![-239, -608972, 0]], ![![-980, 23520, 2450], ![1, -117110, 0]], ![![-784, 18422, 1919], ![86, -91728, 0]]]
  g := ![![![1, 0, 0], ![-46, 239, 0], ![-36, 0, 239]], ![![0, 1, 0], ![-10, 48, 5], ![0, -33, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-60, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-60, 1, 0]] 
 ![![239, 0, 0], ![179, 1, 0], ![164, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-60, 1, 0], ![-2, -58, 5], ![102, -33, -61]]]
  hmulB := by decide  
  f := ![![![61061, 1826452, -157450], ![-7648, 7526110, 0]], ![![45729, 1367896, -117920], ![-5735, 5636576, 0]], ![![41936, 1253297, -108041], ![-5103, 5164360, 0]]]
  g := ![![![1, 0, 0], ![-179, 239, 0], ![-164, 0, 239]], ![![-1, 1, 0], ![40, -58, 5], ![67, -33, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![13, 1, 0]] ![![239, 0, 0], ![46, 1, 0]]
  ![![239, 0, 0], ![-72, 60, 1]] where
 M := ![![![57121, 0, 0], ![10994, 239, 0]], ![![3107, 239, 0], ![596, 61, 5]]]
 hmul := by decide  
 g := ![![![![239, 0, 0], ![0, 0, 0]], ![![46, 1, 0], ![0, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![4, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-72, 60, 1]] ![![239, 0, 0], ![-60, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-14340, 239, 0]], ![![-17208, 14340, 239], ![4302, -3585, 239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-60, 1, 0]]], ![![![-72, 60, 1]], ![![18, -15, 1]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [165, 79, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 36, 157], [42, 204, 84], [0, 1]]
 g := ![![[145, 173, 211], [195, 122], [102, 194], [228, 20], [96, 200, 182], [237, 90, 94], [1]], ![[24, 106, 175, 42], [178, 6], [211, 61], [50, 123], [239, 0, 162, 39], [18, 157, 13, 224], [23, 220, 118, 156]], ![[147, 111, 175, 52], [129, 134], [56, 24], [198, 164], [46, 51, 122, 22], [228, 134, 190, 31], [67, 101, 163, 85]]]
 h' := ![![[175, 36, 157], [111, 225, 115], [76, 45, 107], [235, 212, 26], [66, 17, 35], [178, 159, 172], [76, 162, 217], [0, 1]], ![[42, 204, 84], [73, 196, 222], [139, 119, 214], [3, 17, 28], [78, 103, 169], [125, 7, 42], [78, 218, 53], [175, 36, 157]], ![[0, 1], [162, 61, 145], [38, 77, 161], [222, 12, 187], [57, 121, 37], [108, 75, 27], [132, 102, 212], [42, 204, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 204], []]
 b := ![[], [212, 28, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [165, 79, 24, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6255155, 2542791, -794818]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25955, 10551, -3298]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![108, 68, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![108, 68, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![108, 68, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![108, 68, 1], ![-34, 211, 339], ![6888, -2217, 8]]]
  hmulB := by decide  
  f := ![![![-107, -68, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -68, 251]], ![![0, 0, 1], ![-146, -91, 339], ![24, -11, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [149, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 250], [0, 1]]
 g := ![![[78, 219], [222, 118], [221], [118, 156], [27, 232], [4, 232], [175, 1]], ![[0, 32], [39, 133], [221], [59, 95], [216, 19], [193, 19], [99, 250]]]
 h' := ![![[175, 250], [54, 113], [96, 108], [239, 216], [244, 77], [157, 105], [29, 105], [0, 1]], ![[0, 1], [0, 138], [171, 143], [138, 35], [165, 174], [209, 146], [81, 146], [175, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [56, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [149, 76, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1056, 1120, -2715]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1164, 740, -2715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-88, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-88, 1, 0]] 
 ![![251, 0, 0], ![163, 1, 0], ![243, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-88, 1, 0], ![-2, -86, 5], ![102, -33, -89]]]
  hmulB := by decide  
  f := ![![![-6951, -317861, 18480], ![1255, -927696, 0]], ![![-4447, -206404, 12000], ![1005, -602400, 0]], ![![-6727, -307730, 17891], ![1222, -898128, 0]]]
  g := ![![![1, 0, 0], ![-163, 251, 0], ![-243, 0, 251]], ![![-1, 1, 0], ![51, -86, 5], ![108, -33, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![108, 68, 1]] ![![251, 0, 0], ![-88, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-22088, 251, 0]], ![![27108, 17068, 251], ![-9538, -5773, 251]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-88, 1, 0]]], ![![![108, 68, 1]], ![![-38, -23, 1]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![49, 62, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![49, 62, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![49, 62, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![49, 62, 1], ![-22, 140, 309], ![6276, -2019, -45]]]
  hmulB := by decide  
  f := ![![![-48, -62, -1], ![257, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -62, 257]], ![![0, 0, 1], ![-59, -74, 309], ![33, 3, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [125, 206, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 256], [0, 1]]
 g := ![![[88, 123], [228], [16], [61], [114], [46], [31], [1]], ![[193, 134], [228], [16], [61], [114], [46], [31], [1]]]
 h' := ![![[51, 256], [116, 196], [54, 75], [189, 253], [19, 33], [205, 63], [185, 139], [132, 51], [0, 1]], ![[0, 1], [89, 61], [24, 182], [242, 4], [160, 224], [77, 194], [78, 118], [163, 206], [51, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [241, 177]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [125, 206, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4667, 440, -1195]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![246, 290, -1195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-52, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-52, 1, 0]] 
 ![![257, 0, 0], ![205, 1, 0], ![45, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-52, 1, 0], ![-2, -50, 5], ![102, -33, -53]]]
  hmulB := by decide  
  f := ![![![-26139, -667811, 66780], ![2827, -3432492, 0]], ![![-20837, -532659, 53265], ![2314, -2737821, 0]], ![![-4571, -116932, 11693], ![524, -601020, 0]]]
  g := ![![![1, 0, 0], ![-205, 257, 0], ![-45, 0, 257]], ![![-1, 1, 0], ![39, -50, 5], ![36, -33, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![49, 62, 1]] ![![257, 0, 0], ![-52, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-13364, 257, 0]], ![![12593, 15934, 257], ![-2570, -3084, 257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-52, 1, 0]]], ![![![49, 62, 1]], ![![-10, -12, 1]]]]
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
  g := ![1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1, I227N2]
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
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![227, 227, 227]
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
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
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
      exact NI227N2
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
  β := ![I199N0, I199N1, I199N2, I211N1, I227N0, I227N1, I227N2, I233N1, I239N0, I239N1, I239N2, I251N1, I257N1]
  Il := ![[], [I199N0, I199N1, I199N2], [I211N1], [], [I227N0, I227N1, I227N2], [], [I233N1], [I239N0, I239N1, I239N2], [], [I251N1], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
