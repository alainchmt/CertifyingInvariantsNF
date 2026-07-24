
import IdealArithmetic.Examples.NF3_1_730732_1.RI3_1_730732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![47, -42, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![47, -42, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![47, 97, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![47, -42, 1], ![-148, 11, -83], ![4381, 1441, -31]]]
  hmulB := by decide  
  f := ![![![-46, 42, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -97, 139]], ![![0, -1, 1], ![27, 58, -83], ![42, 32, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [13, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 138], [0, 1]]
 g := ![![[11, 107], [24, 6], [83], [117, 37], [71], [16], [1]], ![[0, 32], [0, 133], [83], [108, 102], [71], [16], [1]]]
 h' := ![![[135, 138], [105, 61], [97, 59], [8, 120], [42, 71], [100, 40], [126, 135], [0, 1]], ![[0, 1], [0, 78], [0, 80], [84, 19], [36, 68], [79, 99], [3, 4], [135, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [31, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [13, 4, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697, -430, -142]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 96, -142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-56, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-56, 1, 0]] 
 ![![139, 0, 0], ![83, 1, 0], ![31, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-56, 1, 0], ![1, -56, 2], ![-106, -36, -55]]]
  hmulB := by decide  
  f := ![![![-1237, 97543, -3484], ![1251, 242138, 0]], ![![-703, 58234, -2080], ![835, 144560, 0]], ![![-265, 21754, -777], ![306, 54002, 0]]]
  g := ![![![1, 0, 0], ![-83, 139, 0], ![-31, 0, 139]], ![![-1, 1, 0], ![33, -56, 2], ![33, -36, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![47, -42, 1]] ![![139, 0, 0], ![-56, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-7784, 139, 0]], ![![6533, -5838, 139], ![-2780, 2363, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-56, 1, 0]]], ![![![47, -42, 1]], ![![-20, 17, -1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [118, 117, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 134, 13], [57, 14, 136], [0, 1]]
 g := ![![[78, 49, 36], [129, 114], [30, 55, 119], [111, 30], [66, 47, 67], [91, 1], []], ![[78, 86, 31, 109], [37, 39], [75, 108, 92, 15], [126, 53], [74, 20, 65, 71], [109, 47], [89, 20]], ![[71, 12, 11, 50], [35, 88], [12, 72, 84, 146], [56, 103], [110, 56, 25, 12], [45, 76], [115, 20]]]
 h' := ![![[34, 134, 13], [80, 33, 143], [36, 12, 76], [124, 22, 87], [109, 93, 46], [139, 112, 118], [0, 0, 1], [0, 1]], ![[57, 14, 136], [62, 15, 47], [133, 65, 28], [118, 23, 14], [91, 59, 65], [143, 61, 128], [41, 64, 14], [34, 134, 13]], ![[0, 1], [115, 101, 108], [64, 72, 45], [133, 104, 48], [143, 146, 38], [15, 125, 52], [109, 85, 134], [57, 14, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 16], []]
 b := ![[], [92, 68, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [118, 117, 58, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![714604, 379056, 110111]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4796, 2544, 739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92, 5, -2]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-92, 5, -2]] 
 ![![151, 0, 0], ![0, 151, 0], ![46, 73, 1]] where
  M :=![![![-92, 5, -2], ![217, -20, 8], ![-388, -38, -15]]]
  hmulB := by decide  
  f := ![![![-4, -1, 0]], ![![-1, -4, -2]], ![![-1, -2, -1]]]
  g := ![![![0, 1, -2], ![-1, -4, 8], ![2, 7, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [127, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 150], [0, 1]]
 g := ![![[75, 44], [112, 110], [42, 138], [124], [56, 11], [144], [1]], ![[0, 107], [0, 41], [47, 13], [124], [75, 140], [144], [1]]]
 h' := ![![[139, 150], [121, 73], [102, 84], [30, 134], [136, 107], [106, 112], [24, 139], [0, 1]], ![[0, 1], [0, 78], [0, 67], [83, 17], [60, 44], [121, 39], [17, 12], [139, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [83, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [127, 12, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291711, -304642, -149158]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43507, 70092, -149158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![151, 0, 0], ![4, 1, 0], ![68, 0, 1]] where
  M :=![![![4, 1, 0], ![1, 4, 2], ![-106, -36, 5]]]
  hmulB := by decide  
  f := ![![![92, -5, 2]], ![![1, 0, 0]], ![![44, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 4, 2], ![-2, -36, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-92, 5, -2]] ![![4, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9173407394165982, -409316452563171, 224778031799570]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![9173407394165982, -409316452563171, 224778031799570]] 
 ![![157, 0, 0], ![0, 157, 0], ![74, 18, 1]] where
  M :=![![![9173407394165982, -409316452563171, 224778031799570], ![-24235787823317591, 1081398249381462, -593854873326772], ![27428303713926656, -1223847965495314, 672081796818291]]]
  hmulB := by decide  
  f := ![![![28032962, 10595833, -13104]], ![![11984857, 28504706, 21178562]], ![![7439100, 5838578, 2670987]]]
  g := ![![![-47516987000014, -28377840923283, 224778031799570], ![125538043330341, 74973159039894, -593854873326772], ![-142074835991254, -84849173937736, 672081796818291]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [54, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 156], [0, 1]]
 g := ![![[111, 11], [40], [128, 126], [114, 154], [75, 51], [156], [1]], ![[117, 146], [40], [54, 31], [41, 3], [60, 106], [156], [1]]]
 h' := ![![[129, 156], [54, 110], [153, 121], [124, 35], [32, 25], [144, 69], [103, 129], [0, 1]], ![[0, 1], [114, 47], [62, 36], [86, 122], [117, 132], [96, 88], [102, 28], [129, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [147, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [54, 28, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-712, -1391, -1028]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![480, 109, -1028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28032962, -10595833, 13104]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-28032962, -10595833, 13104]] 
 ![![157, 0, 0], ![120, 1, 0], ![101, 0, 1]] where
  M :=![![![-28032962, -10595833, 13104], ![-11984857, -28504706, -21178562], ![1122227914, 380519604, -39100539]]]
  hmulB := by decide  
  f := ![![![-9173407394165982, 409316452563171, -224778031799570]], ![![-6857153499850957, 305965452599994, -168022349953004]], ![![-6076066563851534, 271113437416405, -148883203876273]]]
  g := ![![![7911742, -10595833, 13104], ![35335125, -28504706, -21178562], ![-258541211, 380519604, -39100539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![9173407394165982, -409316452563171, 224778031799570]] ![![-28032962, -10595833, 13104]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [154, 54, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 51, 2], [146, 111, 161], [0, 1]]
 g := ![![[108, 100, 6], [125, 158, 60], [45, 35], [10, 55], [96, 152], [149, 140, 1], []], ![[114, 47, 112, 141], [14, 81, 3, 142], [141, 81], [82, 22], [79, 6], [150, 65, 107, 29], [112, 4]], ![[45, 28, 68, 143], [128, 54, 22, 35], [36, 132], [16, 4], [49, 10], [46, 111, 16, 14], [116, 4]]]
 h' := ![![[157, 51, 2], [147, 122, 13], [76, 63, 95], [46, 91, 19], [114, 135, 50], [37, 60, 106], [0, 0, 1], [0, 1]], ![[146, 111, 161], [110, 143, 57], [100, 16, 76], [102, 57, 9], [159, 55, 115], [153, 23, 150], [66, 59, 111], [157, 51, 2]], ![[0, 1], [80, 61, 93], [130, 84, 155], [28, 15, 135], [84, 136, 161], [135, 80, 70], [29, 104, 51], [146, 111, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 161], []]
 b := ![[], [75, 14, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [154, 54, 23, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-138550, -63244, -9454]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-850, -388, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![866985571908, -38684803091, 21243939365]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![866985571908, -38684803091, 21243939365]] 
 ![![167, 0, 0], ![0, 167, 0], ![46, 2, 1]] where
  M :=![![![866985571908, -38684803091, 21243939365], ![-2290542375781, 102203754768, -56125666817], ![2592269432731, -115666783639, 63518951677]]]
  hmulB := by decide  
  f := ![![![57119, -4884, -23419]], ![![2477530, 900203, -33187]], ![![58461, 20445, -1487]]]
  g := ![![![-660093646, -486063963, 21243939365], ![1743941903, 1284162206, -56125666817], ![-1973666733, -1453321479, 63518951677]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [32, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 166], [0, 1]]
 g := ![![[31, 47], [113, 100], [145, 27], [107], [62], [26, 100], [1]], ![[0, 120], [111, 67], [81, 140], [107], [62], [24, 67], [1]]]
 h' := ![![[10, 166], [58, 61], [36, 157], [89, 19], [29, 146], [3, 88], [135, 10], [0, 1]], ![[0, 1], [0, 106], [103, 10], [112, 148], [153, 21], [48, 79], [68, 157], [10, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [107, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [32, 157, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12012, -1684, 995]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346, -22, 995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57119, 4884, 23419]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-57119, 4884, 23419]] 
 ![![167, 0, 0], ![162, 1, 0], ![155, 0, 1]] where
  M :=![![![-57119, 4884, 23419], ![-2477530, -900203, 33187], ![-2180453, -1838573, -895319]]]
  hmulB := by decide  
  f := ![![![-866985571908, 38684803091, -21243939365]], ![![-827312097445, 36914576922, -20271811439]], ![![-820209778913, 36597672232, -20097781756]]]
  g := ![![![-26816, 4884, 23419], ![827613, -900203, 33187], ![2601454, -1838573, -895319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![866985571908, -38684803091, 21243939365]] ![![-57119, 4884, 23419]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![75, 58, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![75, 58, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![75, 58, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![75, 58, 1], ![-48, 39, 117], ![-6219, -2159, 97]]]
  hmulB := by decide  
  f := ![![![-74, -58, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -58, 173]], ![![0, 0, 1], ![-51, -39, 117], ![-78, -45, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [22, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 172], [0, 1]]
 g := ![![[48, 118], [136], [32, 109], [113, 54], [4], [150, 151], [1]], ![[0, 55], [136], [146, 64], [6, 119], [4], [27, 22], [1]]]
 h' := ![![[155, 172], [93, 34], [161, 84], [109, 52], [81, 153], [160, 171], [151, 155], [0, 1]], ![[0, 1], [0, 139], [33, 89], [38, 121], [95, 20], [23, 2], [129, 18], [155, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [148, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [22, 18, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1268, 51, -366]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![166, 123, -366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![56, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![56, 1, 0]] 
 ![![173, 0, 0], ![56, 1, 0], ![76, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![56, 1, 0], ![1, 56, 2], ![-106, -36, 57]]]
  hmulB := by decide  
  f := ![![![3229, 224658, 8024], ![2422, -694076, 0]], ![![1018, 72683, 2596], ![866, -224554, 0]], ![![1380, 98693, 3525], ![1183, -304912, 0]]]
  g := ![![![1, 0, 0], ![-56, 173, 0], ![-76, 0, 173]], ![![0, 1, 0], ![-19, 56, 2], ![-14, -36, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![75, 58, 1]] ![![173, 0, 0], ![56, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![9688, 173, 0]], ![![12975, 10034, 173], ![4152, 3287, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![56, 1, 0]]], ![![![75, 58, 1]], ![![24, 19, 1]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [152, 89, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 173, 48], [146, 5, 131], [0, 1]]
 g := ![![[77, 78, 4], [103, 10, 65], [71, 171], [124, 172], [146, 66, 64], [112, 77, 1], []], ![[56, 133, 104, 172], [143, 87, 63, 95], [161, 129], [65, 146], [157, 96, 107, 64], [178, 10, 113, 126], [159, 156]], ![[131, 167, 18, 123], [37, 152, 142, 165], [98, 81], [71, 31], [64, 145, 53, 24], [48, 20, 135, 62], [76, 156]]]
 h' := ![![[110, 173, 48], [96, 32, 2], [64, 18, 85], [142, 59, 156], [4, 68, 72], [160, 166, 8], [0, 0, 1], [0, 1]], ![[146, 5, 131], [65, 23, 114], [144, 169, 36], [123, 127, 32], [115, 172, 44], [99, 43, 132], [104, 18, 5], [110, 173, 48]], ![[0, 1], [131, 124, 63], [103, 171, 58], [58, 172, 170], [162, 118, 63], [120, 149, 39], [98, 161, 173], [146, 5, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 80], []]
 b := ![[], [4, 133, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [152, 89, 102, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![609674, 230910, 5370]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3406, 1290, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116620556386098, -5203596699113, 2857579305647]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![116620556386098, -5203596699113, 2857579305647]] 
 ![![181, 0, 0], ![0, 181, 0], ![147, 64, 1]] where
  M :=![![![116620556386098, -5203596699113, 2857579305647], ![-308107003097695, 13747701382806, -7549614092579], ![348693119405041, -15558649532869, 8544104683693]]]
  hmulB := by decide  
  f := ![![![-1827053, -912414, -195155]], ![![19774016, 5198527, -2019983]], ![![6118962, 1355159, -849064]]]
  g := ![![![-1676483986431, -1039163935141, 2857579305647], ![4429205903378, 2745430957502, -7549614092579], ![-5012653420430, -3107079277841, 8544104683693]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [171, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 180], [0, 1]]
 g := ![![[32, 138], [43], [104, 116], [147], [89, 55], [6, 135], [1]], ![[28, 43], [43], [119, 65], [147], [132, 126], [128, 46], [1]]]
 h' := ![![[139, 180], [12, 92], [135, 62], [66, 109], [166, 50], [60, 112], [10, 139], [0, 1]], ![[0, 1], [130, 89], [65, 119], [13, 72], [57, 131], [62, 69], [145, 42], [139, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [7, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [171, 42, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1789, -1775, -1060]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![851, 365, -1060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1827053, -912414, -195155]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-1827053, -912414, -195155]] 
 ![![181, 0, 0], ![52, 1, 0], ![6, 0, 1]] where
  M :=![![![-1827053, -912414, -195155], ![19774016, 5198527, -2019983], ![110571889, 46702909, 4286113]]]
  hmulB := by decide  
  f := ![![![116620556386098, -5203596699113, 2857579305647]], ![![31801999607621, -1419001806470, 779251435365]], ![![5792356120009, -258454307887, 141931384075]]]
  g := ![![![258505, -912414, -195155], ![-1317290, 5198527, -2019983], ![-12948597, 46702909, 4286113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![116620556386098, -5203596699113, 2857579305647]] ![![-1827053, -912414, -195155]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [178, 142, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 92, 34], [61, 98, 157], [0, 1]]
 g := ![![[21, 113, 117], [130, 168, 133], [23, 118, 43], [103, 154, 8], [175, 15, 67], [61, 143, 1], []], ![[15, 35, 35, 27], [97, 41, 145, 48], [80, 170, 16, 117], [48, 162, 90, 17], [24, 6, 72, 24], [149, 101, 115, 117], [46, 10]], ![[30, 26, 183, 181], [160, 19, 136, 126], [40, 58, 159, 42], [32, 83, 84, 38], [189, 24, 181, 29], [179, 162, 12, 61], [114, 10]]]
 h' := ![![[82, 92, 34], [162, 163, 58], [108, 182, 18], [2, 80, 59], [174, 61, 114], [29, 73, 81], [0, 0, 1], [0, 1]], ![[61, 98, 157], [50, 28, 148], [140, 46, 121], [24, 123, 98], [57, 133, 67], [121, 144, 106], [64, 91, 98], [82, 92, 34]], ![[0, 1], [167, 0, 176], [5, 154, 52], [147, 179, 34], [162, 188, 10], [186, 165, 4], [46, 100, 92], [61, 98, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 122], []]
 b := ![[], [121, 144, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [178, 142, 48, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1293070, -303308, 242188]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6770, -1588, 1268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7011235, 3082364, 378682]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![7011235, 3082364, 378682]] 
 ![![193, 0, 0], ![0, 193, 0], ![56, 82, 1]] where
  M :=![![![7011235, 3082364, 378682], ![-37057928, -6621317, 6543410], ![-353617006, -137851526, -3538953]]]
  hmulB := by decide  
  f := ![![![-4795085924377, 213956218880, -117495051738]], ![![12668431703108, -565264061809, 310417386022]], ![![3916836152134, -174768808380, 95975103179]]]
  g := ![![![-73549, -144920, 378682], ![-2090616, -2814409, 6543410], ![-805366, 789340, -3538953]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [57, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 192], [0, 1]]
 g := ![![[144, 138], [48], [72], [28], [42], [28], [91, 1]], ![[157, 55], [48], [72], [28], [42], [28], [182, 192]]]
 h' := ![![[91, 192], [92, 157], [133, 56], [143, 119], [52, 75], [138, 106], [24, 118], [0, 1]], ![[0, 1], [97, 36], [18, 137], [164, 74], [122, 118], [134, 87], [147, 75], [91, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [184, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [57, 102, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11113, -15025, -6178]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1735, 2547, -6178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4795085924377, -213956218880, 117495051738]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![4795085924377, -213956218880, 117495051738]] 
 ![![193, 0, 0], ![28, 1, 0], ![91, 0, 1]] where
  M :=![![![4795085924377, -213956218880, 117495051738], ![-12668431703108, 565264061809, -310417386022], ![14337210527882, -639724793718, 351307842929]]]
  hmulB := by decide  
  f := ![![![-7011235, -3082364, -378682]], ![![-825164, -412875, -88842]], ![![-1473603, -739086, -160213]]]
  g := ![![![486063963, -213956218880, 117495051738], ![-1284162206, 565264061809, -310417386022], ![1453321479, -639724793718, 351307842929]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![7011235, 3082364, 378682]] ![![4795085924377, -213956218880, 117495051738]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB242I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB242I3 : PrimesBelowBoundCertificateInterval O 137 193 242 where
  m := 11
  g := ![2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB242I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
    · exact ![I193N0, I193N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I157N1, I167N1, I173N1, I181N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N1], [], [I167N1], [I173N1], [], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
