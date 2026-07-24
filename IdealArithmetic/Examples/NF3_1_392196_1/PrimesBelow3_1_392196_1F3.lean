
import IdealArithmetic.Examples.NF3_1_392196_1.RI3_1_392196_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-27, 28, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-27, 28, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![112, 28, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-27, 28, 1], ![136, -105, 170], ![2286, -610, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -28, 139]], ![![-1, 0, 1], ![-136, -35, 170], ![10, -6, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [67, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 138], [0, 1]]
 g := ![![[116, 83], [20, 91], [16], [110, 65], [83], [5], [1]], ![[0, 56], [0, 48], [16], [56, 74], [83], [5], [1]]]
 h' := ![![[12, 138], [50, 19], [49, 77], [136, 135], [116, 75], [123, 120], [72, 12], [0, 1]], ![[0, 1], [0, 120], [0, 62], [88, 4], [43, 64], [34, 19], [77, 127], [12, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [112, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [67, 127, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![355, 54, -564]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![457, 114, -564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-31, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-31, 1, 0]] 
 ![![139, 0, 0], ![108, 1, 0], ![131, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-31, 1, 0], ![2, -33, 6], ![80, -22, -29]]]
  hmulB := by decide  
  f := ![![![8939, -158708, 28860], ![-3058, -668590, 0]], ![![6948, -123304, 22422], ![-2362, -519443, 0]], ![![8433, -149574, 27199], ![-2844, -630110, 0]]]
  g := ![![![1, 0, 0], ![-108, 139, 0], ![-131, 0, 139]], ![![-1, 1, 0], ![20, -33, 6], ![45, -22, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-27, 28, 1]] ![![139, 0, 0], ![-31, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-4309, 139, 0]], ![![-3753, 3892, 139], ![973, -973, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-31, 1, 0]]], ![![![-27, 28, 1]], ![![7, -7, 1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [55, 26, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 147, 132], [45, 1, 17], [0, 1]]
 g := ![![[101, 145, 104], [140, 124], [126, 27, 7], [138, 37], [66, 25, 140], [3, 1], []], ![[82, 44, 16, 145], [146, 145], [58, 112, 11, 45], [127, 30], [111, 18, 10, 113], [91, 1], [41, 140]], ![[41, 16, 12, 80], [14, 140], [104, 24, 142, 68], [7, 129], [10, 132, 3, 45], [39, 4], [7, 140]]]
 h' := ![![[107, 147, 132], [13, 112, 113], [73, 52, 78], [94, 24, 56], [95, 145, 127], [133, 16, 132], [0, 0, 1], [0, 1]], ![[45, 1, 17], [22, 129, 146], [119, 50, 88], [49, 32, 95], [39, 83, 46], [60, 114, 9], [105, 44, 1], [107, 147, 132]], ![[0, 1], [100, 57, 39], [107, 47, 132], [38, 93, 147], [42, 70, 125], [91, 19, 8], [1, 105, 147], [45, 1, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 109], []]
 b := ![[], [122, 34, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [55, 26, 146, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![560389, -127246, -42167]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3761, -854, -283]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![42, -58, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![42, -58, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![42, 93, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![42, -58, 1], ![-36, 136, -346], ![-4594, 1282, -95]]]
  hmulB := by decide  
  f := ![![![-41, 58, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -93, 151]], ![![0, -1, 1], ![96, 214, -346], ![-4, 67, -95]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [138, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 150], [0, 1]]
 g := ![![[100, 58], [3, 86], [57, 97], [88], [9, 37], [8], [1]], ![[0, 93], [63, 65], [72, 54], [88], [91, 114], [8], [1]]]
 h' := ![![[92, 150], [39, 80], [137, 29], [35, 61], [117, 36], [122, 108], [13, 92], [0, 1]], ![[0, 1], [0, 71], [87, 122], [60, 90], [107, 115], [92, 43], [21, 59], [92, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [72, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [138, 59, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![748022, 114344, -352104]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102890, 217616, -352104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![44, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![44, 1, 0]] 
 ![![151, 0, 0], ![44, 1, 0], ![95, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![44, 1, 0], ![2, 42, 6], ![80, -22, 46]]]
  hmulB := by decide  
  f := ![![![22199, 527999, 75438], ![10117, -1898523, 0]], ![![6446, 153826, 21978], ![3021, -553113, 0]], ![![13975, 332185, 47461], ![6335, -1194435, 0]]]
  g := ![![![1, 0, 0], ![-44, 151, 0], ![-95, 0, 151]], ![![0, 1, 0], ![-16, 42, 6], ![-22, -22, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![42, -58, 1]] ![![151, 0, 0], ![44, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![6644, 151, 0]], ![![6342, -8758, 151], ![1812, -2416, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![44, 1, 0]]], ![![![42, -58, 1]], ![![12, -16, -2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [50, 126, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 56, 83], [84, 100, 74], [0, 1]]
 g := ![![[68, 23, 49], [87, 49], [59, 71, 52], [65, 109, 3], [2, 124, 118], [138, 1], []], ![[45, 51, 113, 7], [94, 138], [107, 121, 95, 6], [115, 66, 105, 142], [8, 81, 16, 22], [109, 109], [80, 138]], ![[35, 2, 1, 96], [10, 124], [119, 82, 7, 85], [87, 117, 38, 63], [80, 156, 122, 59], [17, 153], [89, 138]]]
 h' := ![![[54, 56, 83], [36, 113, 7], [33, 17, 150], [47, 128, 44], [57, 49, 85], [8, 146, 78], [0, 0, 1], [0, 1]], ![[84, 100, 74], [120, 140, 31], [61, 75, 83], [83, 143, 109], [53, 138, 7], [113, 140, 136], [15, 58, 100], [54, 56, 83]], ![[0, 1], [138, 61, 119], [18, 65, 81], [20, 43, 4], [74, 127, 65], [136, 28, 100], [94, 99, 56], [84, 100, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 89], []]
 b := ![[], [131, 64, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [50, 126, 19, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-851254, 364868, -145696]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5422, 2324, -928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [108, 121, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 132, 84], [20, 30, 79], [0, 1]]
 g := ![![[159, 131, 55], [76, 101, 95], [102, 49], [20, 156], [124, 47], [107, 126, 1], []], ![[126, 75, 89, 36], [76, 96, 116, 88], [44, 155], [95, 100], [7, 38], [146, 144, 65, 131], [62, 47]], ![[54, 63, 71, 44], [67, 52, 40, 70], [76, 26], [132, 135], [160, 146], [91, 58, 138, 124], [67, 47]]]
 h' := ![![[106, 132, 84], [105, 112, 113], [161, 87, 62], [16, 131, 156], [100, 119, 112], [17, 14, 84], [0, 0, 1], [0, 1]], ![[20, 30, 79], [137, 152, 84], [71, 66, 40], [52, 78, 36], [83, 14, 153], [137, 102, 110], [139, 84, 30], [106, 132, 84]], ![[0, 1], [52, 62, 129], [76, 10, 61], [121, 117, 134], [14, 30, 61], [159, 47, 132], [10, 79, 132], [20, 30, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 34], []]
 b := ![[], [160, 127, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [108, 121, 37, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27221, 8802, -20049]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![167, 54, -123]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [60, 144, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 30, 90], [78, 136, 77], [0, 1]]
 g := ![![[2, 24, 75], [79, 109, 2], [133, 163, 50], [78, 77], [93, 7], [117, 125, 1], []], ![[5, 34, 106, 129], [131, 96, 80, 111], [14, 86, 23, 146], [67, 42], [1, 49], [73, 157, 50, 151], [35, 84]], ![[114, 23, 1, 49], [53, 76, 47, 1], [154, 41, 82, 94], [43, 6], [20, 50], [166, 93, 117, 162], [48, 84]]]
 h' := ![![[47, 30, 90], [103, 80, 143], [36, 1, 13], [83, 160, 65], [134, 142, 54], [161, 34, 72], [0, 0, 1], [0, 1]], ![[78, 136, 77], [78, 121, 95], [164, 5, 21], [159, 166, 27], [2, 161, 84], [88, 8, 160], [109, 88, 136], [47, 30, 90]], ![[0, 1], [88, 133, 96], [16, 161, 133], [49, 8, 75], [25, 31, 29], [35, 125, 102], [31, 79, 30], [78, 136, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 57], []]
 b := ![[], [31, 99, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [60, 144, 42, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1805270, 83166, -480793]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10810, 498, -2879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![42, -36, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![42, -36, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![42, 137, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![42, -36, 1], ![8, 92, -214], ![-2834, 798, -51]]]
  hmulB := by decide  
  f := ![![![-41, 36, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -137, 173]], ![![0, -1, 1], ![52, 170, -214], ![-4, 45, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [35, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 172], [0, 1]]
 g := ![![[46, 89], [14], [150, 163], [138, 84], [52], [153, 41], [1]], ![[0, 84], [14], [161, 10], [11, 89], [52], [56, 132], [1]]]
 h' := ![![[120, 172], [169, 75], [113, 35], [14, 110], [147, 118], [8, 158], [138, 120], [0, 1]], ![[0, 1], [0, 98], [161, 138], [66, 63], [121, 55], [111, 15], [6, 53], [120, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [25, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [35, 53, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2085, 1194, -754]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, 604, -754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![41, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![41, 1, 0]] 
 ![![173, 0, 0], ![41, 1, 0], ![51, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![41, 1, 0], ![2, 39, 6], ![80, -22, 43]]]
  hmulB := by decide  
  f := ![![![-11140, -235615, -36252], ![-3979, 1045266, 0]], ![![-2657, -55804, -8586], ![-864, 247563, 0]], ![![-3294, -69459, -10687], ![-1131, 308142, 0]]]
  g := ![![![1, 0, 0], ![-41, 173, 0], ![-51, 0, 173]], ![![0, 1, 0], ![-11, 39, 6], ![-7, -22, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![42, -36, 1]] ![![173, 0, 0], ![41, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![7093, 173, 0]], ![![7266, -6228, 173], ![1730, -1384, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![41, 1, 0]]], ![![![42, -36, 1]], ![![10, -8, -1]]]]
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


lemma PB178I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 177 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 177 (by omega)

def PB178I3 : PrimesBelowBoundCertificateInterval O 137 177 178 where
  m := 7
  g := ![2, 1, 2, 1, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB178I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I139N1, I151N1, I173N1]
  Il := ![[I139N1], [], [I151N1], [], [], [], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
