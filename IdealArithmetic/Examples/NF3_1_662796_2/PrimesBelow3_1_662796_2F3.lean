
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![2, -32, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![2, -32, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![2, 107, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![2, -32, 1], ![501, 46, -97], ![-15346, -2301, 111]]]
  hmulB := by decide  
  f := ![![![-1, 32, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -107, 139]], ![![0, -1, 1], ![5, 75, -97], ![-112, -102, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [40, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 138], [0, 1]]
 g := ![![[1, 112], [138, 99], [100], [66, 4], [52], [71], [1]], ![[108, 27], [70, 40], [100], [45, 135], [52], [71], [1]]]
 h' := ![![[99, 138], [40, 23], [32, 51], [1, 10], [126, 2], [11, 82], [99, 99], [0, 1]], ![[0, 1], [93, 116], [77, 88], [18, 129], [46, 137], [67, 57], [31, 40], [99, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [27, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [40, 40, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2663, 2011, 567]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, -422, 567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-42, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-42, 1, 0]] 
 ![![139, 0, 0], ![97, 1, 0], ![28, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-42, 1, 0], ![-1, -41, 3], ![469, 76, -43]]]
  hmulB := by decide  
  f := ![![![-2967, -123411, 9030], ![139, -418390, 0]], ![![-2057, -86101, 6300], ![140, -291900, 0]], ![![-588, -24860, 1819], ![60, -84280, 0]]]
  g := ![![![1, 0, 0], ![-97, 139, 0], ![-28, 0, 139]], ![![-1, 1, 0], ![28, -41, 3], ![-41, 76, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![2, -32, 1]] ![![139, 0, 0], ![-42, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-5838, 139, 0]], ![![278, -4448, 139], ![417, 1390, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-42, 1, 0]]], ![![![2, -32, 1]], ![![3, 10, -1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-66, 63, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-66, 63, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![83, 63, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-66, 63, 1], ![406, 73, 188], ![29209, 4919, -52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -63, 149]], ![![-1, 0, 1], ![-102, -79, 188], ![225, 55, -52]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [133, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 148], [0, 1]]
 g := ![![[9, 121], [81], [18, 64], [123], [119, 20], [25], [1]], ![[0, 28], [81], [145, 85], [123], [19, 129], [25], [1]]]
 h' := ![![[144, 148], [55, 11], [139, 9], [77, 8], [116, 47], [60, 13], [16, 144], [0, 1]], ![[0, 1], [0, 138], [94, 140], [37, 141], [30, 102], [144, 136], [41, 5], [144, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [87, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [133, 5, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21505, 8384, 4920]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2885, -2024, 4920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-39, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-39, 1, 0]] 
 ![![149, 0, 0], ![110, 1, 0], ![52, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-39, 1, 0], ![-1, -38, 3], ![469, 76, -40]]]
  hmulB := by decide  
  f := ![![![-4664, -178753, 14112], ![149, -700896, 0]], ![![-3432, -131937, 10416], ![150, -517328, 0]], ![![-1612, -62384, 4925], ![112, -244608, 0]]]
  g := ![![![1, 0, 0], ![-110, 149, 0], ![-52, 0, 149]], ![![-1, 1, 0], ![27, -38, 3], ![-39, 76, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-66, 63, 1]] ![![149, 0, 0], ![-39, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-5811, 149, 0]], ![![-9834, 9387, 149], ![2980, -2384, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-39, 1, 0]]], ![![![-66, 63, 1]], ![![20, -16, 1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![32, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![32, 1, 0]] 
 ![![151, 0, 0], ![32, 1, 0], ![0, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![32, 1, 0], ![-1, 33, 3], ![469, 76, 31]]]
  hmulB := by decide  
  f := ![![![-31, -1, 0], ![151, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-29, -23, -2], ![140, 101, 0]]]
  g := ![![![1, 0, 0], ![-32, 151, 0], ![0, 0, 151]], ![![0, 1, 0], ![-7, 33, 3], ![-13, 76, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 6, 1]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![24, 6, 1]] 
 ![![151, 0, 0], ![127, 1, 0], ![17, 0, 1]] where
  M :=![![![24, 6, 1], ![463, 106, 17], ![2476, 587, 95]]]
  hmulB := by decide  
  f := ![![![91, 17, -4]], ![![64, 13, -3]], ![![72, 7, -2]]]
  g := ![![![-5, 6, 1], ![-88, 106, 17], ![-488, 587, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-8, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-8, 1, 0]] 
 ![![151, 0, 0], ![143, 1, 0], ![132, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-8, 1, 0], ![-1, -7, 3], ![469, 76, -9]]]
  hmulB := by decide  
  f := ![![![-3819, -26797, 11484], ![151, -578028, 0]], ![![-3616, -25376, 10875], ![152, -547375, 0]], ![![-3340, -23425, 10039], ![103, -505296, 0]]]
  g := ![![![1, 0, 0], ![-143, 151, 0], ![-132, 0, 151]], ![![-1, 1, 0], ![4, -7, 3], ![-61, 76, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![32, 1, 0]] ![![24, 6, 1]]
  ![![151, 0, 0], ![-55, 3, 1]] where
 M := ![![![3624, 906, 151]], ![![1231, 298, 49]]]
 hmul := by decide  
 g := ![![![![24, 6, 1], ![0, 0, 0]]], ![![![26, 1, 0], ![49, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-55, 3, 1]] ![![151, 0, 0], ![-8, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-1208, 151, 0]], ![![-8305, 453, 151], ![906, 0, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-8, 1, 0]]], ![![![-55, 3, 1]], ![![6, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [107, 2, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 23, 147], [138, 133, 10], [0, 1]]
 g := ![![[100, 44, 1], [31, 49], [129, 110, 81], [127, 139, 4], [147, 149, 113], [114, 1], []], ![[20, 85, 83, 130], [70, 12], [133, 53, 129, 11], [41, 105, 88, 4], [5, 49, 111, 147], [84, 105], [107, 100]], ![[28, 128, 125, 120], [92, 36], [13, 36, 77, 143], [115, 125, 15, 143], [4, 121, 124, 153], [49, 58], [87, 100]]]
 h' := ![![[133, 23, 147], [149, 122, 1], [13, 94, 150], [70, 1, 148], [128, 40, 155], [48, 136, 120], [0, 0, 1], [0, 1]], ![[138, 133, 10], [7, 51, 12], [78, 95, 13], [92, 12, 49], [33, 150, 119], [148, 30, 156], [117, 71, 133], [133, 23, 147]], ![[0, 1], [30, 141, 144], [104, 125, 151], [42, 144, 117], [151, 124, 40], [96, 148, 38], [1, 86, 23], [138, 133, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 70], []]
 b := ![[], [68, 115, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [107, 2, 43, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41468216890, -11282230223, -2086992679]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-264128770, -71861339, -13292947]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-112, 69, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-112, 69, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![51, 69, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-112, 69, 1], ![400, 33, 206], ![32023, 5375, -104]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -69, 163]], ![![-1, 0, 1], ![-62, -87, 206], ![229, 77, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [136, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 162], [0, 1]]
 g := ![![[143, 6], [66, 135], [100], [118], [22], [48, 156], [1]], ![[0, 157], [27, 28], [100], [118], [22], [79, 7], [1]]]
 h' := ![![[112, 162], [152, 150], [69, 61], [125, 153], [6, 66], [155, 48], [27, 112], [0, 1]], ![[0, 1], [0, 13], [55, 102], [146, 10], [63, 97], [152, 115], [20, 51], [112, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [35, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [136, 51, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13831, 9544, 4459]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1480, -1829, 4459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-43, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-43, 1, 0]] 
 ![![163, 0, 0], ![120, 1, 0], ![104, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-43, 1, 0], ![-1, -42, 3], ![469, 76, -44]]]
  hmulB := by decide  
  f := ![![![-8956, -378001, 27000], ![163, -1467000, 0]], ![![-6581, -278251, 19875], ![164, -1079875, 0]], ![![-5695, -241179, 17227], ![177, -936000, 0]]]
  g := ![![![1, 0, 0], ![-120, 163, 0], ![-104, 0, 163]], ![![-1, 1, 0], ![29, -42, 3], ![-25, 76, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-112, 69, 1]] ![![163, 0, 0], ![-43, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-7009, 163, 0]], ![![-18256, 11247, 163], ![5216, -2934, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-43, 1, 0]]], ![![![-112, 69, 1]], ![![32, -18, 1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [32, 110, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 102, 40], [20, 64, 127], [0, 1]]
 g := ![![[161, 13, 47], [68, 112, 132], [70, 124, 33], [163, 22], [159, 126], [78, 45, 1], []], ![[32, 1, 80, 74], [136, 85, 149, 140], [86, 131, 8, 105], [122, 63], [31, 66], [9, 62, 164, 13], [0, 97]], ![[101, 12, 51, 44], [4, 158, 59, 121], [139, 96, 102, 42], [140, 48], [156, 121], [96, 56, 57, 4], [80, 97]]]
 h' := ![![[25, 102, 40], [162, 43, 61], [98, 87, 74], [137, 29, 37], [3, 21, 32], [9, 0, 31], [0, 0, 1], [0, 1]], ![[20, 64, 127], [117, 57, 113], [93, 99, 33], [106, 157, 21], [154, 49, 49], [12, 86, 147], [124, 159, 64], [25, 102, 40]], ![[0, 1], [23, 67, 160], [147, 148, 60], [122, 148, 109], [107, 97, 86], [16, 81, 156], [11, 8, 102], [20, 64, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 152], []]
 b := ![[], [46, 26, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [32, 110, 122, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2567792, -603538, -87174]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15376, -3614, -522]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [111, 80, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 129, 171], [136, 43, 2], [0, 1]]
 g := ![![[16, 122, 133], [96, 21], [172, 152, 172], [141, 150, 14], [61, 1], [62, 90, 1], []], ![[154, 71, 121, 165], [8, 100], [84, 164, 0, 3], [100, 106, 32, 102], [133, 167], [142, 161, 154, 108], [17, 4]], ![[155, 38, 20, 131], [98, 152], [58, 124, 110, 66], [149, 20, 98, 27], [49, 139], [115, 36, 78, 66], [13, 4]]]
 h' := ![![[127, 129, 171], [108, 58, 47], [111, 149, 59], [92, 8, 80], [36, 90, 138], [38, 101, 172], [0, 0, 1], [0, 1]], ![[136, 43, 2], [72, 154, 2], [21, 69, 163], [52, 113, 137], [164, 21, 45], [7, 59, 101], [56, 168, 43], [127, 129, 171]], ![[0, 1], [20, 134, 124], [93, 128, 124], [104, 52, 129], [161, 62, 163], [8, 13, 73], [99, 5, 129], [136, 43, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 126], []]
 b := ![[], [100, 140, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [111, 80, 83, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54508667, 12789025, 2070464]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![315079, 73925, 11968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-132, -72, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-132, -72, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![47, 107, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-132, -72, 1], ![541, -128, -217], ![-34106, -5341, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -107, 179]], ![![-1, -1, 1], ![60, 129, -217], ![-195, -40, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [52, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 178], [0, 1]]
 g := ![![[51, 31], [170, 145], [65], [171], [0, 19], [106, 15], [1]], ![[0, 148], [122, 34], [65], [171], [90, 160], [64, 164], [1]]]
 h' := ![![[33, 178], [110, 116], [163, 161], [58, 94], [0, 23], [37, 52], [127, 33], [0, 1]], ![[0, 1], [0, 63], [106, 18], [117, 85], [43, 156], [142, 127], [142, 146], [33, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [36, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [52, 146, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8962, 1637, 651]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-221, -380, 651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![38, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![38, 1, 0]] 
 ![![179, 0, 0], ![38, 1, 0], ![162, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![38, 1, 0], ![-1, 39, 3], ![469, 76, 37]]]
  hmulB := by decide  
  f := ![![![-3073, 118403, 9108], ![179, -543444, 0]], ![![-682, 25115, 1932], ![180, -115276, 0]], ![![-2782, 107158, 8243], ![166, -491832, 0]]]
  g := ![![![1, 0, 0], ![-38, 179, 0], ![-162, 0, 179]], ![![0, 1, 0], ![-11, 39, 3], ![-47, 76, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-132, -72, 1]] ![![179, 0, 0], ![38, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![6802, 179, 0]], ![![-23628, -12888, 179], ![-4475, -2864, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![38, 1, 0]]], ![![![-132, -72, 1]], ![![-25, -16, -1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-65, -45, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-65, -45, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![116, 136, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-65, -45, 1], ![514, -34, -136], ![-21443, -3289, 57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-116, -136, 181]], ![![-1, -1, 1], ![90, 102, -136], ![-155, -61, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [23, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 180], [0, 1]]
 g := ![![[162, 114], [168], [178, 48], [34], [5, 161], [134, 14], [1]], ![[24, 67], [168], [158, 133], [34], [134, 20], [98, 167], [1]]]
 h' := ![![[75, 180], [173, 117], [69, 63], [135, 49], [66, 136], [176, 121], [158, 75], [0, 1]], ![[0, 1], [79, 64], [88, 118], [9, 132], [130, 45], [20, 60], [172, 106], [75, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [6, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [23, 106, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4522, 7767, 3375]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2138, -2493, 3375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-45, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-45, 1, 0]] 
 ![![181, 0, 0], ![136, 1, 0], ![124, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-45, 1, 0], ![-1, -44, 3], ![469, 76, -46]]]
  hmulB := by decide  
  f := ![![![345, 15136, -1032], ![0, 62264, 0]], ![![259, 11352, -774], ![1, 46698, 0]], ![![255, 10369, -707], ![75, 42656, 0]]]
  g := ![![![1, 0, 0], ![-136, 181, 0], ![-124, 0, 181]], ![![-1, 1, 0], ![31, -44, 3], ![-23, 76, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-65, -45, 1]] ![![181, 0, 0], ![-45, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-8145, 181, 0]], ![![-11765, -8145, 181], ![3439, 1991, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-45, 1, 0]]], ![![![-65, -45, 1]], ![![19, 11, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, 11, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![74, 11, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![74, 11, 1]] where
  M :=![![![74, 11, 1], ![458, 161, 32], ![4821, 967, 140]]]
  hmulB := by decide  
  f := ![![![-44, -3, 1]], ![![472, 29, -10]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-10, -1, 32], ![-29, -3, 140]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [24, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 190], [0, 1]]
 g := ![![[4, 8], [117, 43], [45, 90], [26, 52], [91, 9], [0, 48], [1]], ![[0, 183], [0, 148], [0, 101], [0, 139], [182, 182], [167, 143], [1]]]
 h' := ![![[95, 190], [57, 114], [66, 132], [140, 89], [108, 25], [0, 188], [167, 95], [0, 1]], ![[0, 1], [0, 77], [0, 59], [0, 102], [0, 166], [97, 3], [24, 96], [95, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [24, 96, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14999, 6620, 1470]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-491, -50, 1470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -3, 1]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-44, -3, 1]] 
 ![![191, 0, 0], ![159, 1, 0], ![51, 0, 1]] where
  M :=![![![-44, -3, 1], ![472, 29, -10], ![-1745, -97, 36]]]
  hmulB := by decide  
  f := ![![![74, 11, 1]], ![![64, 10, 1]], ![![45, 8, 1]]]
  g := ![![![2, -3, 1], ![-19, 29, -10], ![62, -97, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![74, 11, 1]] ![![-44, -3, 1]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-28, -96, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-28, -96, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![165, 97, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-28, -96, 1], ![565, -48, -289], ![-45362, -7165, 145]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-165, -97, 193]], ![![-1, -1, 1], ![250, 145, -289], ![-359, -110, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [20, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 192], [0, 1]]
 g := ![![[103, 109], [151], [101], [112], [8], [8], [63, 1]], ![[22, 84], [151], [101], [112], [8], [8], [126, 192]]]
 h' := ![![[63, 192], [124, 63], [40, 99], [55, 115], [65, 150], [15, 104], [91, 89], [0, 1]], ![[0, 1], [40, 130], [101, 94], [159, 78], [58, 43], [5, 89], [101, 104], [63, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [102, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [20, 130, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-66928, 368, 6140]
  a := ![-2, -6, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5596, -3084, 6140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![96, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![96, 1, 0]] 
 ![![193, 0, 0], ![96, 1, 0], ![48, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![96, 1, 0], ![-1, 97, 3], ![469, 76, 95]]]
  hmulB := by decide  
  f := ![![![12416, -1204255, -37245], ![0, 2396095, 0]], ![![6175, -598975, -18525], ![1, 1191775, 0]], ![![3072, -299504, -9263], ![32, 595920, 0]]]
  g := ![![![1, 0, 0], ![-96, 193, 0], ![-48, 0, 193]], ![![0, 1, 0], ![-49, 97, 3], ![-59, 76, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-28, -96, 1]] ![![193, 0, 0], ![96, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![18528, 193, 0]], ![![-5404, -18528, 193], ![-2123, -9264, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![96, 1, 0]]], ![![![-28, -96, 1]], ![![-11, -48, -1]]]]
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


lemma PB231I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB231I3 : PrimesBelowBoundCertificateInterval O 137 193 231 where
  m := 11
  g := ![2, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB231I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
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
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
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
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I163N1, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [], [I163N1], [], [], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
