
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-35, -33, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-35, -33, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![104, 106, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-35, -33, 1], ![258, 1, -198], ![-8514, -1145, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -106, 139]], ![![-1, -1, 1], ![150, 151, -198], ![-62, -9, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [62, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 138], [0, 1]]
 g := ![![[29, 54], [122, 116], [69], [44, 66], [66], [81], [1]], ![[98, 85], [54, 23], [69], [82, 73], [66], [81], [1]]]
 h' := ![![[9, 138], [81, 101], [94, 106], [52, 114], [125, 109], [73, 30], [77, 9], [0, 1]], ![[0, 1], [17, 38], [75, 33], [105, 25], [133, 30], [65, 109], [19, 130], [9, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [94, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [62, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![578, -15, -88]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 67, -88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![59, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![59, 1, 0]] 
 ![![139, 0, 0], ![59, 1, 0], ![138, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![59, 1, 0], ![0, 59, 6], ![258, 36, 59]]]
  hmulB := by decide  
  f := ![![![1594, 27, 0], ![-3753, 0, 0]], ![![590, 10, 0], ![-1389, 0, 0]], ![![1490, -24, -5], ![-3508, 116, 0]]]
  g := ![![![1, 0, 0], ![-59, 139, 0], ![-138, 0, 139]], ![![0, 1, 0], ![-31, 59, 6], ![-72, 36, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-35, -33, 1]] ![![139, 0, 0], ![59, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![8201, 139, 0]], ![![-4865, -4587, 139], ![-1807, -1946, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![59, 1, 0]]], ![![![-35, -33, 1]], ![![-13, -14, -1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [143, 115, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 23, 49], [55, 125, 100], [0, 1]]
 g := ![![[76, 87, 81], [138, 33], [19, 21, 67], [56, 9], [60, 85, 125], [64, 1], []], ![[110, 43, 15, 29], [38, 61], [83, 131, 119, 68], [60, 22], [105, 98, 53, 22], [28, 129], [64, 17]], ![[117, 63, 32, 46], [46, 124], [103, 144, 126, 143], [135, 45], [53, 127, 83, 142], [20, 82], [13, 17]]]
 h' := ![![[9, 23, 49], [116, 10, 140], [114, 91, 35], [8, 52, 118], [62, 112, 3], [86, 96, 107], [0, 0, 1], [0, 1]], ![[55, 125, 100], [44, 140, 110], [73, 59, 43], [67, 141, 14], [81, 73, 52], [45, 0, 50], [18, 10, 125], [9, 23, 49]], ![[0, 1], [6, 148, 48], [37, 148, 71], [98, 105, 17], [35, 113, 94], [51, 53, 141], [123, 139, 23], [55, 125, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 60], []]
 b := ![[], [0, 78, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [143, 115, 85, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-468158, 17582, 57216]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3142, 118, 384]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![21, 38, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![21, 38, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![21, 38, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![21, 38, 1], ![258, 57, 228], ![9804, 1411, 57]]]
  hmulB := by decide  
  f := ![![![-20, -38, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -38, 151]], ![![0, 0, 1], ![-30, -57, 228], ![57, -5, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [88, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 150], [0, 1]]
 g := ![![[78, 139], [23, 68], [92, 31], [76], [110, 98], [80], [1]], ![[0, 12], [12, 83], [67, 120], [76], [143, 53], [80], [1]]]
 h' := ![![[82, 150], [90, 21], [58, 81], [61, 22], [135, 128], [100, 131], [63, 82], [0, 1]], ![[0, 1], [0, 130], [56, 70], [53, 129], [61, 23], [121, 20], [143, 69], [82, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [43, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [88, 69, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-748, -88, 101]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -26, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![74, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![74, 1, 0]] 
 ![![151, 0, 0], ![74, 1, 0], ![94, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![74, 1, 0], ![0, 74, 6], ![258, 36, 74]]]
  hmulB := by decide  
  f := ![![![3405, 46, 0], ![-6946, 0, 0]], ![![1702, 23, 0], ![-3472, 0, 0]], ![![2054, -34, -5], ![-4190, 126, 0]]]
  g := ![![![1, 0, 0], ![-74, 151, 0], ![-94, 0, 151]], ![![0, 1, 0], ![-40, 74, 6], ![-62, 36, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![21, 38, 1]] ![![151, 0, 0], ![74, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![11174, 151, 0]], ![![3171, 5738, 151], ![1812, 2869, 302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![74, 1, 0]]], ![![![21, 38, 1]], ![![12, 19, 2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-77, -76, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-77, -76, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![80, 81, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-77, -76, 1], ![258, -41, -456], ![-19608, -2693, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -81, 157]], ![![-1, -1, 1], ![234, 235, -456], ![-104, 4, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [97, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 156], [0, 1]]
 g := ![![[36, 12], [130], [112, 143], [134, 143], [36, 17], [31], [1]], ![[51, 145], [130], [16, 14], [38, 14], [18, 140], [31], [1]]]
 h' := ![![[119, 156], [126, 144], [126, 75], [33, 65], [119, 92], [122, 71], [60, 119], [0, 1]], ![[0, 1], [149, 13], [102, 82], [75, 92], [77, 65], [93, 86], [91, 38], [119, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [52, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [97, 38, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1412, 211, 210]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116, -107, 210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-15, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-15, 1, 0]] 
 ![![157, 0, 0], ![142, 1, 0], ![41, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-15, 1, 0], ![0, -15, 6], ![258, 36, -15]]]
  hmulB := by decide  
  f := ![![![376, -25, 0], ![3925, 0, 0]], ![![346, -23, 0], ![3612, 0, 0]], ![![98, 6, -5], ![1023, 131, 0]]]
  g := ![![![1, 0, 0], ![-142, 157, 0], ![-41, 0, 157]], ![![-1, 1, 0], ![12, -15, 6], ![-27, 36, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-77, -76, 1]] ![![157, 0, 0], ![-15, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-2355, 157, 0]], ![![-12089, -11932, 157], ![1413, 1099, -471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-15, 1, 0]]], ![![![-77, -76, 1]], ![![9, 7, -3]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319, -62, -21]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-319, -62, -21]] 
 ![![163, 0, 0], ![0, 163, 0], ![54, 34, 1]] where
  M :=![![![-319, -62, -21], ![-5418, -1075, -372], ![-15996, -3135, -1075]]]
  hmulB := by decide  
  f := ![![![65, 5, -3]], ![![-774, -43, 30]], ![![-132, -7, 5]]]
  g := ![![![5, 4, -21], ![90, 71, -372], ![258, 205, -1075]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [48, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 162], [0, 1]]
 g := ![![[138, 34], [112, 150], [10], [115], [71], [40, 58], [1]], ![[25, 129], [160, 13], [10], [115], [71], [39, 105], [1]]]
 h' := ![![[59, 162], [3, 69], [160, 98], [71, 70], [7, 21], [36, 87], [115, 59], [0, 1]], ![[0, 1], [162, 94], [74, 65], [126, 93], [105, 142], [116, 76], [10, 104], [59, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [47, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [48, 104, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![564, 11, -62]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 13, -62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -5, 3]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-65, -5, 3]] 
 ![![163, 0, 0], ![122, 1, 0], ![73, 0, 1]] where
  M :=![![![-65, -5, 3], ![774, 43, -30], ![-1290, -51, 43]]]
  hmulB := by decide  
  f := ![![![319, 62, 21]], ![![272, 53, 18]], ![![241, 47, 16]]]
  g := ![![![2, -5, 3], ![-14, 43, -30], ![11, -51, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-319, -62, -21]] ![![-65, -5, 3]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-56, 38, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-56, 38, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![111, 38, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-56, 38, 1], ![258, -20, 228], ![9804, 1411, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -38, 167]], ![![-1, 0, 1], ![-150, -52, 228], ![72, 13, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [120, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 166], [0, 1]]
 g := ![![[155, 42], [120, 96], [10, 11], [126], [115], [42, 128], [1]], ![[14, 125], [84, 71], [152, 156], [126], [115], [161, 39], [1]]]
 h' := ![![[104, 166], [129, 84], [136, 116], [88, 41], [126, 31], [137, 68], [47, 104], [0, 1]], ![[0, 1], [14, 83], [9, 51], [10, 126], [10, 136], [28, 99], [8, 63], [104, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [87, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [120, 63, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9988, 2646, 2267]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1447, -500, 2267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-61, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-61, 1, 0]] 
 ![![167, 0, 0], ![106, 1, 0], ![20, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-61, 1, 0], ![0, -61, 6], ![258, 36, -61]]]
  hmulB := by decide  
  f := ![![![8480, -139, 0], ![23213, 0, 0]], ![![5430, -89, 0], ![14864, 0, 0]], ![![1112, -8, -1], ![3044, 28, 0]]]
  g := ![![![1, 0, 0], ![-106, 167, 0], ![-20, 0, 167]], ![![-1, 1, 0], ![38, -61, 6], ![-14, 36, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-56, 38, 1]] ![![167, 0, 0], ![-61, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-10187, 167, 0]], ![![-9352, 6346, 167], ![3674, -2338, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-61, 1, 0]]], ![![![-56, 38, 1]], ![![22, -14, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [120, 91, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 110, 161], [167, 62, 12], [0, 1]]
 g := ![![[126, 54, 38], [11, 67], [11, 92, 121], [59, 139, 47], [101, 73], [171, 98, 1], []], ![[143, 118, 92, 18], [24, 133], [54, 150, 67, 127], [0, 112, 171, 70], [81, 118], [99, 49, 79, 63], [54, 144]], ![[120, 33, 160, 30], [74, 149], [44, 47, 170, 11], [39, 130, 61, 53], [22, 113], [131, 169, 0, 53], [30, 144]]]
 h' := ![![[104, 110, 161], [8, 144, 111], [64, 65, 76], [13, 110, 11], [154, 53, 77], [67, 13, 108], [0, 0, 1], [0, 1]], ![[167, 62, 12], [116, 123, 137], [48, 120, 126], [156, 97, 54], [112, 5, 159], [12, 90, 139], [11, 167, 62], [104, 110, 161]], ![[0, 1], [56, 79, 98], [74, 161, 144], [112, 139, 108], [132, 115, 110], [2, 70, 99], [69, 6, 110], [167, 62, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 48], []]
 b := ![[], [122, 152, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [120, 91, 75, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2941, -5190, 1730]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, -30, 10]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [15, 19, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 16, 63], [15, 162, 116], [0, 1]]
 g := ![![[63, 168, 52], [146, 177, 75], [146, 4], [38, 76], [172, 140, 129], [132, 144, 1], []], ![[66, 72, 132, 30], [122, 167, 22, 109], [37, 65], [134, 5], [171, 157, 7, 140], [178, 76, 118, 128], [36, 31]], ![[161, 11, 53, 89], [73, 148, 32, 39], [27, 51], [21, 106], [40, 52, 21, 57], [123, 25, 72, 161], [162, 31]]]
 h' := ![![[129, 16, 63], [137, 28, 125], [96, 87, 84], [73, 161, 2], [105, 123, 75], [168, 165, 147], [0, 0, 1], [0, 1]], ![[15, 162, 116], [118, 145, 176], [2, 133, 115], [60, 121, 85], [82, 32, 30], [82, 34, 20], [170, 115, 162], [129, 16, 63]], ![[0, 1], [55, 6, 57], [14, 138, 159], [47, 76, 92], [2, 24, 74], [171, 159, 12], [122, 64, 16], [15, 162, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 142], []]
 b := ![[], [137, 10, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [15, 19, 35, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![237891, 53163, 20048]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1329, 297, 112]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [120, 14, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 63, 5], [99, 117, 176], [0, 1]]
 g := ![![[167, 177, 29], [140, 180], [130, 26, 25], [52, 55], [52, 122, 11], [42, 150, 1], []], ![[166, 121, 179, 64], [44, 119], [155, 123, 61, 138], [169, 48], [5, 34, 34, 165], [73, 146, 22, 27], [36, 25]], ![[18, 102, 112, 139], [47, 67], [118, 160, 111, 56], [3, 38], [167, 104, 132, 132], [155, 6, 174, 65], [46, 25]]]
 h' := ![![[51, 63, 5], [103, 156, 145], [147, 141, 19], [70, 62, 5], [95, 77, 69], [28, 55, 98], [0, 0, 1], [0, 1]], ![[99, 117, 176], [77, 23, 7], [17, 146, 32], [67, 54, 171], [165, 129, 132], [167, 40, 157], [91, 26, 117], [51, 63, 5]], ![[0, 1], [77, 2, 29], [58, 75, 130], [101, 65, 5], [113, 156, 161], [23, 86, 107], [118, 155, 63], [99, 117, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 133], []]
 b := ![[], [107, 178, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [120, 14, 31, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2955368, -240368, 136836]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16328, -1328, 756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -3, 2]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-49, -3, 2]] 
 ![![191, 0, 0], ![29, 1, 0], ![19, 0, 1]] where
  M :=![![![-49, -3, 2], ![516, 23, -18], ![-774, -22, 23]]]
  hmulB := by decide  
  f := ![![![133, 25, 8]], ![![31, 6, 2]], ![![47, 9, 3]]]
  g := ![![![0, -3, 2], ![1, 23, -18], ![-3, -22, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3089, -608, -209]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-3089, -608, -209]] 
 ![![191, 0, 0], ![35, 1, 0], ![146, 0, 1]] where
  M :=![![![-3089, -608, -209], ![-53922, -10613, -3648], ![-156864, -30875, -10613]]]
  hmulB := by decide  
  f := ![![![-3769, -171, 133]], ![![-511, -26, 19]], ![![-3112, -133, 107]]]
  g := ![![![255, -608, -209], ![4451, -10613, -3648], ![12949, -30875, -10613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 4, -1]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-19, 4, -1]] 
 ![![191, 0, 0], ![127, 1, 0], ![145, 0, 1]] where
  M :=![![![-19, 4, -1], ![-258, -55, 24], ![1032, 101, -55]]]
  hmulB := by decide  
  f := ![![![601, 119, 41]], ![![455, 90, 31]], ![![617, 122, 42]]]
  g := ![![![-2, 4, -1], ![17, -55, 24], ![-20, 101, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-49, -3, 2]] ![![-3089, -608, -209]]
  ![![-601, -119, -41]] where
 M := ![![![-601, -119, -41]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-601, -119, -41]] ![![-19, 4, -1]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, 1, 2]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-119, 1, 2]] 
 ![![193, 0, 0], ![25, 1, 0], ![121, 0, 1]] where
  M :=![![![-119, 1, 2], ![516, -47, 6], ![258, 122, -47]]]
  hmulB := by decide  
  f := ![![![1477, 291, 100]], ![![325, 64, 22]], ![![1315, 259, 89]]]
  g := ![![![-2, 1, 2], ![5, -47, 6], ![15, 122, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![511, 26, -19]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![511, 26, -19]] 
 ![![193, 0, 0], ![35, 1, 0], ![21, 0, 1]] where
  M :=![![![511, 26, -19], ![-4902, -173, 156], ![6708, 119, -173]]]
  hmulB := by decide  
  f := ![![![11365, 2237, 769]], ![![3089, 608, 209]], ![![4227, 832, 286]]]
  g := ![![![0, 26, -19], ![-11, -173, 156], ![32, 119, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![685159, 134856, 46355]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![685159, 134856, 46355]] 
 ![![193, 0, 0], ![133, 1, 0], ![172, 0, 1]] where
  M :=![![![685159, 134856, 46355], ![11959590, 2353939, 809136], ![34792848, 6848081, 2353939]]]
  hmulB := by decide  
  f := ![![![-52295, -3029, 2071]], ![![-33269, -1972, 1333]], ![![-50654, -2803, 1961]]]
  g := ![![![-130693, 134856, 46355], ![-2281273, 2353939, 809136], ![-6636681, 6848081, 2353939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-119, 1, 2]] ![![511, 26, -19]]
  ![![-52295, -3029, 2071]] where
 M := ![![![-52295, -3029, 2071]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-52295, -3029, 2071]] ![![685159, 134856, 46355]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB233I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB233I3 : PrimesBelowBoundCertificateInterval O 137 193 233 where
  m := 11
  g := ![2, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB233I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![191, 191, 191]
    · exact ![193, 193, 193]
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
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I151N1, I157N1, I163N1, I167N1, I191N0, I191N1, I191N2, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [], [I151N1], [I157N1], [I163N1], [I167N1], [], [], [], [I191N0, I191N1, I191N2], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
