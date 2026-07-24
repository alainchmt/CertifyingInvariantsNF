
import IdealArithmetic.Examples.NF3_3_895700_1.RI3_3_895700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-26, -37, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-26, -37, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![113, 102, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-26, -37, 1], ![-465, 60, -73], ![15665, -3353, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -102, 139]], ![![-1, -1, 1], ![56, 54, -73], ![94, -41, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [85, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 138], [0, 1]]
 g := ![![[60, 129], [83, 57], [127], [118, 112], [78], [42], [1]], ![[47, 10], [32, 82], [127], [69, 27], [78], [42], [1]]]
 h' := ![![[43, 138], [34, 44], [114, 14], [117, 108], [55, 23], [41, 56], [54, 43], [0, 1]], ![[0, 1], [119, 95], [21, 125], [35, 31], [71, 116], [86, 83], [96, 96], [43, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [116, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [85, 96, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2405, -434, 162]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-149, -122, 162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-66, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-66, 1, 0]] 
 ![![139, 0, 0], ![73, 1, 0], ![116, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-66, 1, 0], ![1, -66, 2], ![-428, 86, -65]]]
  hmulB := by decide  
  f := ![![![-2011, 211182, -6400], ![2502, 444800, 0]], ![![-1019, 110870, -3360], ![1391, 233520, 0]], ![![-1664, 176238, -5341], ![2118, 371200, 0]]]
  g := ![![![1, 0, 0], ![-73, 139, 0], ![-116, 0, 139]], ![![-1, 1, 0], ![33, -66, 2], ![6, 86, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-26, -37, 1]] ![![139, 0, 0], ![-66, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-9174, 139, 0]], ![![-3614, -5143, 139], ![1251, 2502, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-66, 1, 0]]], ![![![-26, -37, 1]], ![![9, 18, -1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [88, 58, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 123, 37], [125, 25, 112], [0, 1]]
 g := ![![[17, 4, 148], [5, 16], [4, 135, 25], [58, 42], [147, 74, 22], [119, 1], []], ![[73, 19, 51, 88], [2, 76], [78, 104, 22, 81], [121, 22], [147, 5, 53, 121], [147, 29], [67, 28]], ![[140, 47, 48, 143], [143, 63], [30, 14, 68, 80], [125, 121], [97, 129, 14, 95], [100, 80], [141, 28]]]
 h' := ![![[143, 123, 37], [92, 24, 105], [95, 42, 4], [95, 135, 144], [27, 136, 41], [107, 13, 97], [0, 0, 1], [0, 1]], ![[125, 25, 112], [18, 126, 86], [94, 86, 15], [126, 9, 102], [33, 120, 97], [44, 142, 75], [100, 71, 25], [143, 123, 37]], ![[0, 1], [114, 148, 107], [35, 21, 130], [140, 5, 52], [73, 42, 11], [136, 143, 126], [88, 78, 123], [125, 25, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 85], []]
 b := ![[], [50, 36, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [88, 58, 30, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12998164, -4998354, 1008432]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87236, -33546, 6768]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-21, 20, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-21, 20, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![130, 20, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-21, 20, 1], ![-408, 65, 41], ![-8731, 1549, 85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-130, -20, 151]], ![![-1, 0, 1], ![-38, -5, 41], ![-131, -1, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [114, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 150], [0, 1]]
 g := ![![[81, 40], [59, 68], [119, 25], [29], [16, 76], [76], [1]], ![[67, 111], [5, 83], [148, 126], [29], [80, 75], [76], [1]]]
 h' := ![![[128, 150], [69, 74], [24, 81], [9, 5], [139, 123], [104, 23], [37, 128], [0, 1]], ![[0, 1], [28, 77], [124, 70], [45, 146], [28, 28], [28, 128], [113, 23], [128, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [130, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [114, 23, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-685535, -756335, 381548]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-333025, -55545, 381548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-41, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-41, 1, 0]] 
 ![![151, 0, 0], ![110, 1, 0], ![66, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-41, 1, 0], ![1, -41, 2], ![-428, 86, -40]]]
  hmulB := by decide  
  f := ![![![-1777, 86338, -4212], ![1208, 318006, 0]], ![![-1287, 62888, -3068], ![907, 231634, 0]], ![![-771, 37737, -1841], ![549, 138996, 0]]]
  g := ![![![1, 0, 0], ![-110, 151, 0], ![-66, 0, 151]], ![![-1, 1, 0], ![29, -41, 2], ![-48, 86, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-21, 20, 1]] ![![151, 0, 0], ![-41, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-6191, 151, 0]], ![![-3171, 3020, 151], ![453, -755, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-41, 1, 0]]], ![![![-21, 20, 1]], ![![3, -5, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-3, -29, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-3, -29, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![154, 128, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-3, -29, 1], ![-457, 83, -57], ![12241, -2665, 54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -128, 157]], ![![-1, -1, 1], ![53, 47, -57], ![25, -61, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [104, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 156], [0, 1]]
 g := ![![[138, 12], [126], [127, 110], [121, 76], [34, 39], [143], [1]], ![[143, 145], [126], [42, 47], [48, 81], [11, 118], [143], [1]]]
 h' := ![![[92, 156], [13, 144], [137, 35], [133, 61], [75, 62], [26, 143], [53, 92], [0, 1]], ![[0, 1], [73, 13], [60, 122], [93, 96], [127, 95], [151, 14], [39, 65], [92, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [75, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [104, 65, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16, -5074, 1837]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1802, -1530, 1837]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![57, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![57, 1, 0]] 
 ![![157, 0, 0], ![57, 1, 0], ![103, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![57, 1, 0], ![1, 57, 2], ![-428, 86, 58]]]
  hmulB := by decide  
  f := ![![![-3410, -249643, -8760], ![-2669, 687660, 0]], ![![-1248, -90624, -3180], ![-941, 249630, 0]], ![![-2207, -163778, -5747], ![-1834, 451140, 0]]]
  g := ![![![1, 0, 0], ![-57, 157, 0], ![-103, 0, 157]], ![![0, 1, 0], ![-22, 57, 2], ![-72, 86, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-3, -29, 1]] ![![157, 0, 0], ![57, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![8949, 157, 0]], ![![-471, -4553, 157], ![-628, -1570, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![57, 1, 0]]], ![![![-3, -29, 1]], ![![-4, -10, 0]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [144, 127, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 79, 35], [79, 83, 128], [0, 1]]
 g := ![![[29, 36, 156], [68, 52, 65], [68, 74], [4, 33], [55, 144], [31, 141, 1], []], ![[74, 84, 141, 115], [26, 61, 135, 146], [119, 90], [54, 65], [141, 4], [40, 131, 61, 38], [96, 84]], ![[75, 37, 88, 19], [50, 28, 131, 89], [43, 88], [16, 156], [20, 100], [124, 39, 139, 148], [3, 84]]]
 h' := ![![[62, 79, 35], [151, 34, 51], [99, 2, 126], [130, 88, 143], [124, 61, 14], [100, 46, 12], [0, 0, 1], [0, 1]], ![[79, 83, 128], [46, 28, 44], [125, 92, 96], [132, 132, 116], [128, 139, 37], [63, 65, 161], [126, 15, 83], [62, 79, 35]], ![[0, 1], [154, 101, 68], [158, 69, 104], [112, 106, 67], [42, 126, 112], [92, 52, 153], [104, 148, 79], [79, 83, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 129], []]
 b := ![[], [124, 53, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [144, 127, 22, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-66667, 143929, -47922]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-409, 883, -294]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-32, -53, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-32, -53, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![135, 114, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-32, -53, 1], ![-481, 54, -105], ![22513, -4729, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-135, -114, 167]], ![![-1, -1, 1], ![82, 72, -105], ![134, -29, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [109, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 166], [0, 1]]
 g := ![![[35, 31], [143, 93], [29, 100], [57], [28], [51, 8], [1]], ![[6, 136], [56, 74], [124, 67], [57], [28], [92, 159], [1]]]
 h' := ![![[26, 166], [111, 71], [12, 107], [20, 157], [87, 97], [119, 144], [58, 26], [0, 1]], ![[0, 1], [120, 96], [122, 60], [94, 10], [104, 70], [22, 23], [66, 141], [26, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [85, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [109, 141, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49575, 11020, 2045]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1950, -1330, 2045]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-62, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-62, 1, 0]] 
 ![![167, 0, 0], ![105, 1, 0], ![166, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-62, 1, 0], ![1, -62, 2], ![-428, 86, -61]]]
  hmulB := by decide  
  f := ![![![-774, 67265, -2170], ![835, 181195, 0]], ![![-495, 42281, -1364], ![502, 113894, 0]], ![![-756, 66862, -2157], ![866, 180110, 0]]]
  g := ![![![1, 0, 0], ![-105, 167, 0], ![-166, 0, 167]], ![![-1, 1, 0], ![37, -62, 2], ![4, 86, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-32, -53, 1]] ![![167, 0, 0], ![-62, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-10354, 167, 0]], ![![-5344, -8851, 167], ![1503, 3340, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-62, 1, 0]]], ![![![-32, -53, 1]], ![![9, 20, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-4, -49, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-4, -49, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![169, 124, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-4, -49, 1], ![-477, 82, -97], ![20801, -4385, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-169, -124, 173]], ![![-1, -1, 1], ![92, 70, -97], ![88, -49, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [68, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 172], [0, 1]]
 g := ![![[96, 25], [4], [131, 29], [170, 96], [51], [82, 40], [1]], ![[35, 148], [4], [81, 144], [88, 77], [51], [19, 133], [1]]]
 h' := ![![[46, 172], [33, 5], [88, 171], [31, 95], [35, 142], [133, 140], [105, 46], [0, 1]], ![[0, 1], [90, 168], [169, 2], [76, 78], [166, 31], [172, 33], [145, 127], [46, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [52, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [68, 127, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5992, -2718, 405]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-361, -306, 405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-76, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-76, 1, 0]] 
 ![![173, 0, 0], ![97, 1, 0], ![140, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-76, 1, 0], ![1, -76, 2], ![-428, 86, -75]]]
  hmulB := by decide  
  f := ![![![-4715, 531666, -13992], ![5190, 1210308, 0]], ![![-2629, 298055, -7844], ![2942, 678506, 0]], ![![-3820, 430250, -11323], ![4190, 979440, 0]]]
  g := ![![![1, 0, 0], ![-97, 173, 0], ![-140, 0, 173]], ![![-1, 1, 0], ![41, -76, 2], ![10, 86, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-4, -49, 1]] ![![173, 0, 0], ![-76, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-13148, 173, 0]], ![![-692, -8477, 173], ![-173, 3806, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-76, 1, 0]]], ![![![-4, -49, 1]], ![![-1, 22, -1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-33, 62, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-33, 62, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![146, 62, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-33, 62, 1], ![-366, 53, 125], ![-26707, 5161, 115]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -62, 179]], ![![-1, 0, 1], ![-104, -43, 125], ![-243, -11, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [137, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 178], [0, 1]]
 g := ![![[156, 138], [56, 172], [151], [27], [111, 36], [32, 29], [1]], ![[24, 41], [16, 7], [151], [27], [61, 143], [121, 150], [1]]]
 h' := ![![[108, 178], [25, 106], [59, 107], [124, 35], [8, 122], [91, 173], [42, 108], [0, 1]], ![[0, 1], [17, 73], [159, 72], [145, 144], [117, 57], [159, 6], [71, 71], [108, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [6, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [137, 71, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5876, -1973, 1686]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1408, -595, 1686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![54, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![54, 1, 0]] 
 ![![179, 0, 0], ![54, 1, 0], ![64, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![54, 1, 0], ![1, 54, 2], ![-428, 86, 55]]]
  hmulB := by decide  
  f := ![![![-1097, -68037, -2520], ![-537, 225540, 0]], ![![-326, -20519, -760], ![-178, 68020, 0]], ![![-388, -24326, -901], ![-206, 80640, 0]]]
  g := ![![![1, 0, 0], ![-54, 179, 0], ![-64, 0, 179]], ![![0, 1, 0], ![-17, 54, 2], ![-48, 86, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-33, 62, 1]] ![![179, 0, 0], ![54, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![9666, 179, 0]], ![![-5907, 11098, 179], ![-2148, 3401, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![54, 1, 0]]], ![![![-33, 62, 1]], ![![-12, 19, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-68, -74, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-68, -74, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![113, 107, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-68, -74, 1], ![-502, 18, -147], ![31501, -6535, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -107, 181]], ![![-1, -1, 1], ![89, 87, -147], ![209, -3, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [172, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 180], [0, 1]]
 g := ![![[13, 20], [122], [178, 106], [180], [127, 125], [59, 114], [1]], ![[0, 161], [122], [91, 75], [180], [91, 56], [3, 67], [1]]]
 h' := ![![[117, 180], [17, 54], [154, 22], [163, 58], [57, 19], [169, 46], [9, 117], [0, 1]], ![[0, 1], [0, 127], [13, 159], [71, 123], [108, 162], [121, 135], [123, 64], [117, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [113, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [172, 64, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4398, -4275, 1880]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1198, -1135, 1880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-34, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-34, 1, 0]] 
 ![![181, 0, 0], ![147, 1, 0], ![56, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-34, 1, 0], ![1, -34, 2], ![-428, 86, -33]]]
  hmulB := by decide  
  f := ![![![1549, -56097, 3300], ![-543, -298650, 0]], ![![1273, -45558, 2680], ![-361, -242540, 0]], ![![480, -17356, 1021], ![-164, -92400, 0]]]
  g := ![![![1, 0, 0], ![-147, 181, 0], ![-56, 0, 181]], ![![-1, 1, 0], ![27, -34, 2], ![-62, 86, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-68, -74, 1]] ![![181, 0, 0], ![-34, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-6154, 181, 0]], ![![-12308, -13394, 181], ![1810, 2534, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-34, 1, 0]]], ![![![-68, -74, 1]], ![![10, 14, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-78, -44, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-78, -44, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![113, 147, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-78, -44, 1], ![-472, 8, -87], ![18661, -3955, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -147, 191]], ![![-1, -1, 1], ![49, 67, -87], ![119, 7, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [55, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [185, 190], [0, 1]]
 g := ![![[14, 12], [83, 92], [140, 77], [33, 67], [35, 68], [62, 36], [1]], ![[133, 179], [104, 99], [60, 114], [13, 124], [9, 123], [37, 155], [1]]]
 h' := ![![[185, 190], [19, 143], [131, 130], [95, 162], [176, 81], [28, 100], [136, 185], [0, 1]], ![[0, 1], [116, 48], [115, 61], [78, 29], [72, 110], [1, 91], [172, 6], [185, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [81, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [55, 6, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45399, -16616, 3260]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1691, -2596, 3260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![87, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![87, 1, 0]] 
 ![![191, 0, 0], ![87, 1, 0], ![36, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![87, 1, 0], ![1, 87, 2], ![-428, 86, 88]]]
  hmulB := by decide  
  f := ![![![-2748, -360251, -8282], ![-3056, 790931, 0]], ![![-1277, -164075, -3772], ![-1336, 360226, 0]], ![![-543, -67901, -1561], ![-521, 149076, 0]]]
  g := ![![![1, 0, 0], ![-87, 191, 0], ![-36, 0, 191]], ![![0, 1, 0], ![-40, 87, 2], ![-58, 86, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-78, -44, 1]] ![![191, 0, 0], ![87, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![16617, 191, 0]], ![![-14898, -8404, 191], ![-7258, -3820, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![87, 1, 0]]], ![![![-78, -44, 1]], ![![-38, -20, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-134, -52, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-134, -52, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![59, 141, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-134, -52, 1], ![-480, -48, -103], ![22085, -4643, -100]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -141, 193]], ![![-1, -1, 1], ![29, 75, -103], ![145, 49, -100]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [11, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 192], [0, 1]]
 g := ![![[22, 31], [7], [131], [56], [81], [72], [144, 1]], ![[47, 162], [7], [131], [56], [81], [72], [95, 192]]]
 h' := ![![[144, 192], [158, 80], [87, 59], [131, 175], [19, 153], [36, 9], [153, 74], [0, 1]], ![[0, 1], [98, 113], [91, 134], [48, 18], [49, 40], [174, 184], [1, 119], [144, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [60, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [11, 49, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24741, -41132, 20477]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6388, -15173, 20477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-90, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-90, 1, 0]] 
 ![![193, 0, 0], ![103, 1, 0], ![100, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-90, 1, 0], ![1, -90, 2], ![-428, 86, -89]]]
  hmulB := by decide  
  f := ![![![-1154, 168742, -3750], ![1544, 361875, 0]], ![![-639, 89996, -2000], ![773, 193000, 0]], ![![-590, 87431, -1943], ![817, 187500, 0]]]
  g := ![![![1, 0, 0], ![-103, 193, 0], ![-100, 0, 193]], ![![-1, 1, 0], ![47, -90, 2], ![-2, 86, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-134, -52, 1]] ![![193, 0, 0], ![-90, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-17370, 193, 0]], ![![-25862, -10036, 193], ![11580, 4632, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-90, 1, 0]]], ![![![-134, -52, 1]], ![![60, 24, -1]]]]
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


lemma PB211I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB211I3 : PrimesBelowBoundCertificateInterval O 137 193 211 where
  m := 11
  g := ![2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB211I3_primes
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
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
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
  β := ![I139N1, I151N1, I157N1, I167N1, I173N1, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N1], [], [I167N1], [I173N1], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
