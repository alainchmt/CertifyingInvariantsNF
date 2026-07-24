
import IdealArithmetic.Examples.NF3_1_564300_3.RI3_1_564300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-23, 36, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-23, 36, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![116, 36, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-23, 36, 1], ![30, -53, 180], ![1080, -1074, -53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-116, -36, 139]], ![![-1, 0, 1], ![-150, -47, 180], ![52, 6, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [106, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 138], [0, 1]]
 g := ![![[52, 80], [133, 122], [83], [24, 137], [28], [80], [1]], ![[0, 59], [12, 17], [83], [67, 2], [28], [80], [1]]]
 h' := ![![[48, 138], [80, 91], [55, 20], [97, 120], [110, 89], [115, 58], [33, 48], [0, 1]], ![[0, 1], [0, 48], [42, 119], [19, 19], [73, 50], [119, 81], [113, 91], [48, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [113, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [106, 91, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![166, -145, -116]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98, 29, -116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-41, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-41, 1, 0]] 
 ![![139, 0, 0], ![98, 1, 0], ![53, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-41, 1, 0], ![0, -41, 5], ![30, -30, -41]]]
  hmulB := by decide  
  f := ![![![4019, -98, 0], ![13622, 0, 0]], ![![2830, -69, 0], ![9592, 0, 0]], ![![1569, -30, -1], ![5318, 28, 0]]]
  g := ![![![1, 0, 0], ![-98, 139, 0], ![-53, 0, 139]], ![![-1, 1, 0], ![27, -41, 5], ![37, -30, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-23, 36, 1]] ![![139, 0, 0], ![-41, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-5699, 139, 0]], ![![-3197, 5004, 139], ![973, -1529, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-41, 1, 0]]], ![![![-23, 36, 1]], ![![7, -11, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![67, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![67, 1, 0]] 
 ![![149, 0, 0], ![67, 1, 0], ![26, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![67, 1, 0], ![0, 67, 5], ![30, -30, 67]]]
  hmulB := by decide  
  f := ![![![3016, 45, 0], ![-6705, 0, 0]], ![![1340, 20, 0], ![-2979, 0, 0]], ![![502, -6, -1], ![-1116, 30, 0]]]
  g := ![![![1, 0, 0], ![-67, 149, 0], ![-26, 0, 149]], ![![0, 1, 0], ![-31, 67, 5], ![2, -30, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-56, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-56, 1, 0]] 
 ![![149, 0, 0], ![93, 1, 0], ![88, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-56, 1, 0], ![0, -56, 5], ![30, -30, -56]]]
  hmulB := by decide  
  f := ![![![785, -14, 0], ![2086, 0, 0]], ![![505, -9, 0], ![1342, 0, 0]], ![![520, 2, -1], ![1382, 30, 0]]]
  g := ![![![1, 0, 0], ![-93, 149, 0], ![-88, 0, 149]], ![![-1, 1, 0], ![32, -56, 5], ![52, -30, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-11, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-11, 1, 0]] 
 ![![149, 0, 0], ![138, 1, 0], ![95, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-11, 1, 0], ![0, -11, 5], ![30, -30, -11]]]
  hmulB := by decide  
  f := ![![![1387, -126, 0], ![18774, 0, 0]], ![![1288, -117, 0], ![17434, 0, 0]], ![![883, -78, -1], ![11952, 30, 0]]]
  g := ![![![1, 0, 0], ![-138, 149, 0], ![-95, 0, 149]], ![![-1, 1, 0], ![7, -11, 5], ![35, -30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![67, 1, 0]] ![![149, 0, 0], ![-56, 1, 0]]
  ![![149, 0, 0], ![84, 32, 1]] where
 M := ![![![22201, 0, 0], ![-8344, 149, 0]], ![![9983, 149, 0], ![-3752, 11, 5]]]
 hmul := by decide  
 g := ![![![![65, -32, -1], ![149, 0, 0]], ![![-56, 1, 0], ![0, 0, 0]]], ![![![-17, -31, -1], ![149, 0, 0]], ![![-28, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![84, 32, 1]] ![![149, 0, 0], ![-11, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-1639, 149, 0]], ![![12516, 4768, 149], ![-894, -298, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-11, 1, 0]]], ![![![84, 32, 1]], ![![-6, -2, 1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [66, 90, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 81, 41], [29, 69, 110], [0, 1]]
 g := ![![[81, 71, 88], [1, 147, 97], [115, 72, 103], [109, 5], [58, 69, 29], [119, 1], []], ![[67, 84, 51, 93], [129, 126, 135, 115], [106, 115, 43, 73], [16, 91], [58, 66, 112, 112], [3, 80], [113, 20]], ![[53, 95, 81, 110], [33, 39, 87, 105], [6, 123, 45, 4], [129, 37], [42, 24, 78, 105], [74, 68], [44, 20]]]
 h' := ![![[90, 81, 41], [85, 113, 115], [111, 34, 90], [145, 39, 109], [98, 45, 55], [149, 96, 28], [0, 0, 1], [0, 1]], ![[29, 69, 110], [129, 140, 35], [98, 145, 54], [96, 68, 60], [47, 96, 53], [38, 72, 130], [38, 70, 69], [90, 81, 41]], ![[0, 1], [16, 49, 1], [100, 123, 7], [40, 44, 133], [131, 10, 43], [133, 134, 144], [51, 81, 81], [29, 69, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 55], []]
 b := ![[], [140, 4, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [66, 90, 32, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41827, -44092, 10117]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![277, -292, 67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [83, 96, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 103, 138], [69, 53, 19], [0, 1]]
 g := ![![[97, 130, 115], [152, 156], [76, 110, 121], [91, 74, 108], [103, 15, 67], [25, 1], []], ![[139, 10, 151, 109], [56, 140], [88, 139, 54, 146], [44, 11, 150, 117], [18, 123, 147, 56], [145, 140], [87, 47]], ![[140, 105, 33, 31], [89, 124], [86, 76, 86, 86], [52, 154, 8, 138], [87, 67, 146, 27], [64, 90], [49, 47]]]
 h' := ![![[113, 103, 138], [100, 72, 30], [129, 34, 28], [140, 54, 146], [86, 71, 39], [123, 29, 58], [0, 0, 1], [0, 1]], ![[69, 53, 19], [92, 145, 65], [117, 86, 53], [7, 153, 118], [128, 43, 90], [37, 150, 11], [53, 35, 53], [113, 103, 138]], ![[0, 1], [140, 97, 62], [84, 37, 76], [0, 107, 50], [23, 43, 28], [143, 135, 88], [66, 122, 103], [69, 53, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 69], []]
 b := ![[], [96, 45, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [83, 96, 132, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![273337, -5652, 5652]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1741, -36, 36]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [134, 81, 143, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 43, 122], [90, 119, 41], [0, 1]]
 g := ![![[110, 92, 58], [133, 47, 145], [48, 134], [], [36, 95], [156, 20, 1], []], ![[32, 26, 46, 79], [155, 142, 67, 29], [111, 74], [117, 140], [149, 133], [138, 148, 53, 5], [102, 51]], ![[36, 145, 124, 71], [80, 117, 146, 62], [87, 158], [138, 140], [21, 158], [104, 158, 137, 14], [20, 51]]]
 h' := ![![[93, 43, 122], [108, 2, 59], [152, 40, 109], [155, 140, 121], [36, 11], [123, 6, 62], [0, 0, 1], [0, 1]], ![[90, 119, 41], [18, 51, 93], [80, 6, 84], [11, 141, 20], [81, 147, 38], [18, 119, 123], [34, 74, 119], [93, 43, 122]], ![[0, 1], [99, 110, 11], [71, 117, 133], [112, 45, 22], [48, 5, 125], [108, 38, 141], [41, 89, 43], [90, 119, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 48], []]
 b := ![[], [60, 31, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [134, 81, 143, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54931, 68134, -61940]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-337, 418, -380]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-19, 70, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-19, 70, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![148, 70, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-19, 70, 1], ![30, -49, 350], ![2100, -2094, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-148, -70, 167]], ![![-1, 0, 1], ![-310, -147, 350], ![56, 8, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [69, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 166], [0, 1]]
 g := ![![[94, 32], [13, 36], [30, 137], [56], [65], [92, 61], [1]], ![[123, 135], [150, 131], [55, 30], [56], [65], [69, 106], [1]]]
 h' := ![![[27, 166], [105, 52], [101, 6], [93, 53], [28, 132], [165, 30], [98, 27], [0, 1]], ![[0, 1], [6, 115], [96, 161], [21, 114], [85, 35], [140, 137], [159, 140], [27, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [156, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [69, 140, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129, -194, -165]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147, 68, -165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-16, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-16, 1, 0]] 
 ![![167, 0, 0], ![151, 1, 0], ![49, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-16, 1, 0], ![0, -16, 5], ![30, -30, -16]]]
  hmulB := by decide  
  f := ![![![1633, -102, 0], ![17034, 0, 0]], ![![1489, -93, 0], ![15532, 0, 0]], ![![487, -24, -2], ![5080, 67, 0]]]
  g := ![![![1, 0, 0], ![-151, 167, 0], ![-49, 0, 167]], ![![-1, 1, 0], ![13, -16, 5], ![32, -30, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-19, 70, 1]] ![![167, 0, 0], ![-16, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-2672, 167, 0]], ![![-3173, 11690, 167], ![334, -1169, 334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-16, 1, 0]]], ![![![-19, 70, 1]], ![![2, -7, 2]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-12, 86, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-12, 86, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![161, 86, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-12, 86, 1], ![30, -42, 430], ![2580, -2574, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-161, -86, 173]], ![![-1, 0, 1], ![-400, -214, 430], ![54, 6, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [2, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 172], [0, 1]]
 g := ![![[114, 169], [67], [121, 36], [35, 60], [151], [98, 84], [1]], ![[161, 4], [67], [44, 137], [22, 113], [151], [149, 89], [1]]]
 h' := ![![[118, 172], [129, 13], [104, 76], [103, 6], [54, 135], [150, 155], [171, 118], [0, 1]], ![[0, 1], [106, 160], [76, 97], [119, 167], [68, 38], [102, 18], [82, 55], [118, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [170, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [2, 55, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1198, -51, 1832]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1698, -911, 1832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-84, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-84, 1, 0]] 
 ![![173, 0, 0], ![89, 1, 0], ![42, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-84, 1, 0], ![0, -84, 5], ![30, -30, -84]]]
  hmulB := by decide  
  f := ![![![13441, -160, 0], ![27680, 0, 0]], ![![6973, -83, 0], ![14360, 0, 0]], ![![3402, 10, -3], ![7006, 104, 0]]]
  g := ![![![1, 0, 0], ![-89, 173, 0], ![-42, 0, 173]], ![![-1, 1, 0], ![42, -84, 5], ![36, -30, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-12, 86, 1]] ![![173, 0, 0], ![-84, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-14532, 173, 0]], ![![-2076, 14878, 173], ![1038, -7266, 346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-84, 1, 0]]], ![![![-12, 86, 1]], ![![6, -42, 2]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [8, 76, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 131, 19], [5, 47, 160], [0, 1]]
 g := ![![[83, 117, 149], [44, 94, 46], [40, 3], [138, 46], [92, 3, 13], [130, 57, 1], []], ![[71, 58, 88, 88], [49, 97, 129, 168], [161, 126], [39, 81], [164, 72, 117, 117], [101, 32, 84, 85], [137, 3]], ![[78, 67, 102, 72], [176, 49, 51, 103], [123, 70], [65, 36], [29, 77, 99, 112], [60, 127, 103, 79], [175, 3]]]
 h' := ![![[52, 131, 19], [6, 30, 111], [3, 47, 15], [12, 152, 19], [159, 47, 164], [34, 46, 27], [0, 0, 1], [0, 1]], ![[5, 47, 160], [159, 156, 59], [75, 98, 166], [162, 113, 22], [142, 44, 9], [18, 96, 174], [176, 145, 47], [52, 131, 19]], ![[0, 1], [39, 172, 9], [19, 34, 177], [65, 93, 138], [76, 88, 6], [13, 37, 157], [57, 34, 131], [5, 47, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 66], []]
 b := ![[], [136, 131, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [8, 76, 122, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25597, 25239, 5370]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, 141, 30]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-4, 89, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-4, 89, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![177, 89, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-4, 89, 1], ![30, -34, 445], ![2670, -2664, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-177, -89, 181]], ![![-1, 0, 1], ![-435, -219, 445], ![48, 2, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [165, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 180], [0, 1]]
 g := ![![[116, 147], [152], [57, 33], [46], [55, 38], [163, 125], [1]], ![[0, 34], [152], [127, 148], [46], [174, 143], [121, 56], [1]]]
 h' := ![![[46, 180], [128, 131], [7, 40], [94, 24], [156, 107], [74, 161], [16, 46], [0, 1]], ![[0, 1], [0, 50], [37, 141], [112, 157], [10, 74], [59, 20], [141, 135], [46, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [51, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [165, 135, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![285, 39, 155]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-150, -76, 155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-83, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-83, 1, 0]] 
 ![![181, 0, 0], ![98, 1, 0], ![34, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-83, 1, 0], ![0, -83, 5], ![30, -30, -83]]]
  hmulB := by decide  
  f := ![![![3321, -40, 0], ![7240, 0, 0]], ![![1910, -23, 0], ![4164, 0, 0]], ![![622, 59, -4], ![1356, 145, 0]]]
  g := ![![![1, 0, 0], ![-98, 181, 0], ![-34, 0, 181]], ![![-1, 1, 0], ![44, -83, 5], ![32, -30, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-4, 89, 1]] ![![181, 0, 0], ![-83, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-15023, 181, 0]], ![![-724, 16109, 181], ![362, -7421, 362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-83, 1, 0]]], ![![![-4, 89, 1]], ![![2, -41, 2]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![55, 14, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![55, 14, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![55, 14, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![55, 14, 1], ![30, 25, 70], ![420, -414, 25]]]
  hmulB := by decide  
  f := ![![![-54, -14, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -14, 191]], ![![0, 0, 1], ![-20, -5, 70], ![-5, -4, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [8, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 190], [0, 1]]
 g := ![![[172, 24], [32, 40], [146, 45], [139, 109], [67, 78], [133, 184], [1]], ![[0, 167], [0, 151], [110, 146], [90, 82], [81, 113], [24, 7], [1]]]
 h' := ![![[152, 190], [126, 62], [169, 68], [34, 42], [37, 49], [82, 90], [183, 152], [0, 1]], ![[0, 1], [0, 129], [0, 123], [115, 149], [36, 142], [10, 101], [176, 39], [152, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [8, 39, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1110, 794, 466]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, -30, 466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-70, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-70, 1, 0]] 
 ![![191, 0, 0], ![121, 1, 0], ![166, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-70, 1, 0], ![0, -70, 5], ![30, -30, -70]]]
  hmulB := by decide  
  f := ![![![12531, -179, 0], ![34189, 0, 0]], ![![7981, -114, 0], ![21775, 0, 0]], ![![10926, -170, 1], ![29810, -38, 0]]]
  g := ![![![1, 0, 0], ![-121, 191, 0], ![-166, 0, 191]], ![![-1, 1, 0], ![40, -70, 5], ![80, -30, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![55, 14, 1]] ![![191, 0, 0], ![-70, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13370, 191, 0]], ![![10505, 2674, 191], ![-3820, -955, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-70, 1, 0]]], ![![![55, 14, 1]], ![![-20, -5, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [169, 87, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 140, 188], [105, 52, 5], [0, 1]]
 g := ![![[43, 39, 98], [119, 121], [160, 189], [63, 21], [54, 48], [183, 55], [1]], ![[173, 180, 38, 30], [172, 32], [181, 157], [163, 186], [131, 8], [135, 101], [89, 185, 1, 68]], ![[123, 64, 74, 153], [95, 16], [45, 129], [160, 64], [8, 124], [68, 151], [106, 170, 117, 125]]]
 h' := ![![[67, 140, 188], [126, 131, 22], [101, 156, 11], [11, 188, 31], [129, 124, 139], [143, 137, 56], [24, 106, 172], [0, 1]], ![[105, 52, 5], [98, 54, 103], [71, 152, 178], [121, 27, 93], [29, 168, 46], [121, 110, 104], [82, 134, 115], [67, 140, 188]], ![[0, 1], [189, 8, 68], [178, 78, 4], [177, 171, 69], [191, 94, 8], [81, 139, 33], [46, 146, 99], [105, 52, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 184], []]
 b := ![[], [133, 108, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [169, 87, 21, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6176, 0, 0]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 0, 0]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB213I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB213I3 : PrimesBelowBoundCertificateInterval O 137 193 213 where
  m := 11
  g := ![2, 3, 1, 1, 1, 2, 2, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB213I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
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
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![7189057]
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
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N0, I149N1, I149N2, I167N1, I173N1, I181N1, I191N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [], [], [I167N1], [I173N1], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
