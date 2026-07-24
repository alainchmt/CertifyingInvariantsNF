
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![21, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![21, 1, 0]] 
 ![![139, 0, 0], ![21, 1, 0], ![115, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![21, 1, 0], ![0, 21, 1], ![153, -47, 22]]]
  hmulB := by decide  
  f := ![![![988, 47, 0], ![-6533, 0, 0]], ![![126, 6, 0], ![-833, 0, 0]], ![![802, 38, 0], ![-5303, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 139, 0], ![-115, 0, 139]], ![![0, 1, 0], ![-4, 21, 1], ![-10, -47, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![42, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![42, 1, 0]] 
 ![![139, 0, 0], ![42, 1, 0], ![43, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![42, 1, 0], ![0, 42, 1], ![153, -47, 43]]]
  hmulB := by decide  
  f := ![![![2437, 58, 0], ![-8062, 0, 0]], ![![714, 17, 0], ![-2362, 0, 0]], ![![769, 18, 0], ![-2544, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 139, 0], ![-43, 0, 139]], ![![0, 1, 0], ![-13, 42, 1], ![2, -47, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-64, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-64, 1, 0]] 
 ![![139, 0, 0], ![75, 1, 0], ![74, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-64, 1, 0], ![0, -64, 1], ![153, -47, -63]]]
  hmulB := by decide  
  f := ![![![5825, -91, 0], ![12649, 0, 0]], ![![3201, -50, 0], ![6951, 0, 0]], ![![3102, -48, 0], ![6736, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 139, 0], ![-74, 0, 139]], ![![-1, 1, 0], ![34, -64, 1], ![60, -47, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![21, 1, 0]] ![![139, 0, 0], ![42, 1, 0]]
  ![![139, 0, 0], ![48, 63, 1]] where
 M := ![![![19321, 0, 0], ![5838, 139, 0]], ![![2919, 139, 0], ![882, 63, 1]]]
 hmul := by decide  
 g := ![![![![91, -63, -1], ![139, 0, 0]], ![![-6, -62, -1], ![139, 0, 0]]], ![![![-27, -62, -1], ![139, 0, 0]], ![![-42, -63, -1], ![140, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![48, 63, 1]] ![![139, 0, 0], ![-64, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8896, 139, 0]], ![![6672, 8757, 139], ![-2919, -4031, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-64, 1, 0]]], ![![![48, 63, 1]], ![![-21, -29, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-26, -47, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-26, -47, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![123, 102, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-26, -47, 1], ![153, -73, -46], ![-7038, 2315, -119]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-123, -102, 149]], ![![-1, -1, 1], ![39, 31, -46], ![51, 97, -119]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [24, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 148], [0, 1]]
 g := ![![[121, 118], [110], [126, 31], [123], [124, 116], [114], [1]], ![[0, 31], [110], [98, 118], [123], [0, 33], [114], [1]]]
 h' := ![![[76, 148], [41, 72], [105, 40], [44, 39], [4, 47], [75, 99], [125, 76], [0, 1]], ![[0, 1], [0, 77], [16, 109], [28, 110], [0, 102], [0, 50], [90, 73], [76, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [87, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [24, 73, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483, -61, -116]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99, 79, -116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![46, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![46, 1, 0]] 
 ![![149, 0, 0], ![46, 1, 0], ![119, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![46, 1, 0], ![0, 46, 1], ![153, -47, 47]]]
  hmulB := by decide  
  f := ![![![2531, 55, 0], ![-8195, 0, 0]], ![![782, 17, 0], ![-2532, 0, 0]], ![![1993, 43, 0], ![-6453, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 149, 0], ![-119, 0, 149]], ![![0, 1, 0], ![-15, 46, 1], ![-22, -47, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-26, -47, 1]] ![![149, 0, 0], ![46, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![6854, 149, 0]], ![![-3874, -7003, 149], ![-1043, -2235, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![46, 1, 0]]], ![![![-26, -47, 1]], ![![-7, -15, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![93, 25, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![93, 25, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![93, 25, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![93, 25, 1], ![153, 46, 26], ![3978, -1069, 72]]]
  hmulB := by decide  
  f := ![![![-92, -25, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -25, 151]], ![![0, 0, 1], ![-15, -4, 26], ![-18, -19, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [46, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 150], [0, 1]]
 g := ![![[13, 125], [93, 90], [81, 74], [31], [118, 99], [36], [1]], ![[8, 26], [29, 61], [72, 77], [31], [108, 52], [36], [1]]]
 h' := ![![[6, 150], [101, 27], [49, 111], [148, 136], [8, 129], [7, 117], [105, 6], [0, 1]], ![[0, 1], [112, 124], [111, 40], [58, 15], [27, 22], [105, 34], [141, 145], [6, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [2, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [46, 145, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-557, 1232, 7]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 7, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-26, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-26, 1, 0]] 
 ![![151, 0, 0], ![125, 1, 0], ![79, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-26, 1, 0], ![0, -26, 1], ![153, -47, -25]]]
  hmulB := by decide  
  f := ![![![3381, -130, 0], ![19630, 0, 0]], ![![2835, -109, 0], ![16460, 0, 0]], ![![1773, -68, 0], ![10294, 1, 0]]]
  g := ![![![1, 0, 0], ![-125, 151, 0], ![-79, 0, 151]], ![![-1, 1, 0], ![21, -26, 1], ![53, -47, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![93, 25, 1]] ![![151, 0, 0], ![-26, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-3926, 151, 0]], ![![14043, 3775, 151], ![-2265, -604, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-26, 1, 0]]], ![![![93, 25, 1]], ![![-15, -4, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [75, 106, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 111, 133], [39, 45, 24], [0, 1]]
 g := ![![[73, 10, 106], [88, 19], [47, 115, 147], [82, 38, 67], [81, 103, 118], [59, 1], []], ![[80, 149, 135, 50], [106, 118], [120, 10, 126, 8], [88, 152, 146, 45], [24, 145, 86, 149], [32, 141], [82, 105]], ![[127, 122, 77, 24], [12, 106], [12, 112, 133, 54], [79, 124, 4, 8], [68, 103, 120, 119], [144, 75], [34, 105]]]
 h' := ![![[20, 111, 133], [11, 20, 48], [86, 153, 31], [130, 25, 124], [48, 73, 99], [128, 108, 78], [0, 0, 1], [0, 1]], ![[39, 45, 24], [103, 82, 110], [108, 105, 78], [96, 104, 113], [127, 102, 34], [139, 75, 133], [59, 119, 45], [20, 111, 133]], ![[0, 1], [69, 55, 156], [59, 56, 48], [51, 28, 77], [91, 139, 24], [66, 131, 103], [70, 38, 111], [39, 45, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 73], []]
 b := ![[], [67, 155, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [75, 106, 98, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![116337, -2512, 2512]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![741, -16, 16]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-12, 27, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-12, 27, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![151, 27, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-12, 27, 1], ![153, -59, 28], ![4284, -1163, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-151, -27, 163]], ![![-1, 0, 1], ![-25, -5, 28], ![55, -2, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [146, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 162], [0, 1]]
 g := ![![[67, 115], [60, 56], [65], [36], [74], [87, 4], [1]], ![[0, 48], [111, 107], [65], [36], [74], [79, 159], [1]]]
 h' := ![![[161, 162], [42, 21], [2, 43], [110, 126], [98, 6], [12, 20], [17, 161], [0, 1]], ![[0, 1], [0, 142], [79, 120], [21, 37], [86, 157], [135, 143], [21, 2], [161, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [86, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [146, 2, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![608, 1240, -431]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![403, 79, -431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-28, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-28, 1, 0]] 
 ![![163, 0, 0], ![135, 1, 0], ![31, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-28, 1, 0], ![0, -28, 1], ![153, -47, -27]]]
  hmulB := by decide  
  f := ![![![3165, -113, 0], ![18419, 0, 0]], ![![2633, -94, 0], ![15323, 0, 0]], ![![649, -23, 0], ![3777, 1, 0]]]
  g := ![![![1, 0, 0], ![-135, 163, 0], ![-31, 0, 163]], ![![-1, 1, 0], ![23, -28, 1], ![45, -47, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-12, 27, 1]] ![![163, 0, 0], ![-28, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4564, 163, 0]], ![![-1956, 4401, 163], ![489, -815, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-28, 1, 0]]], ![![![-12, 27, 1]], ![![3, -5, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [11, 35, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 20, 162], [156, 146, 5], [0, 1]]
 g := ![![[21, 79, 132], [166, 79, 162], [141, 156, 77], [94, 44], [89, 6], [79, 92, 1], []], ![[143, 9, 138, 150], [153, 28, 131, 100], [46, 92, 64, 122], [98, 108], [21, 152], [73, 64, 161, 133], [96, 25]], ![[148, 158, 163, 34], [139, 149, 29, 142], [94, 91, 33, 146], [32, 38], [86, 50], [47, 42, 110, 163], [86, 25]]]
 h' := ![![[103, 20, 162], [11, 134, 74], [119, 144, 50], [68, 41, 54], [10, 149, 82], [133, 64, 29], [0, 0, 1], [0, 1]], ![[156, 146, 5], [130, 160, 114], [118, 76, 67], [115, 123, 164], [109, 165, 38], [29, 148, 73], [34, 151, 146], [103, 20, 162]], ![[0, 1], [112, 40, 146], [37, 114, 50], [157, 3, 116], [26, 20, 47], [53, 122, 65], [10, 16, 20], [156, 146, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 79], []]
 b := ![[], [140, 58, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [11, 35, 75, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45758, 3507, -5678]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![274, 21, -34]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [35, 171, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 99, 32], [42, 73, 141], [0, 1]]
 g := ![![[23, 60, 136], [158, 151], [43, 49, 9], [110, 134, 14], [110, 41], [26, 102, 1], []], ![[30, 159, 142, 75], [25, 31], [153, 92, 159, 75], [78, 171, 119, 123], [154, 163], [42, 16, 53, 123], [64, 159]], ![[53, 151, 159, 154], [9, 136], [162, 134, 159, 91], [7, 14, 96, 156], [24, 100], [118, 26, 160, 17], [128, 159]]]
 h' := ![![[60, 99, 32], [115, 144, 89], [52, 134, 18], [129, 57, 3], [78, 26, 35], [128, 115, 53], [0, 0, 1], [0, 1]], ![[42, 73, 141], [45, 2, 33], [48, 9, 66], [17, 60, 140], [106, 65, 100], [47, 117, 110], [149, 42, 73], [60, 99, 32]], ![[0, 1], [65, 27, 51], [42, 30, 89], [84, 56, 30], [49, 82, 38], [102, 114, 10], [52, 131, 99], [42, 73, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 102], []]
 b := ![[], [2, 34, 159], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [35, 171, 71, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1264976, -203794, -10726]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7312, -1178, -62]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [43, 151, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 24, 175], [178, 154, 4], [0, 1]]
 g := ![![[156, 53, 101], [12, 90, 125], [150, 5], [136, 22], [54, 82, 75], [85, 93, 1], []], ![[62, 158, 29, 35], [55, 7, 55, 103], [69, 169], [159, 121], [44, 167, 118, 176], [132, 116, 142, 6], [43, 16]], ![[109, 67, 49, 13], [105, 41, 67, 110], [160, 110], [32, 60], [156, 132, 44, 5], [5, 176, 79, 156], [35, 16]]]
 h' := ![![[94, 24, 175], [21, 153, 97], [69, 60, 150], [84, 129, 30], [5, 31, 102], [104, 171, 84], [0, 0, 1], [0, 1]], ![[178, 154, 4], [128, 33, 6], [165, 81, 127], [39, 175, 166], [130, 49, 11], [35, 78, 80], [6, 16, 154], [94, 24, 175]], ![[0, 1], [44, 172, 76], [128, 38, 81], [122, 54, 162], [148, 99, 66], [150, 109, 15], [107, 163, 24], [178, 154, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 38], []]
 b := ![[], [138, 62, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [43, 151, 86, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-136040, 58712, -4117]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-760, 328, -23]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5254, -191, -100]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-5254, -191, -100]] 
 ![![181, 0, 0], ![0, 181, 0], ![172, 163, 1]] where
  M :=![![![-5254, -191, -100], ![-15300, -554, -291], ![-44523, -1623, -845]]]
  hmulB := by decide  
  f := ![![![23, -5, -1]], ![![-153, 70, -6]], ![![-121, 59, -6]]]
  g := ![![![66, 89, -100], ![192, 259, -291], ![557, 752, -845]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [172, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 180], [0, 1]]
 g := ![![[78, 20], [145], [21, 142], [169], [133, 122], [178, 122], [1]], ![[0, 161], [145], [155, 39], [169], [164, 59], [28, 59], [1]]]
 h' := ![![[159, 180], [102, 54], [8, 67], [86, 93], [111, 168], [154, 159], [9, 159], [0, 1]], ![[0, 1], [0, 127], [163, 114], [31, 88], [35, 13], [95, 22], [131, 22], [159, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [119, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [172, 22, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1396, 258, -135]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 123, -135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 5, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-23, 5, 1]] 
 ![![181, 0, 0], ![17, 1, 0], ![73, 0, 1]] where
  M :=![![![-23, 5, 1], ![153, -70, 6], ![918, -129, -64]]]
  hmulB := by decide  
  f := ![![![5254, 191, 100]], ![![578, 21, 11]], ![![2365, 86, 45]]]
  g := ![![![-1, 5, 1], ![5, -70, 6], ![43, -129, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-5254, -191, -100]] ![![-23, 5, 1]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![34, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![34, 1, 0]] 
 ![![191, 0, 0], ![34, 1, 0], ![181, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![34, 1, 0], ![0, 34, 1], ![153, -47, 35]]]
  hmulB := by decide  
  f := ![![![3129, 92, 0], ![-17572, 0, 0]], ![![510, 15, 0], ![-2864, 0, 0]], ![![2931, 86, 0], ![-16460, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 191, 0], ![-181, 0, 191]], ![![0, 1, 0], ![-7, 34, 1], ![-24, -47, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![38, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![38, 1, 0]] 
 ![![191, 0, 0], ![38, 1, 0], ![84, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![38, 1, 0], ![0, 38, 1], ![153, -47, 39]]]
  hmulB := by decide  
  f := ![![![4409, 116, 0], ![-22156, 0, 0]], ![![874, 23, 0], ![-4392, 0, 0]], ![![1908, 50, 0], ![-9588, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 191, 0], ![-84, 0, 191]], ![![0, 1, 0], ![-8, 38, 1], ![-7, -47, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-73, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-73, 1, 0]] 
 ![![191, 0, 0], ![118, 1, 0], ![19, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-73, 1, 0], ![0, -73, 1], ![153, -47, -72]]]
  hmulB := by decide  
  f := ![![![12922, -177, 0], ![33807, 0, 0]], ![![7958, -109, 0], ![20820, 0, 0]], ![![1342, -18, 0], ![3511, 1, 0]]]
  g := ![![![1, 0, 0], ![-118, 191, 0], ![-19, 0, 191]], ![![-1, 1, 0], ![45, -73, 1], ![37, -47, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![34, 1, 0]] ![![191, 0, 0], ![38, 1, 0]]
  ![![191, 0, 0], ![-45, 72, 1]] where
 M := ![![![36481, 0, 0], ![7258, 191, 0]], ![![6494, 191, 0], ![1292, 72, 1]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![38, 1, 0], ![0, 0, 0]]], ![![![34, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-45, 72, 1]] ![![191, 0, 0], ![-73, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13943, 191, 0]], ![![-8595, 13752, 191], ![3438, -5348, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-73, 1, 0]]], ![![![-45, 72, 1]], ![![18, -28, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![51, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![51, 1, 0]] 
 ![![193, 0, 0], ![51, 1, 0], ![101, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![51, 1, 0], ![0, 51, 1], ![153, -47, 52]]]
  hmulB := by decide  
  f := ![![![2296, 45, 0], ![-8685, 0, 0]], ![![612, 12, 0], ![-2315, 0, 0]], ![![1136, 22, 0], ![-4297, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 193, 0], ![-101, 0, 193]], ![![0, 1, 0], ![-14, 51, 1], ![-14, -47, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-36, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-36, 1, 0]] 
 ![![193, 0, 0], ![157, 1, 0], ![55, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-36, 1, 0], ![0, -36, 1], ![153, -47, -35]]]
  hmulB := by decide  
  f := ![![![2701, -75, 0], ![14475, 0, 0]], ![![2233, -62, 0], ![11967, 0, 0]], ![![763, -21, 0], ![4089, 1, 0]]]
  g := ![![![1, 0, 0], ![-157, 193, 0], ![-55, 0, 193]], ![![-1, 1, 0], ![29, -36, 1], ![49, -47, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-16, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-16, 1, 0]] 
 ![![193, 0, 0], ![177, 1, 0], ![130, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-16, 1, 0], ![0, -16, 1], ![153, -47, -15]]]
  hmulB := by decide  
  f := ![![![2929, -183, 0], ![35319, 0, 0]], ![![2689, -168, 0], ![32425, 0, 0]], ![![1986, -124, 0], ![23948, 1, 0]]]
  g := ![![![1, 0, 0], ![-177, 193, 0], ![-130, 0, 193]], ![![-1, 1, 0], ![14, -16, 1], ![54, -47, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![51, 1, 0]] ![![193, 0, 0], ![-36, 1, 0]]
  ![![193, 0, 0], ![94, 15, 1]] where
 M := ![![![37249, 0, 0], ![-6948, 193, 0]], ![![9843, 193, 0], ![-1836, 15, 1]]]
 hmul := by decide  
 g := ![![![![99, -15, -1], ![193, 0, 0]], ![![-36, 1, 0], ![0, 0, 0]]], ![![![-43, -14, -1], ![193, 0, 0]], ![![-10, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![94, 15, 1]] ![![193, 0, 0], ![-16, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-3088, 193, 0]], ![![18142, 2895, 193], ![-1351, -193, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-16, 1, 0]]], ![![![94, 15, 1]], ![![-7, -1, 0]]]]
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


lemma PB271I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB271I3 : PrimesBelowBoundCertificateInterval O 137 193 271 where
  m := 11
  g := ![3, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB271I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![32761, 181]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
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
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I163N1, I181N1, I191N0, I191N1, I191N2, I193N0, I193N1, I193N2]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [], [I163N1], [], [], [], [I181N1], [I191N0, I191N1, I191N2], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
