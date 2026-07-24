
import IdealArithmetic.Examples.NF3_1_462051_1.RI3_1_462051_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![65, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![65, 1, 0]] 
 ![![139, 0, 0], ![65, 1, 0], ![84, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![65, 1, 0], ![0, 65, 1], ![155, 36, 65]]]
  hmulB := by decide  
  f := ![![![2796, 43, 0], ![-5977, 0, 0]], ![![1300, 20, 0], ![-2779, 0, 0]], ![![1656, 25, 0], ![-3540, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 139, 0], ![-84, 0, 139]], ![![0, 1, 0], ![-31, 65, 1], ![-55, 36, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-51, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-51, 1, 0]] 
 ![![139, 0, 0], ![88, 1, 0], ![40, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-51, 1, 0], ![0, -51, 1], ![155, 36, -51]]]
  hmulB := by decide  
  f := ![![![2347, -46, 0], ![6394, 0, 0]], ![![1480, -29, 0], ![4032, 0, 0]], ![![682, -13, 0], ![1858, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 139, 0], ![-40, 0, 139]], ![![-1, 1, 0], ![32, -51, 1], ![-7, 36, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-14, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-14, 1, 0]] 
 ![![139, 0, 0], ![125, 1, 0], ![82, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-14, 1, 0], ![0, -14, 1], ![155, 36, -14]]]
  hmulB := by decide  
  f := ![![![169, -12, 0], ![1668, 0, 0]], ![![155, -11, 0], ![1530, 0, 0]], ![![114, -8, 0], ![1126, 1, 0]]]
  g := ![![![1, 0, 0], ![-125, 139, 0], ![-82, 0, 139]], ![![-1, 1, 0], ![12, -14, 1], ![-23, 36, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![65, 1, 0]] ![![139, 0, 0], ![-51, 1, 0]]
  ![![139, 0, 0], ![21, 14, 1]] where
 M := ![![![19321, 0, 0], ![-7089, 139, 0]], ![![9035, 139, 0], ![-3315, 14, 1]]]
 hmul := by decide  
 g := ![![![![118, -14, -1], ![139, 0, 0]], ![![-51, 1, 0], ![0, 0, 0]]], ![![![44, -13, -1], ![139, 0, 0]], ![![-24, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![21, 14, 1]] ![![139, 0, 0], ![-14, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-1946, 139, 0]], ![![2919, 1946, 139], ![-139, -139, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-14, 1, 0]]], ![![![21, 14, 1]], ![![-1, -1, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-30, -30, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-30, -30, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![119, 119, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-30, -30, 1], ![155, 6, -30], ![-4650, -925, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -119, 149]], ![![-1, -1, 1], ![25, 24, -30], ![-36, -11, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [119, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 148], [0, 1]]
 g := ![![[116, 144], [103], [78, 1], [104], [4, 118], [127], [1]], ![[0, 5], [103], [131, 148], [104], [0, 31], [127], [1]]]
 h' := ![![[53, 148], [109, 12], [105, 111], [87, 1], [120, 113], [91, 77], [30, 53], [0, 1]], ![[0, 1], [0, 137], [28, 38], [140, 148], [0, 36], [0, 72], [8, 96], [53, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [72, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [119, 96, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![429, 131, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 48, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![30, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![30, 1, 0]] 
 ![![149, 0, 0], ![30, 1, 0], ![143, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![30, 1, 0], ![0, 30, 1], ![155, 36, 30]]]
  hmulB := by decide  
  f := ![![![91, 3, 0], ![-447, 0, 0]], ![![-30, -1, 0], ![150, 0, 0]], ![![97, 3, 0], ![-477, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 149, 0], ![-143, 0, 149]], ![![0, 1, 0], ![-7, 30, 1], ![-35, 36, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-30, -30, 1]] ![![149, 0, 0], ![30, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![4470, 149, 0]], ![![-4470, -4470, 149], ![-745, -894, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![30, 1, 0]]], ![![![-30, -30, 1]], ![![-5, -6, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [80, 140, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 129, 55], [47, 21, 96], [0, 1]]
 g := ![![[47, 113, 47], [87, 147, 116], [121, 131, 43], [2, 138], [111, 105, 58], [62, 1], []], ![[113, 120, 40, 40], [130, 36, 79, 124], [143, 72, 102, 110], [109, 94], [116, 6, 140, 39], [72, 139], [4, 5]], ![[80, 104, 122, 54], [0, 102, 87, 96], [117, 96, 51, 111], [38, 34], [110, 2, 47, 140], [102, 31], [114, 5]]]
 h' := ![![[15, 129, 55], [137, 23, 54], [135, 102, 95], [77, 110, 88], [29, 145, 134], [23, 149, 80], [0, 0, 1], [0, 1]], ![[47, 21, 96], [33, 47, 134], [39, 141, 55], [11, 131, 46], [44, 39, 68], [94, 2, 60], [56, 41, 21], [15, 129, 55]], ![[0, 1], [88, 81, 114], [100, 59, 1], [22, 61, 17], [58, 118, 100], [11, 0, 11], [35, 110, 129], [47, 21, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 35], []]
 b := ![[], [137, 107, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [80, 140, 89, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![186183, 319516, 56021]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1233, 2116, 371]
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


def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![13, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![13, 1, 0]] 
 ![![157, 0, 0], ![13, 1, 0], ![145, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![13, 1, 0], ![0, 13, 1], ![155, 36, 13]]]
  hmulB := by decide  
  f := ![![![1574, 121, 0], ![-18997, 0, 0]], ![![130, 10, 0], ![-1569, 0, 0]], ![![1458, 112, 0], ![-17597, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 157, 0], ![-145, 0, 157]], ![![0, 1, 0], ![-2, 13, 1], ![-14, 36, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-26, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-26, 1, 0]] 
 ![![157, 0, 0], ![131, 1, 0], ![109, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-26, 1, 0], ![0, -26, 1], ![155, 36, -26]]]
  hmulB := by decide  
  f := ![![![3979, -153, 0], ![24021, 0, 0]], ![![3329, -128, 0], ![20097, 0, 0]], ![![2787, -107, 0], ![16825, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 157, 0], ![-109, 0, 157]], ![![-1, 1, 0], ![21, -26, 1], ![-11, 36, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![13, 1, 0]] ![![157, 0, 0], ![13, 1, 0]]
  ![![157, 0, 0], ![12, 26, 1]] where
 M := ![![![24649, 0, 0], ![2041, 157, 0]], ![![2041, 157, 0], ![169, 26, 1]]]
 hmul := by decide  
 g := ![![![![145, -26, -1], ![157, 0, 0]], ![![1, -25, -1], ![157, 0, 0]]], ![![![1, -25, -1], ![157, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![12, 26, 1]] ![![157, 0, 0], ![-26, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-4082, 157, 0]], ![![1884, 4082, 157], ![-157, -628, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-26, 1, 0]]], ![![![12, 26, 1]], ![![-1, -4, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![61, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![61, 1, 0]] 
 ![![163, 0, 0], ![61, 1, 0], ![28, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![61, 1, 0], ![0, 61, 1], ![155, 36, 61]]]
  hmulB := by decide  
  f := ![![![3478, 57, 0], ![-9291, 0, 0]], ![![1220, 20, 0], ![-3259, 0, 0]], ![![572, 9, 0], ![-1528, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 163, 0], ![-28, 0, 163]], ![![0, 1, 0], ![-23, 61, 1], ![-23, 36, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-49, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-49, 1, 0]] 
 ![![163, 0, 0], ![114, 1, 0], ![44, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-49, 1, 0], ![0, -49, 1], ![155, 36, -49]]]
  hmulB := by decide  
  f := ![![![785, -16, 0], ![2608, 0, 0]], ![![540, -11, 0], ![1794, 0, 0]], ![![260, -5, 0], ![864, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 163, 0], ![-44, 0, 163]], ![![-1, 1, 0], ![34, -49, 1], ![-11, 36, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-12, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-12, 1, 0]] 
 ![![163, 0, 0], ![151, 1, 0], ![19, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-12, 1, 0], ![0, -12, 1], ![155, 36, -12]]]
  hmulB := by decide  
  f := ![![![889, -74, 0], ![12062, 0, 0]], ![![829, -69, 0], ![11248, 0, 0]], ![![121, -10, 0], ![1642, 1, 0]]]
  g := ![![![1, 0, 0], ![-151, 163, 0], ![-19, 0, 163]], ![![-1, 1, 0], ![11, -12, 1], ![-31, 36, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![61, 1, 0]] ![![163, 0, 0], ![-49, 1, 0]]
  ![![163, 0, 0], ![-55, 12, 1]] where
 M := ![![![26569, 0, 0], ![-7987, 163, 0]], ![![9943, 163, 0], ![-2989, 12, 1]]]
 hmul := by decide  
 g := ![![![![163, 0, 0], ![0, 0, 0]], ![![6, -11, -1], ![163, 0, 0]]], ![![![61, 1, 0], ![0, 0, 0]], ![![37, -12, -1], ![164, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-55, 12, 1]] ![![163, 0, 0], ![-12, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-1956, 163, 0]], ![![-8965, 1956, 163], ![815, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-12, 1, 0]]], ![![![-55, 12, 1]], ![![5, -1, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-82, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-82, 1, 0]] 
 ![![167, 0, 0], ![85, 1, 0], ![123, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-82, 1, 0], ![0, -82, 1], ![155, 36, -82]]]
  hmulB := by decide  
  f := ![![![6971, -85, 0], ![14195, 0, 0]], ![![3609, -44, 0], ![7349, 0, 0]], ![![5207, -63, 0], ![10603, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 167, 0], ![-123, 0, 167]], ![![-1, 1, 0], ![41, -82, 1], ![43, 36, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-64, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-64, 1, 0]] 
 ![![167, 0, 0], ![103, 1, 0], ![79, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-64, 1, 0], ![0, -64, 1], ![155, 36, -64]]]
  hmulB := by decide  
  f := ![![![8513, -133, 0], ![22211, 0, 0]], ![![5249, -82, 0], ![13695, 0, 0]], ![![4057, -63, 0], ![10585, 1, 0]]]
  g := ![![![1, 0, 0], ![-103, 167, 0], ![-79, 0, 167]], ![![-1, 1, 0], ![39, -64, 1], ![9, 36, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-21, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-21, 1, 0]] 
 ![![167, 0, 0], ![146, 1, 0], ![60, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-21, 1, 0], ![0, -21, 1], ![155, 36, -21]]]
  hmulB := by decide  
  f := ![![![211, -10, 0], ![1670, 0, 0]], ![![190, -9, 0], ![1504, 0, 0]], ![![108, -5, 0], ![856, 1, 0]]]
  g := ![![![1, 0, 0], ![-146, 167, 0], ![-60, 0, 167]], ![![-1, 1, 0], ![18, -21, 1], ![-23, 36, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-82, 1, 0]] ![![167, 0, 0], ![-64, 1, 0]]
  ![![167, 0, 0], ![-96, 21, 1]] where
 M := ![![![27889, 0, 0], ![-10688, 167, 0]], ![![-13694, 167, 0], ![5248, -146, 1]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![32, -20, -1], ![167, 0, 0]]], ![![![14, -20, -1], ![167, 0, 0]], ![![32, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-96, 21, 1]] ![![167, 0, 0], ![-21, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-3507, 167, 0]], ![![-16032, 3507, 167], ![2171, -501, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-21, 1, 0]]], ![![![-96, 21, 1]], ![![13, -3, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![11, 77, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![11, 77, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![11, 77, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![11, 77, 1], ![155, 47, 77], ![11935, 2927, 47]]]
  hmulB := by decide  
  f := ![![![-10, -77, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -77, 173]], ![![0, 0, 1], ![-4, -34, 77], ![66, -4, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [12, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 172], [0, 1]]
 g := ![![[48, 109], [121], [32, 52], [132, 95], [52], [74, 135], [1]], ![[63, 64], [121], [9, 121], [80, 78], [52], [164, 38], [1]]]
 h' := ![![[116, 172], [165, 52], [135, 11], [146, 15], [78, 152], [150, 15], [161, 116], [0, 1]], ![[0, 1], [142, 121], [27, 162], [156, 158], [64, 21], [160, 158], [123, 57], [116, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [59, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [12, 57, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![150, 12, 108]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -48, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-77, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-77, 1, 0]] 
 ![![173, 0, 0], ![96, 1, 0], ![126, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-77, 1, 0], ![0, -77, 1], ![155, 36, -77]]]
  hmulB := by decide  
  f := ![![![1310, -17, 0], ![2941, 0, 0]], ![![694, -9, 0], ![1558, 0, 0]], ![![882, -11, 0], ![1980, 1, 0]]]
  g := ![![![1, 0, 0], ![-96, 173, 0], ![-126, 0, 173]], ![![-1, 1, 0], ![42, -77, 1], ![37, 36, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![11, 77, 1]] ![![173, 0, 0], ![-77, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-13321, 173, 0]], ![![1903, 13321, 173], ![-692, -5882, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-77, 1, 0]]], ![![![11, 77, 1]], ![![-4, -34, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15946, -5823, -774]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-15946, -5823, -774]] 
 ![![179, 0, 0], ![0, 179, 0], ![170, 122, 1]] where
  M :=![![![-15946, -5823, -774], ![-119970, -43810, -5823], ![-902565, -329598, -43810]]]
  hmulB := by decide  
  f := ![![![-374, -18, 9]], ![![1395, -50, -18]], ![![580, -47, -4]]]
  g := ![![![646, 495, -774], ![4860, 3724, -5823], ![36565, 28018, -43810]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [34, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 178], [0, 1]]
 g := ![![[97, 22], [84, 76], [129], [4], [166, 16], [88, 48], [1]], ![[36, 157], [36, 103], [129], [4], [24, 163], [20, 131], [1]]]
 h' := ![![[103, 178], [8, 77], [51, 75], [118, 32], [84, 2], [51, 175], [145, 103], [0, 1]], ![[0, 1], [63, 102], [79, 104], [13, 147], [111, 177], [176, 4], [14, 76], [103, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [9, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [34, 76, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-819, 1257, 91]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -55, 91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![374, 18, -9]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![374, 18, -9]] 
 ![![179, 0, 0], ![57, 1, 0], ![152, 0, 1]] where
  M :=![![![374, 18, -9], ![-1395, 50, 18], ![2790, -747, 50]]]
  hmulB := by decide  
  f := ![![![15946, 5823, 774]], ![![5748, 2099, 279]], ![![18583, 6786, 902]]]
  g := ![![![4, 18, -9], ![-39, 50, 18], ![211, -747, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-15946, -5823, -774]] ![![374, 18, -9]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [138, 71, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 116, 7], [124, 64, 174], [0, 1]]
 g := ![![[67, 172, 70], [18, 119], [119, 136, 27], [50, 55], [30, 75, 165], [45, 109, 1], []], ![[86, 52, 154, 54], [54, 73], [115, 2, 28, 35], [159, 135], [155, 26, 127, 30], [42, 151, 7, 74], [87, 49]], ![[131, 38, 147, 89], [165, 49], [26, 16, 159, 2], [154, 5], [172, 67, 134, 40], [179, 180, 23, 109], [101, 49]]]
 h' := ![![[166, 116, 7], [98, 115, 147], [49, 143, 149], [145, 133, 99], [23, 68, 112], [125, 44, 105], [0, 0, 1], [0, 1]], ![[124, 64, 174], [3, 169, 77], [45, 82, 39], [5, 123, 27], [107, 137, 42], [138, 66, 150], [165, 52, 64], [166, 116, 7]], ![[0, 1], [37, 78, 138], [1, 137, 174], [81, 106, 55], [95, 157, 27], [6, 71, 107], [171, 129, 116], [124, 64, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 158], []]
 b := ![[], [32, 150, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [138, 71, 72, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18462, 724, 724]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, 4, 4]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [42, 49, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 26, 112], [61, 164, 79], [0, 1]]
 g := ![![[127, 31, 115], [145, 20, 107], [29, 79, 65], [46, 133, 102], [167, 147, 169], [37, 75, 1], []], ![[147, 127, 74, 159], [4, 149, 53, 174], [166, 97, 84, 139], [8, 141, 180, 175], [133, 87, 41, 179], [102, 63, 138, 91], [28, 129]], ![[134, 87, 74, 100], [93, 132, 42, 2], [7, 149, 179, 107], [115, 86, 23, 4], [55, 184, 22, 125], [124, 168, 39, 115], [61, 129]]]
 h' := ![![[14, 26, 112], [22, 104, 45], [119, 138, 153], [169, 126, 175], [53, 71, 169], [165, 3, 13], [0, 0, 1], [0, 1]], ![[61, 164, 79], [162, 179, 119], [136, 160, 56], [41, 184, 28], [69, 173, 142], [73, 155, 176], [166, 50, 164], [14, 26, 112]], ![[0, 1], [75, 99, 27], [21, 84, 173], [7, 72, 179], [87, 138, 71], [135, 33, 2], [13, 141, 26], [61, 164, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 187], []]
 b := ![[], [132, 78, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [42, 49, 116, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2106348, 686454, 96646]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11028, 3594, 506]
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



lemma PB193I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 192 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 192 (by omega)

def PB193I3 : PrimesBelowBoundCertificateInterval O 137 192 193 where
  m := 10
  g := ![3, 2, 1, 3, 3, 3, 2, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191]
  hP := PB193I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![6967871]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
  β := ![I139N0, I139N1, I139N2, I149N1, I157N0, I157N1, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N1, I179N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [], [I157N0, I157N0, I157N1], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N1], [I179N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
