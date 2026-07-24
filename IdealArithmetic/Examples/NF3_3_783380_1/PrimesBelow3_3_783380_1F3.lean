
import IdealArithmetic.Examples.NF3_3_783380_1.RI3_3_783380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187889, -653075, -247695]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-187889, -653075, -247695]] 
 ![![139, 0, 0], ![0, 139, 0], ![13, 75, 1]] where
  M :=![![![-187889, -653075, -247695], ![-2476950, -8609519, -3265375], ![-6530750, -22699940, -8609519]]]
  hmulB := by decide  
  f := ![![![5999, 125, -220]], ![![-2200, -1481, 625]], ![![-617, -760, 306]]]
  g := ![![![21814, 128950, -247695], ![287575, 1699954, -3265375], ![758223, 4482115, -8609519]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [85, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 138], [0, 1]]
 g := ![![[22, 9], [40, 65], [117], [138, 52], [24], [77], [1]], ![[11, 130], [115, 74], [117], [59, 87], [24], [77], [1]]]
 h' := ![![[76, 138], [75, 3], [60, 75], [85, 16], [131, 82], [124, 21], [54, 76], [0, 1]], ![[0, 1], [25, 136], [61, 64], [50, 123], [108, 57], [52, 118], [131, 63], [76, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [107, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [85, 63, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105, 7, -24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 13, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5999, -125, 220]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-5999, -125, 220]] 
 ![![139, 0, 0], ![42, 1, 0], ![92, 0, 1]] where
  M :=![![![-5999, -125, 220], ![2200, 1481, -625], ![-1250, -3810, 1481]]]
  hmulB := by decide  
  f := ![![![187889, 653075, 247695]], ![![74592, 259271, 98335]], ![![171342, 595560, 225881]]]
  g := ![![![-151, -125, 220], ![-18, 1481, -625], ![162, -3810, 1481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-187889, -653075, -247695]] ![![-5999, -125, 220]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-449, 9, 17]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-449, 9, 17]] 
 ![![149, 0, 0], ![0, 149, 0], ![70, 132, 1]] where
  M :=![![![-449, 9, 17], ![170, 129, 45], ![90, 340, 129]]]
  hmulB := by decide  
  f := ![![![9, 31, -12]], ![![-120, -399, 155]], ![![-100, -332, 129]]]
  g := ![![![-11, -15, 17], ![-20, -39, 45], ![-60, -112, 129]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [96, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 148], [0, 1]]
 g := ![![[65, 104], [24], [48, 103], [19], [18, 64], [26], [1]], ![[0, 45], [24], [114, 46], [19], [127, 85], [26], [1]]]
 h' := ![![[18, 148], [52, 113], [11, 60], [137, 38], [60, 67], [15, 141], [53, 18], [0, 1]], ![[0, 1], [0, 36], [48, 89], [76, 111], [74, 82], [20, 8], [79, 131], [18, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [104, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [96, 131, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-154, -648, 713]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-336, -636, 713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -31, 12]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-9, -31, 12]] 
 ![![149, 0, 0], ![85, 1, 0], ![45, 0, 1]] where
  M :=![![![-9, -31, 12], ![120, 399, -155], ![-310, -1030, 399]]]
  hmulB := by decide  
  f := ![![![449, -9, -17]], ![![255, -6, -10]], ![![135, -5, -6]]]
  g := ![![![14, -31, 12], ![-180, 399, -155], ![465, -1030, 399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-449, 9, 17]] ![![-9, -31, 12]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2809, 11330, -4378]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![2809, 11330, -4378]] 
 ![![151, 0, 0], ![0, 151, 0], ![91, 5, 1]] where
  M :=![![![2809, 11330, -4378], ![-43780, -146043, 56650], ![113300, 376464, -146043]]]
  hmulB := by decide  
  f := ![![![12399, 43098, 16346]], ![![163460, 568163, 215490]], ![![15739, 54707, 20749]]]
  g := ![![![2657, 220, -4378], ![-34430, -2843, 56650], ![88763, 7329, -146043]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [73, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 150], [0, 1]]
 g := ![![[22, 20], [8, 110], [87, 55], [47], [107, 47], [5], [1]], ![[65, 131], [18, 41], [92, 96], [47], [125, 104], [5], [1]]]
 h' := ![![[55, 150], [20, 41], [142, 84], [62, 120], [41, 97], [132, 97], [78, 55], [0, 1]], ![[0, 1], [10, 110], [81, 67], [18, 31], [91, 54], [31, 54], [83, 96], [55, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [54, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [73, 96, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1995, -98, 71]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -3, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12399, -43098, -16346]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-12399, -43098, -16346]] 
 ![![151, 0, 0], ![126, 1, 0], ![26, 0, 1]] where
  M :=![![![-12399, -43098, -16346], ![-163460, -568163, -215490], ![-430980, -1498024, -568163]]]
  hmulB := by decide  
  f := ![![![-2809, -11330, 4378]], ![![-2054, -8487, 3278]], ![![-1234, -4444, 1721]]]
  g := ![![![38695, -43098, -16346], ![510118, -568163, -215490], ![1344982, -1498024, -568163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![2809, 11330, -4378]] ![![-12399, -43098, -16346]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 962, 366]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![239, 962, 366]] 
 ![![157, 0, 0], ![0, 157, 0], ![68, 97, 1]] where
  M :=![![![239, 962, 366], ![3660, 12683, 4810], ![9620, 33440, 12683]]]
  hmulB := by decide  
  f := ![![![-77, -242, 94]], ![![940, 3119, -1210]], ![![532, 1771, -687]]]
  g := ![![![-157, -220, 366], ![-2060, -2891, 4810], ![-5432, -7623, 12683]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [156, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 156], [0, 1]]
 g := ![![[90, 156], [110], [143, 113], [57, 71], [147, 3], [93], [1]], ![[0, 1], [110], [108, 44], [10, 86], [103, 154], [93], [1]]]
 h' := ![![[90, 156], [149, 28], [143, 61], [57, 120], [147, 89], [94, 72], [1, 90], [0, 1]], ![[0, 1], [0, 129], [138, 96], [24, 37], [150, 68], [137, 85], [94, 67], [90, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [77, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [156, 67, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![164, -117, 104]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -65, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -242, 94]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-77, -242, 94]] 
 ![![157, 0, 0], ![143, 1, 0], ![55, 0, 1]] where
  M :=![![![-77, -242, 94], ![940, 3119, -1210], ![-2420, -8040, 3119]]]
  hmulB := by decide  
  f := ![![![239, 962, 366]], ![![241, 957, 364]], ![![145, 550, 209]]]
  g := ![![![187, -242, 94], ![-2411, 3119, -1210], ![6215, -8040, 3119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![239, 962, 366]] ![![-77, -242, 94]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17891, -52, -495]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![17891, -52, -495]] 
 ![![163, 0, 0], ![0, 163, 0], ![88, 63, 1]] where
  M :=![![![17891, -52, -495], ![-4950, 1061, -260], ![-520, -2758, 1061]]]
  hmulB := by decide  
  f := ![![![-2507, -8714, -3305]], ![![-33050, -114877, -43570]], ![![-14662, -50963, -19329]]]
  g := ![![![377, 191, -495], ![110, 107, -260], ![-576, -427, 1061]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [24, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 162], [0, 1]]
 g := ![![[5, 34], [19, 64], [96], [55], [36], [18, 56], [1]], ![[0, 129], [0, 99], [96], [55], [36], [144, 107], [1]]]
 h' := ![![[43, 162], [33, 94], [145, 8], [161, 52], [103, 113], [57, 6], [139, 43], [0, 1]], ![[0, 1], [0, 69], [0, 155], [115, 111], [72, 50], [152, 157], [32, 120], [43, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [3, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [24, 120, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44, -50, -81]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, 31, -81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2507, -8714, -3305]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-2507, -8714, -3305]] 
 ![![163, 0, 0], ![11, 1, 0], ![41, 0, 1]] where
  M :=![![![-2507, -8714, -3305], ![-33050, -114877, -43570], ![-87140, -302886, -114877]]]
  hmulB := by decide  
  f := ![![![17891, -52, -495]], ![![1177, 3, -35]], ![![4497, -30, -118]]]
  g := ![![![1404, -8714, -3305], ![18509, -114877, -43570], ![48801, -302886, -114877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![17891, -52, -495]] ![![-2507, -8714, -3305]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [89, 143, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 70, 164], [122, 96, 3], [0, 1]]
 g := ![![[70, 45, 19], [119, 64, 126], [75, 67, 126], [63, 16], [104, 81], [55, 71, 1], []], ![[74, 21, 97, 142], [49, 153, 40, 110], [91, 128, 59, 120], [75, 29], [87, 16], [102, 11, 49, 74], [52, 9]], ![[44, 141, 83, 50], [56, 23, 155, 144], [119, 156, 146, 107], [34, 157], [65, 25], [70, 81, 27, 4], [46, 9]]]
 h' := ![![[116, 70, 164], [97, 24, 112], [5, 84, 136], [89, 22, 136], [128, 155, 163], [115, 11, 9], [0, 0, 1], [0, 1]], ![[122, 96, 3], [138, 57, 159], [108, 104, 112], [14, 106, 131], [164, 47, 153], [15, 152, 163], [144, 154, 96], [116, 70, 164]], ![[0, 1], [87, 86, 63], [77, 146, 86], [112, 39, 67], [93, 132, 18], [37, 4, 162], [102, 13, 70], [122, 96, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 93], []]
 b := ![[], [63, 144, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [89, 143, 96, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400299, 1377416, 368235]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2397, 8248, 2205]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [167, 28, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 149, 148], [153, 23, 25], [0, 1]]
 g := ![![[78, 8, 95], [57, 89], [148, 94, 22], [24, 73, 152], [100, 149], [169, 102, 1], []], ![[58, 77, 66, 60], [96, 92], [48, 129, 18, 14], [144, 62, 42, 34], [8, 43], [113, 35, 30, 96], [75, 106]], ![[5, 87, 168, 36], [122, 56], [56, 56, 16, 118], [66, 17, 99, 1], [136, 90], [42, 69, 32, 41], [25, 106]]]
 h' := ![![[122, 149, 148], [6, 99, 21], [23, 29, 98], [144, 126, 56], [138, 18, 124], [149, 32, 29], [0, 0, 1], [0, 1]], ![[153, 23, 25], [35, 123, 84], [155, 67, 145], [51, 7, 41], [58, 138, 153], [150, 88, 40], [110, 119, 23], [122, 149, 148]], ![[0, 1], [61, 124, 68], [59, 77, 103], [52, 40, 76], [162, 17, 69], [62, 53, 104], [31, 54, 149], [153, 23, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 72], []]
 b := ![[], [167, 71, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [167, 28, 71, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519, 519, -173]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 3, -1]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3501, 6, -103]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![3501, 6, -103]] 
 ![![179, 0, 0], ![49, 1, 0], ![21, 0, 1]] where
  M :=![![![3501, 6, -103], ![-1030, -1, 30], ![60, -2, -1]]]
  hmulB := by decide  
  f := ![![![-61, -212, -77]], ![![-21, -73, -27]], ![![-19, -66, -24]]]
  g := ![![![30, 6, -103], ![-9, -1, 30], ![1, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![1, 3, 0]] 
 ![![179, 0, 0], ![60, 1, 0], ![175, 0, 1]] where
  M :=![![![1, 3, 0], ![0, 1, 15], ![30, 102, 1]]]
  hmulB := by decide  
  f := ![![![1529, 3, -45]], ![![510, 1, -15]], ![![1495, 3, -44]]]
  g := ![![![-1, 3, 0], ![-15, 1, 15], ![-35, 102, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, 2]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![1, 5, 2]] 
 ![![179, 0, 0], ![70, 1, 0], ![94, 0, 1]] where
  M :=![![![1, 5, 2], ![20, 69, 25], ![50, 174, 69]]]
  hmulB := by decide  
  f := ![![![-411, -3, 13]], ![![-160, -1, 5]], ![![-216, -2, 7]]]
  g := ![![![-3, 5, 2], ![-40, 69, 25], ![-104, 174, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![3501, 6, -103]] ![![1, 3, 0]]
  ![![411, 3, -13]] where
 M := ![![![411, 3, -13]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![411, 3, -13]] ![![1, 5, 2]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -1, 3]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-91, -1, 3]] 
 ![![181, 0, 0], ![71, 1, 0], ![114, 0, 1]] where
  M :=![![![-91, -1, 3], ![30, 11, -5], ![-10, -28, 11]]]
  hmulB := by decide  
  f := ![![![19, 73, 28]], ![![9, 34, 13]], ![![16, 60, 23]]]
  g := ![![![-2, -1, 3], ![-1, 11, -5], ![4, -28, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2379, -8271, -3137]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-2379, -8271, -3137]] 
 ![![181, 0, 0], ![122, 1, 0], ![64, 0, 1]] where
  M :=![![![-2379, -8271, -3137], ![-31370, -109037, -41355], ![-82710, -287488, -109037]]]
  hmulB := by decide  
  f := ![![![-1129, -4829, 1864]], ![![-658, -2911, 1123]], ![![-666, -2594, 1003]]]
  g := ![![![6671, -8271, -3137], ![87944, -109037, -41355], ![231874, -287488, -109037]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -224, 87]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-71, -224, 87]] 
 ![![181, 0, 0], ![169, 1, 0], ![116, 0, 1]] where
  M :=![![![-71, -224, 87], ![870, 2887, -1120], ![-2240, -7442, 2887]]]
  hmulB := by decide  
  f := ![![![-271, -766, -289]], ![![-269, -771, -291]], ![![-216, -638, -241]]]
  g := ![![![153, -224, 87], ![-1973, 2887, -1120], ![5086, -7442, 2887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-91, -1, 3]] ![![-2379, -8271, -3137]]
  ![![-271, -766, -289]] where
 M := ![![![-271, -766, -289]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-271, -766, -289]] ![![-71, -224, 87]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 86, 24]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![311, 86, 24]] 
 ![![191, 0, 0], ![0, 191, 0], ![5, 115, 1]] where
  M :=![![![311, 86, 24], ![240, 1127, 430], ![860, 2972, 1127]]]
  hmulB := by decide  
  f := ![![![41, 134, -52]], ![![-520, -1727, 670]], ![![-305, -1013, 393]]]
  g := ![![![1, -14, 24], ![-10, -253, 430], ![-25, -663, 1127]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [105, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 190], [0, 1]]
 g := ![![[165, 162], [139, 180], [42, 27], [146, 117], [2, 80], [169, 80], [1]], ![[69, 29], [96, 11], [26, 164], [13, 74], [89, 111], [65, 111], [1]]]
 h' := ![![[56, 190], [112, 60], [174, 107], [141, 72], [172, 58], [18, 56], [86, 56], [0, 1]], ![[0, 1], [34, 131], [54, 84], [162, 119], [173, 133], [98, 135], [166, 135], [56, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [65, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [105, 135, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145, 279, 411]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -246, 411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -134, 52]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-41, -134, 52]] 
 ![![191, 0, 0], ![189, 1, 0], ![152, 0, 1]] where
  M :=![![![-41, -134, 52], ![520, 1727, -670], ![-1340, -4452, 1727]]]
  hmulB := by decide  
  f := ![![![-311, -86, -24]], ![![-309, -91, -26]], ![![-252, -84, -25]]]
  g := ![![![91, -134, 52], ![-1173, 1727, -670], ![3024, -4452, 1727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![311, 86, 24]] ![![-41, -134, 52]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [182, 167, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 50, 79], [13, 142, 114], [0, 1]]
 g := ![![[117, 155, 21], [28, 54], [97, 129], [174, 190], [107, 107], [183, 92], [1]], ![[86, 5, 21, 13], [56, 36], [8, 65], [82, 107], [32, 81], [132, 143], [157, 76, 116, 117]], ![[162, 47, 34, 41], [54, 130], [64, 95], [21, 139], [11, 177], [154, 12], [160, 112, 75, 76]]]
 h' := ![![[129, 50, 79], [30, 78, 139], [84, 181, 61], [91, 26, 69], [140, 84, 169], [11, 166, 140], [11, 26, 142], [0, 1]], ![[13, 142, 114], [176, 142, 38], [116, 164, 187], [75, 76, 79], [157, 128, 140], [34, 144, 184], [133, 174, 23], [129, 50, 79]], ![[0, 1], [96, 166, 16], [184, 41, 138], [32, 91, 45], [103, 174, 77], [102, 76, 62], [97, 186, 28], [13, 142, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109, 53], []]
 b := ![[], [126, 28, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [182, 167, 51, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112712, -382526, 147066]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-584, -1982, 762]
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



lemma PB197I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 196 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 196 (by omega)

def PB197I3 : PrimesBelowBoundCertificateInterval O 137 196 197 where
  m := 11
  g := ![2, 2, 2, 2, 2, 1, 1, 3, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB197I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![181, 181, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I179N0, I179N1, I179N2, I181N0, I181N1, I181N2, I191N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [], [], [I179N0, I179N1, I179N2], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
