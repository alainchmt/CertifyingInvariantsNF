
import IdealArithmetic.Examples.NF3_1_536787_1.RI3_1_536787_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [6, 133, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 127, 85], [62, 11, 54], [0, 1]]
 g := ![![[103, 79, 46], [43, 129, 129], [14, 55], [64, 58, 120], [67, 36], [0, 1], []], ![[80, 45, 71, 21], [0, 123, 100, 74], [2, 113], [134, 9, 18, 123], [40, 34], [13, 121], [45, 136]], ![[105, 103, 53, 80], [96, 1, 137, 125], [130, 66], [86, 136, 69, 83], [36, 24], [90, 5], [76, 136]]]
 h' := ![![[77, 127, 85], [20, 91, 18], [32, 22, 44], [33, 122, 65], [15, 47, 113], [0, 133, 6], [0, 0, 1], [0, 1]], ![[62, 11, 54], [52, 18, 10], [105, 40, 130], [16, 135, 104], [87, 103, 95], [132, 25, 112], [99, 108, 11], [77, 127, 85]], ![[0, 1], [65, 30, 111], [70, 77, 104], [135, 21, 109], [48, 128, 70], [79, 120, 21], [52, 31, 127], [62, 11, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 6], []]
 b := ![[], [33, 1, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [6, 133, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20016, -556, -556]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -4, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -2, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![4, -2, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![4, 147, 1]] where
  M :=![![![4, -2, 1], ![141, 4, -2], ![-282, 141, 4]]]
  hmulB := by decide  
  f := ![![![2, 1, 0]], ![![0, 2, 1]], ![![1, 2, 1]]]
  g := ![![![0, -1, 1], ![1, 2, -2], ![-2, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [129, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 148], [0, 1]]
 g := ![![[14, 67], [143], [98, 53], [22], [69, 16], [26], [1]], ![[0, 82], [143], [38, 96], [22], [79, 133], [26], [1]]]
 h' := ![![[131, 148], [111, 31], [23, 21], [24, 84], [39, 52], [26, 4], [20, 131], [0, 1]], ![[0, 1], [0, 118], [92, 128], [2, 65], [146, 97], [103, 145], [46, 18], [131, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [42, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [129, 18, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1580, 1237, 52]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -43, 52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![149, 0, 0], ![2, 1, 0], ![145, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![141, 0, 2]]]
  hmulB := by decide  
  f := ![![![4, -2, 1]], ![![1, 0, 0]], ![![2, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![4, -2, 1]] ![![2, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [10, 27, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 108, 24], [87, 42, 127], [0, 1]]
 g := ![![[43, 51, 4], [124, 69, 37], [84, 136, 17], [103, 127], [55, 149, 49], [110, 1], []], ![[48, 75, 24, 115], [14, 2, 132, 30], [53, 6, 32, 82], [85, 103], [122, 4, 24, 146], [98, 103], [141, 123]], ![[61, 22, 134, 10], [41, 124, 140, 4], [79, 82, 142, 38], [139, 22], [147, 6, 99, 31], [99, 37], [38, 123]]]
 h' := ![![[23, 108, 24], [119, 16, 2], [66, 36, 43], [74, 124, 116], [54, 82, 60], [108, 40, 144], [0, 0, 1], [0, 1]], ![[87, 42, 127], [84, 80, 15], [6, 15, 103], [88, 103, 147], [118, 35, 109], [98, 122, 62], [25, 82, 42], [23, 108, 24]], ![[0, 1], [34, 55, 134], [57, 100, 5], [92, 75, 39], [24, 34, 133], [75, 140, 96], [92, 69, 108], [87, 42, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 139], []]
 b := ![[], [10, 23, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [10, 27, 41, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-73084, -14647, -6795]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-484, -97, -45]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![75, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![75, 1, 0]] 
 ![![157, 0, 0], ![75, 1, 0], ![27, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![75, 1, 0], ![0, 75, 1], ![141, 0, 75]]]
  hmulB := by decide  
  f := ![![![3226, 43, 0], ![-6751, 0, 0]], ![![1500, 20, 0], ![-3139, 0, 0]], ![![486, 6, 0], ![-1017, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 157, 0], ![-27, 0, 157]], ![![0, 1, 0], ![-36, 75, 1], ![-12, 0, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136, 26, 5]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![136, 26, 5]] 
 ![![157, 0, 0], ![115, 1, 0], ![120, 0, 1]] where
  M :=![![![136, 26, 5], ![705, 136, 26], ![3666, 705, 136]]]
  hmulB := by decide  
  f := ![![![166, -11, -4]], ![![118, -7, -3]], ![![117, -12, -2]]]
  g := ![![![-22, 26, 5], ![-115, 136, 26], ![-597, 705, 136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-33, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-33, 1, 0]] 
 ![![157, 0, 0], ![124, 1, 0], ![10, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-33, 1, 0], ![0, -33, 1], ![141, 0, -33]]]
  hmulB := by decide  
  f := ![![![4819, -146, 0], ![22922, 0, 0]], ![![3796, -115, 0], ![18056, 0, 0]], ![![370, -11, 0], ![1760, 1, 0]]]
  g := ![![![1, 0, 0], ![-124, 157, 0], ![-10, 0, 157]], ![![-1, 1, 0], ![26, -33, 1], ![3, 0, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![75, 1, 0]] ![![136, 26, 5]]
  ![![157, 0, 0], ![-10, 33, 1]] where
 M := ![![![21352, 4082, 785]], ![![10905, 2086, 401]]]
 hmul := by decide  
 g := ![![![![136, 26, 5], ![0, 0, 0]]], ![![![75, -5, 2], ![87, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-10, 33, 1]] ![![157, 0, 0], ![-33, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5181, 157, 0]], ![![-1570, 5181, 157], ![471, -1099, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-33, 1, 0]]], ![![![-10, 33, 1]], ![![3, -7, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![10, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![10, 1, 0]] 
 ![![163, 0, 0], ![10, 1, 0], ![63, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![10, 1, 0], ![0, 10, 1], ![141, 0, 10]]]
  hmulB := by decide  
  f := ![![![471, 47, 0], ![-7661, 0, 0]], ![![10, 1, 0], ![-162, 0, 0]], ![![171, 17, 0], ![-2781, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 163, 0], ![-63, 0, 163]], ![![0, 1, 0], ![-1, 10, 1], ![-3, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![62, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![62, 1, 0]] 
 ![![163, 0, 0], ![62, 1, 0], ![68, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![62, 1, 0], ![0, 62, 1], ![141, 0, 62]]]
  hmulB := by decide  
  f := ![![![3039, 49, 0], ![-7987, 0, 0]], ![![1178, 19, 0], ![-3096, 0, 0]], ![![1264, 20, 0], ![-3322, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 163, 0], ![-68, 0, 163]], ![![0, 1, 0], ![-24, 62, 1], ![-25, 0, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![406, 78, 15]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![406, 78, 15]] 
 ![![163, 0, 0], ![91, 1, 0], ![32, 0, 1]] where
  M :=![![![406, 78, 15], ![2115, 406, 78], ![10998, 2115, 406]]]
  hmulB := by decide  
  f := ![![![-134, 57, -6]], ![![-80, 31, -3]], ![![23, 6, -2]]]
  g := ![![![-44, 78, 15], ![-229, 406, 78], ![-1193, 2115, 406]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![10, 1, 0]] ![![163, 0, 0], ![62, 1, 0]]
  ![![134, -57, 6]] where
 M := ![![![26569, 0, 0], ![10106, 163, 0]], ![![1630, 163, 0], ![620, 72, 1]]]
 hmul := by decide  
 g := ![![![![-66178, -12714, -2445]], ![![-27287, -5242, -1008]]], ![![![-6175, -1186, -228]], ![![-2546, -489, -94]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![134, -57, 6]] ![![406, 78, 15]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![2, -13, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![2, -13, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![2, 154, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![2, -13, 1], ![141, 2, -13], ![-1833, 141, 2]]]
  hmulB := by decide  
  f := ![![![-1, 13, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -154, 167]], ![![0, -1, 1], ![1, 12, -13], ![-11, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [147, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 166], [0, 1]]
 g := ![![[143, 25], [120, 42], [12, 121], [97], [14], [81, 107], [1]], ![[0, 142], [0, 125], [48, 46], [97], [14], [157, 60], [1]]]
 h' := ![![[21, 166], [62, 5], [73, 84], [77, 156], [108, 40], [117, 66], [20, 21], [0, 1]], ![[0, 1], [0, 162], [0, 83], [13, 11], [113, 127], [0, 101], [127, 146], [21, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [143, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [147, 146, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-552, 1417, -443]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 417, -443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![13, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![13, 1, 0]] 
 ![![167, 0, 0], ![13, 1, 0], ![165, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![13, 1, 0], ![0, 13, 1], ![141, 0, 13]]]
  hmulB := by decide  
  f := ![![![1067, 82, 0], ![-13694, 0, 0]], ![![65, 5, 0], ![-834, 0, 0]], ![![1055, 81, 0], ![-13540, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 167, 0], ![-165, 0, 167]], ![![0, 1, 0], ![-2, 13, 1], ![-12, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![2, -13, 1]] ![![167, 0, 0], ![13, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![2171, 167, 0]], ![![334, -2171, 167], ![167, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![13, 1, 0]]], ![![![2, -13, 1]], ![![1, -1, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2558, 2360, -359]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-2558, 2360, -359]] 
 ![![173, 0, 0], ![0, 173, 0], ![77, 58, 1]] where
  M :=![![![-2558, 2360, -359], ![-50619, -2558, 2360], ![332760, -50619, -2558]]]
  hmulB := by decide  
  f := ![![![728348, 139937, 26886]], ![![3790926, 728348, 139937]], ![![1709177, 328383, 63092]]]
  g := ![![![145, 134, -359], ![-1343, -806, 2360], ![3062, 565, -2558]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [156, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 172], [0, 1]]
 g := ![![[69, 34], [139], [28, 24], [31, 121], [149], [61, 60], [1]], ![[161, 139], [139], [154, 149], [104, 52], [149], [30, 113], [1]]]
 h' := ![![[135, 172], [60, 131], [130, 100], [8, 102], [112, 162], [172, 29], [17, 135], [0, 1]], ![[0, 1], [99, 42], [136, 73], [111, 71], [11, 11], [108, 144], [77, 38], [135, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [170, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [156, 38, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![438, 103, -37]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 13, -37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-728348, -139937, -26886]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-728348, -139937, -26886]] 
 ![![173, 0, 0], ![115, 1, 0], ![96, 0, 1]] where
  M :=![![![-728348, -139937, -26886], ![-3790926, -728348, -139937], ![-19731117, -3790926, -728348]]]
  hmulB := by decide  
  f := ![![![2558, -2360, 359]], ![![1993, -1554, 225]], ![![-504, -1017, 214]]]
  g := ![![![103731, -139937, -26886], ![539902, -728348, -139937], ![2810097, -3790926, -728348]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-2558, 2360, -359]] ![![-728348, -139937, -26886]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![51, 87, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![51, 87, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![51, 87, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![51, 87, 1], ![141, 51, 87], ![12267, 141, 51]]]
  hmulB := by decide  
  f := ![![![-50, -87, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -87, 179]], ![![0, 0, 1], ![-24, -42, 87], ![54, -24, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [162, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 178], [0, 1]]
 g := ![![[121, 144], [4, 75], [75], [121], [168, 85], [147, 47], [1]], ![[84, 35], [160, 104], [75], [121], [130, 94], [166, 132], [1]]]
 h' := ![![[88, 178], [68, 167], [35, 95], [152, 84], [171, 168], [172, 62], [17, 88], [0, 1]], ![[0, 1], [86, 12], [161, 84], [26, 95], [98, 11], [79, 117], [64, 91], [88, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [21, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [162, 91, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5612, 1908, 454]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, -210, 454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-87, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-87, 1, 0]] 
 ![![179, 0, 0], ![92, 1, 0], ![128, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-87, 1, 0], ![0, -87, 1], ![141, 0, -87]]]
  hmulB := by decide  
  f := ![![![12268, -141, 0], ![25239, 0, 0]], ![![6352, -73, 0], ![13068, 0, 0]], ![![8830, -101, 0], ![18166, 1, 0]]]
  g := ![![![1, 0, 0], ![-92, 179, 0], ![-128, 0, 179]], ![![-1, 1, 0], ![44, -87, 1], ![63, 0, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![51, 87, 1]] ![![179, 0, 0], ![-87, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-15573, 179, 0]], ![![9129, 15573, 179], ![-4296, -7518, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-87, 1, 0]]], ![![![51, 87, 1]], ![![-24, -42, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![18, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![18, 1, 0]] 
 ![![181, 0, 0], ![18, 1, 0], ![38, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![18, 1, 0], ![0, 18, 1], ![141, 0, 18]]]
  hmulB := by decide  
  f := ![![![2503, 139, 0], ![-25159, 0, 0]], ![![234, 13, 0], ![-2352, 0, 0]], ![![506, 28, 0], ![-5086, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 181, 0], ![-38, 0, 181]], ![![0, 1, 0], ![-2, 18, 1], ![-3, 0, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![23, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![23, 1, 0]] 
 ![![181, 0, 0], ![23, 1, 0], ![14, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![23, 1, 0], ![0, 23, 1], ![141, 0, 23]]]
  hmulB := by decide  
  f := ![![![1312, 57, 0], ![-10317, 0, 0]], ![![138, 6, 0], ![-1085, 0, 0]], ![![72, 3, 0], ![-566, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 181, 0], ![-14, 0, 181]], ![![0, 1, 0], ![-3, 23, 1], ![-1, 0, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-41, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-41, 1, 0]] 
 ![![181, 0, 0], ![140, 1, 0], ![129, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-41, 1, 0], ![0, -41, 1], ![141, 0, -41]]]
  hmulB := by decide  
  f := ![![![2912, -71, 0], ![12851, 0, 0]], ![![2256, -55, 0], ![9956, 0, 0]], ![![2060, -50, 0], ![9091, 1, 0]]]
  g := ![![![1, 0, 0], ![-140, 181, 0], ![-129, 0, 181]], ![![-1, 1, 0], ![31, -41, 1], ![30, 0, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![18, 1, 0]] ![![181, 0, 0], ![23, 1, 0]]
  ![![181, 0, 0], ![52, 41, 1]] where
 M := ![![![32761, 0, 0], ![4163, 181, 0]], ![![3258, 181, 0], ![414, 41, 1]]]
 hmul := by decide  
 g := ![![![![129, -41, -1], ![181, 0, 0]], ![![-29, -40, -1], ![181, 0, 0]]], ![![![-34, -40, -1], ![181, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![52, 41, 1]] ![![181, 0, 0], ![-41, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-7421, 181, 0]], ![![9412, 7421, 181], ![-1991, -1629, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-41, 1, 0]]], ![![![52, 41, 1]], ![![-11, -9, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-19, 73, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-19, 73, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![172, 73, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-19, 73, 1], ![141, -19, 73], ![10293, 141, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-172, -73, 191]], ![![-1, 0, 1], ![-65, -28, 73], ![71, 8, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [88, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 190], [0, 1]]
 g := ![![[159, 133], [70, 15], [158, 121], [23, 75], [176, 98], [36, 109], [1]], ![[136, 58], [99, 176], [150, 70], [168, 116], [149, 93], [43, 82], [1]]]
 h' := ![![[142, 190], [143, 18], [39, 145], [77, 11], [174, 71], [79, 17], [103, 142], [0, 1]], ![[0, 1], [25, 173], [1, 46], [111, 180], [133, 120], [10, 174], [21, 49], [142, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [34, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [88, 49, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-806, 282, -38]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 16, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-73, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-73, 1, 0]] 
 ![![191, 0, 0], ![118, 1, 0], ![19, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-73, 1, 0], ![0, -73, 1], ![141, 0, -73]]]
  hmulB := by decide  
  f := ![![![12922, -177, 0], ![33807, 0, 0]], ![![7958, -109, 0], ![20820, 0, 0]], ![![1342, -18, 0], ![3511, 1, 0]]]
  g := ![![![1, 0, 0], ![-118, 191, 0], ![-19, 0, 191]], ![![-1, 1, 0], ![45, -73, 1], ![8, 0, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-19, 73, 1]] ![![191, 0, 0], ![-73, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13943, 191, 0]], ![![-3629, 13943, 191], ![1528, -5348, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-73, 1, 0]]], ![![![-19, 73, 1]], ![![8, -28, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [36, 119, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [176, 91, 179], [17, 101, 14], [0, 1]]
 g := ![![[38, 149, 145], [96, 138], [128, 128], [189, 8], [136, 166], [], [1]], ![[65, 183, 120, 24], [30, 65], [59, 28], [53, 126], [86, 59], [87, 23], [130, 4, 47, 151]], ![[105, 157, 26, 143], [36, 101], [75, 95], [96, 69], [165, 8], [1, 23], [65, 155, 137, 42]]]
 h' := ![![[176, 91, 179], [110, 149, 97], [51, 130, 36], [151, 15, 30], [59, 167, 104], [138, 76, 72], [157, 74], [0, 1]], ![[17, 101, 14], [64, 93, 184], [117, 137, 79], [120, 145, 118], [171, 31, 60], [117, 128, 32], [57, 172, 122], [176, 91, 179]], ![[0, 1], [37, 144, 105], [102, 119, 78], [183, 33, 45], [92, 188, 29], [7, 182, 89], [64, 140, 71], [17, 101, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 168], []]
 b := ![[], [56, 192, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [36, 119, 0, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159225, 965, 1930]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![825, 5, 10]
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



lemma PB208I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB208I3 : PrimesBelowBoundCertificateInterval O 137 193 208 where
  m := 11
  g := ![1, 2, 1, 3, 3, 2, 2, 2, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB208I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
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
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
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
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I157N0, I157N1, I157N2, I163N0, I163N1, I163N2, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1]
  Il := ![[], [I149N1], [], [I157N0, I157N1, I157N2], [I163N0, I163N1, I163N2], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
