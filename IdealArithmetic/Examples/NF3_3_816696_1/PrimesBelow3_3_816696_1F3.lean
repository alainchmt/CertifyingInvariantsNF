
import IdealArithmetic.Examples.NF3_3_816696_1.RI3_3_816696_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [56, 24, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 122, 61], [61, 16, 78], [0, 1]]
 g := ![![[33, 0, 1], [120, 11, 116], [106, 25], [73, 62, 7], [10, 13], [20, 1], []], ![[38, 38, 96, 97], [105, 83, 80, 48], [1, 117], [138, 55, 11, 88], [77, 64], [89, 117], [66, 107]], ![[54, 117, 74, 30], [11, 81, 45, 24], [9, 121], [97, 15, 138, 5], [107, 116], [61, 11], [49, 107]]]
 h' := ![![[98, 122, 61], [91, 10, 138], [93, 75, 106], [82, 44, 5], [60, 102, 110], [131, 20, 98], [0, 0, 1], [0, 1]], ![[61, 16, 78], [28, 35, 38], [129, 69, 16], [18, 34, 123], [103, 41, 59], [55, 3, 8], [70, 73, 16], [98, 122, 61]], ![[0, 1], [2, 94, 102], [88, 134, 17], [6, 61, 11], [50, 135, 109], [75, 116, 33], [4, 66, 122], [61, 16, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 89], []]
 b := ![[], [25, 100, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [56, 24, 119, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75616, -47538, -6672]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-544, -342, -48]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6893, -4594, -1240]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-6893, -4594, -1240]] 
 ![![149, 0, 0], ![0, 149, 0], ![66, 15, 1]] where
  M :=![![![-6893, -4594, -1240], ![-83446, -55619, -15022], ![-367094, -244662, -66047]]]
  hmulB := by decide  
  f := ![![![12379, 262, -292]], ![![-20994, -439, 494]], ![![3430, 73, -81]]]
  g := ![![![503, 94, -1240], ![6094, 1139, -15022], ![26792, 5007, -66047]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [5, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 148], [0, 1]]
 g := ![![[16, 30], [26], [93, 19], [121], [71, 63], [142], [1]], ![[0, 119], [26], [63, 130], [121], [97, 86], [142], [1]]]
 h' := ![![[69, 148], [45, 103], [131, 18], [111, 67], [92, 138], [60, 19], [144, 69], [0, 1]], ![[0, 1], [0, 46], [32, 131], [115, 82], [78, 11], [30, 130], [137, 80], [69, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [14, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [5, 80, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3819, -1403, 3403]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1533, -352, 3403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12379, -262, 292]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-12379, -262, 292]] 
 ![![149, 0, 0], ![103, 1, 0], ![24, 0, 1]] where
  M :=![![![-12379, -262, 292], ![20994, 439, -494], ![-8966, -170, 207]]]
  hmulB := by decide  
  f := ![![![6893, 4594, 1240]], ![![5325, 3549, 958]], ![![3574, 2382, 643]]]
  g := ![![![51, -262, 292], ![-83, 439, -494], ![24, -170, 207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-6893, -4594, -1240]] ![![-12379, -262, 292]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6473, -90, 142]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-6473, -90, 142]] 
 ![![151, 0, 0], ![58, 1, 0], ![5, 0, 1]] where
  M :=![![![-6473, -90, 142], ![10172, -277, -128], ![-1704, 1526, -315]]]
  hmulB := by decide  
  f := ![![![-282583, -188342, -50854]], ![![-131206, -87449, -23612]], ![![-109029, -72668, -19621]]]
  g := ![![![-13, -90, 142], ![178, -277, -128], ![-587, 1526, -315]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 2, -1]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![4, 2, -1]] 
 ![![151, 0, 0], ![104, 1, 0], ![53, 0, 1]] where
  M :=![![![4, 2, -1], ![-73, -41, 5], ![109, 48, -38]]]
  hmulB := by decide  
  f := ![![![-1318, -28, 31]], ![![-893, -19, 21]], ![![-469, -10, 11]]]
  g := ![![![-1, 2, -1], ![26, -41, 5], ![-19, 48, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11286, 7522, 2031]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![11286, 7522, 2031]] 
 ![![151, 0, 0], ![140, 1, 0], ![6, 0, 1]] where
  M :=![![![11286, 7522, 2031], ![136679, 91097, 24597], ![601085, 400624, 108172]]]
  hmulB := by decide  
  f := ![![![-3844, -2440, 627]], ![![-3253, -2093, 537]], ![![-1163, -634, 166]]]
  g := ![![![-6980, 7522, 2031], ![-84533, 91097, 24597], ![-371757, 400624, 108172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-6473, -90, 142]] ![![4, 2, -1]]
  ![![-3844, -2440, 627]] where
 M := ![![![-3844, -2440, 627]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-3844, -2440, 627]] ![![11286, 7522, 2031]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10758, -7186, -1941]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-10758, -7186, -1941]] 
 ![![157, 0, 0], ![0, 157, 0], ![40, 82, 1]] where
  M :=![![![-10758, -7186, -1941], ![-130625, -87035, -23499], ![-574259, -382756, -103348]]]
  hmulB := by decide  
  f := ![![![-3248, -1724, 453]], ![![33887, 17955, -4719]], ![![16187, 8576, -2254]]]
  g := ![![![426, 968, -1941], ![5155, 11719, -23499], ![22673, 51540, -103348]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [127, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 156], [0, 1]]
 g := ![![[92, 68], [138], [111, 100], [21, 145], [110, 14], [117], [1]], ![[0, 89], [138], [105, 57], [28, 12], [128, 143], [117], [1]]]
 h' := ![![[91, 156], [48, 15], [33, 74], [2, 147], [3, 107], [14, 93], [30, 91], [0, 1]], ![[0, 1], [0, 142], [16, 83], [34, 10], [6, 50], [156, 64], [147, 66], [91, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [113, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [127, 66, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129299, 159190, 192704]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48273, -99634, 192704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3248, 1724, -453]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![3248, 1724, -453]] 
 ![![157, 0, 0], ![67, 1, 0], ![148, 0, 1]] where
  M :=![![![3248, 1724, -453], ![-33887, -17955, 4719], ![107455, 56918, -14960]]]
  hmulB := by decide  
  f := ![![![10758, 7186, 1941]], ![![5423, 3621, 978]], ![![13799, 9212, 2488]]]
  g := ![![![-288, 1724, -453], ![2998, -17955, 4719], ![-9503, 56918, -14960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-10758, -7186, -1941]] ![![3248, 1724, -453]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2745, 46, -62]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![2745, 46, -62]] 
 ![![163, 0, 0], ![0, 163, 0], ![53, 157, 1]] where
  M :=![![![2745, 46, -62], ![-4448, 33, 76], ![1220, -378, 63]]]
  hmulB := by decide  
  f := ![![![-189, -126, -34]], ![![-2288, -1525, -412]], ![![-2327, -1551, -419]]]
  g := ![![![37, 60, -62], ![-52, -73, 76], ![-13, -63, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [76, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 162], [0, 1]]
 g := ![![[123, 15], [], [], [46], [151], [0, 152], [1]], ![[83, 148], [], [], [46], [151], [138, 11], [1]]]
 h' := ![![[106, 162], [0, 34], [69], [45], [97, 32], [0, 92], [87, 106], [0, 1]], ![[0, 1], [18, 129], [69], [45], [66, 131], [135, 71], [76, 57], [106, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [143, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [76, 57, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2192, -84, 2296]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-760, -2212, 2296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -126, -34]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-189, -126, -34]] 
 ![![163, 0, 0], ![17, 1, 0], ![72, 0, 1]] where
  M :=![![![-189, -126, -34], ![-2288, -1525, -412], ![-10068, -6710, -1811]]]
  hmulB := by decide  
  f := ![![![2745, 46, -62]], ![![259, 5, -6]], ![![1220, 18, -27]]]
  g := ![![![27, -126, -34], ![327, -1525, -412], ![1438, -6710, -1811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![2745, 46, -62]] ![![-189, -126, -34]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [34, 5, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 41, 4], [149, 125, 163], [0, 1]]
 g := ![![[66, 98, 14], [79, 157, 130], [9, 2, 58], [53, 137], [5, 8], [93, 76, 1], []], ![[14, 147, 129, 112], [166, 12, 102, 6], [11, 64, 36, 27], [89, 132], [7, 44], [36, 143, 142, 42], [41, 16]], ![[85, 139, 15, 119], [126, 160, 22, 159], [114, 154, 100, 46], [115, 97], [82, 141], [135, 53, 31, 123], [49, 16]]]
 h' := ![![[94, 41, 4], [153, 61, 66], [28, 139, 111], [98, 158, 152], [118, 93, 114], [11, 124, 141], [0, 0, 1], [0, 1]], ![[149, 125, 163], [67, 40, 144], [148, 95, 69], [13, 122, 93], [37, 48, 93], [38, 1, 85], [94, 112, 125], [94, 41, 4]], ![[0, 1], [162, 66, 124], [33, 100, 154], [16, 54, 89], [98, 26, 127], [106, 42, 108], [161, 55, 41], [149, 125, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 155], []]
 b := ![[], [74, 121, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [34, 5, 91, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84001, -57114, -17535]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-503, -342, -105]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![194175, 129418, 34944]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![194175, 129418, 34944]] 
 ![![173, 0, 0], ![7, 1, 0], ![101, 0, 1]] where
  M :=![![![194175, 129418, 34944], ![2351606, 1567349, 423198], ![10341830, 6892846, 1861129]]]
  hmulB := by decide  
  f := ![![![-35513, -17702, 4692]], ![![591, 347, -90]], ![![-27103, -13704, 3625]]]
  g := ![![![-24515, 129418, 34944], ![-296895, 1567349, 423198], ![-1305677, 6892846, 1861129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2348, -48, 55]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-2348, -48, 55]] 
 ![![173, 0, 0], ![76, 1, 0], ![118, 0, 1]] where
  M :=![![![-2348, -48, 55], ![3953, 65, -89], ![-1593, 26, 24]]]
  hmulB := by decide  
  f := ![![![3874, 2582, 697]], ![![1973, 1315, 355]], ![![3835, 2556, 690]]]
  g := ![![![-30, -48, 55], ![55, 65, -89], ![-37, 26, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1028, -544, 143]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-1028, -544, 143]] 
 ![![173, 0, 0], ![90, 1, 0], ![40, 0, 1]] where
  M :=![![![-1028, -544, 143], ![10697, 5665, -1489], ![-33905, -17958, 4720]]]
  hmulB := by decide  
  f := ![![![-662, -314, -79]], ![![-375, -185, -47]], ![![-297, -168, -44]]]
  g := ![![![244, -544, 143], ![-2541, 5665, -1489], ![8055, -17958, 4720]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![194175, 129418, 34944]] ![![-2348, -48, 55]]
  ![![662, 314, 79]] where
 M := ![![![662, 314, 79]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![662, 314, 79]] ![![-1028, -544, 143]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-260, -150, 39]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-260, -150, 39]] 
 ![![179, 0, 0], ![0, 179, 0], ![53, 65, 1]] where
  M :=![![![-260, -150, 39], ![2919, 1567, -411], ![-9363, -4968, 1306]]]
  hmulB := by decide  
  f := ![![![26, 12, 3]], ![![201, 143, 39]], ![![86, 59, 16]]]
  g := ![![![-13, -15, 39], ![138, 158, -411], ![-439, -502, 1306]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [132, 71, 1] where
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
 g := ![![[48, 52], [87, 20], [47], [161], [3, 83], [38, 29], [1]], ![[115, 127], [99, 159], [47], [161], [17, 96], [127, 150], [1]]]
 h' := ![![[108, 178], [151, 125], [23, 60], [61, 88], [141, 124], [175, 158], [47, 108], [0, 1]], ![[0, 1], [47, 54], [59, 119], [78, 91], [108, 55], [55, 21], [76, 71], [108, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [163, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [132, 71, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10490, 7718, 2096]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-562, -718, 2096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -12, -3]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-26, -12, -3]] 
 ![![179, 0, 0], ![162, 1, 0], ![17, 0, 1]] where
  M :=![![![-26, -12, -3], ![-201, -143, -39], ![-951, -630, -170]]]
  hmulB := by decide  
  f := ![![![260, 150, -39]], ![![219, 127, -33]], ![![77, 42, -11]]]
  g := ![![![11, -12, -3], ![132, -143, -39], ![581, -630, -170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-260, -150, 39]] ![![-26, -12, -3]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4634, -2454, 645]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-4634, -2454, 645]] 
 ![![181, 0, 0], ![0, 181, 0], ![22, 125, 1]] where
  M :=![![![-4634, -2454, 645], ![48249, 25555, -6717], ![-152949, -81012, 21292]]]
  hmulB := by decide  
  f := ![![![-224, -12, 3]], ![![225, -83, -33]], ![![124, -61, -23]]]
  g := ![![![-104, -459, 645], ![1083, 4780, -6717], ![-3433, -15152, 21292]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [47, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 180], [0, 1]]
 g := ![![[], [15], [], [142], [0, 102], [], [1]], ![[], [15], [], [142], [0, 79], [], [1]]]
 h' := ![![[0, 180], [19], [0, 167], [23], [0, 93], [0, 37], [134], [0, 1]], ![[0, 1], [19], [0, 14], [23], [0, 88], [0, 144], [134], [0, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [0, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [47, 0, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1712, -776, 712]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -496, 712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![224, 12, -3]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![224, 12, -3]] 
 ![![181, 0, 0], ![167, 1, 0], ![171, 0, 1]] where
  M :=![![![224, 12, -3], ![-225, 83, 33], ![753, 402, 104]]]
  hmulB := by decide  
  f := ![![![4634, 2454, -645]], ![![4009, 2123, -558]], ![![5223, 2766, -727]]]
  g := ![![![-7, 12, -3], ![-109, 83, 33], ![-465, 402, 104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-4634, -2454, 645]] ![![224, 12, -3]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![511, 10, -12]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![511, 10, -12]] 
 ![![191, 0, 0], ![0, 191, 0], ![37, 31, 1]] where
  M :=![![![511, 10, -12], ![-862, -15, 18], ![314, -26, -7]]]
  hmulB := by decide  
  f := ![![![-3, -2, 0]], ![![2, -1, -6]], ![![-1, -1, -1]]]
  g := ![![![5, 2, -12], ![-8, -3, 18], ![3, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [9, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 190], [0, 1]]
 g := ![![[134, 85], [19, 100], [130, 90], [147, 34], [11, 5], [146, 162], [1]], ![[0, 106], [131, 91], [78, 101], [17, 157], [93, 186], [167, 29], [1]]]
 h' := ![![[131, 190], [20, 64], [167, 181], [14, 102], [92, 15], [23, 177], [182, 131], [0, 1]], ![[0, 1], [0, 127], [3, 10], [6, 89], [147, 176], [99, 14], [153, 60], [131, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [45, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [9, 60, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![228, 795, 1911]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-369, -306, 1911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -2, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-3, -2, 0]] 
 ![![191, 0, 0], ![97, 1, 0], ![79, 0, 1]] where
  M :=![![![-3, -2, 0], ![2, -1, -6], ![-142, -86, -5]]]
  hmulB := by decide  
  f := ![![![511, 10, -12]], ![![255, 5, -6]], ![![213, 4, -5]]]
  g := ![![![1, -2, 0], ![3, -1, -6], ![45, -86, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![511, 10, -12]] ![![-3, -2, 0]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7350, -3892, 1023]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-7350, -3892, 1023]] 
 ![![193, 0, 0], ![0, 193, 0], ![33, 66, 1]] where
  M :=![![![-7350, -3892, 1023], ![76525, 40531, -10653], ![-242573, -128482, 33770]]]
  hmulB := by decide  
  f := ![![![-68, 22, 9]], ![![617, 297, 75]], ![![209, 112, 29]]]
  g := ![![![-213, -370, 1023], ![2218, 3853, -10653], ![-7031, -12214, 33770]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [36, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 192], [0, 1]]
 g := ![![[78, 59], [3], [107], [54], [147], [36], [87, 1]], ![[0, 134], [3], [107], [54], [147], [36], [174, 192]]]
 h' := ![![[87, 192], [82, 161], [169, 179], [136, 53], [166, 61], [61, 95], [149, 6], [0, 1]], ![[0, 1], [0, 32], [109, 14], [115, 140], [69, 132], [27, 98], [92, 187], [87, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [107, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [36, 106, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![861, 950, 570]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-93, -190, 570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68, -22, -9]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![68, -22, -9]] 
 ![![193, 0, 0], ![187, 1, 0], ![50, 0, 1]] where
  M :=![![![68, -22, -9], ![-617, -297, -75], ![-1859, -1288, -350]]]
  hmulB := by decide  
  f := ![![![7350, 3892, -1023]], ![![6725, 3561, -936]], ![![3161, 1674, -440]]]
  g := ![![![24, -22, -9], ![304, -297, -75], ![1329, -1288, -350]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-7350, -3892, 1023]] ![![68, -22, -9]]
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


lemma PB201I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB201I3 : PrimesBelowBoundCertificateInterval O 137 193 201 where
  m := 11
  g := ![1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB201I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
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
      exact NI173N1
      exact NI173N2
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
  β := ![I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I173N0, I173N1, I173N2, I179N1, I181N1, I191N1, I193N1]
  Il := ![[], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [], [I173N0, I173N1, I173N2], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
