
import IdealArithmetic.Examples.NF3_1_648324_3.RI3_1_648324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107598689, -3876241, -457110]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![107598689, -3876241, -457110]] 
 ![![139, 0, 0], ![0, 139, 0], ![28, 92, 1]] where
  M :=![![![107598689, -3876241, -457110], ![-194728860, 70572779, -7752482], ![-1651278666, -411339951, 70572779]]]
  hmulB := by decide  
  f := ![![![-12889291868881, -3320753269391, -448273464668]], ![![-190964495948568, -49199442506989, -6641506538782]], ![![-139167443829910, -35854626366769, -4840069791983]]]
  g := ![![![866171, 274661, -457110], ![160724, 5638857, -7752482], ![-26095802, -49669321, 70572779]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [136, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 138], [0, 1]]
 g := ![![[90, 46], [48, 6], [112], [121, 37], [16], [64], [1]], ![[0, 93], [0, 133], [112], [103, 102], [16], [64], [1]]]
 h' := ![![[131, 138], [5, 18], [55, 59], [85, 116], [0, 71], [62, 135], [3, 131], [0, 1]], ![[0, 1], [0, 121], [0, 80], [130, 23], [127, 68], [94, 4], [67, 8], [131, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [95, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [136, 8, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![988, 367, 75]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -47, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12889291868881, 3320753269391, 448273464668]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![12889291868881, 3320753269391, 448273464668]] 
 ![![139, 0, 0], ![94, 1, 0], ![30, 0, 1]] where
  M :=![![![12889291868881, 3320753269391, 448273464668], ![190964495948568, 49199442506989, 6641506538782], ![1414640892760566, 364463262794955, 49199442506989]]]
  hmulB := by decide  
  f := ![![![-107598689, 3876241, 457110]], ![![-71363654, 2113625, 364898]], ![![-11343036, 3795879, -409061]]]
  g := ![![![-2249710211467, 3320753269391, 448273464668], ![-33331138819222, 49199442506989, 6641506538782], ![-246912871116366, 364463262794955, 49199442506989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![107598689, -3876241, -457110]] ![![12889291868881, 3320753269391, 448273464668]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [140, 136, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 102, 64], [48, 46, 85], [0, 1]]
 g := ![![[98, 78, 68], [117, 80], [99, 120, 144], [42, 88], [9, 78, 130], [36, 1], []], ![[42, 29], [146, 16], [116, 114, 113, 145], [52, 36], [69, 140, 141, 64], [66, 30], [39, 73]], ![[48, 55, 60, 118], [41, 37], [93, 69, 101, 116], [132, 68], [141, 119, 51, 33], [101, 123], [18, 73]]]
 h' := ![![[137, 102, 64], [19, 117, 51], [146, 56, 123], [85, 62, 137], [81, 5, 45], [26, 30, 117], [0, 0, 1], [0, 1]], ![[48, 46, 85], [20, 90], [14, 58, 4], [106, 127, 138], [95, 95, 6], [67, 44, 1], [48, 57, 46], [137, 102, 64]], ![[0, 1], [132, 91, 98], [106, 35, 22], [140, 109, 23], [137, 49, 98], [34, 75, 31], [82, 92, 102], [48, 46, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 111], []]
 b := ![[], [90, 98, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [140, 136, 113, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17582, 695532, 240784]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![118, 4668, 1616]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3647251, -147599, 53156]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-3647251, -147599, 53156]] 
 ![![151, 0, 0], ![0, 151, 0], ![114, 133, 1]] where
  M :=![![![-3647251, -147599, 53156], ![22644456, 658385, -295198], ![-62877174, -633291, 658385]]]
  hmulB := by decide  
  f := ![![![-1632613057, -420620869, -56780242]], ![![-24188383092, -6231812659, -841241738]], ![![-23724220728, -6112227448, -825098751]]]
  g := ![![![-64285, -47797, 53156], ![372828, 264369, -295198], ![-913464, -584096, 658385]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [42, 59, 1] where
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
 g := ![![[5, 18], [65, 94], [59, 2], [19], [27, 2], [8], [1]], ![[0, 133], [106, 57], [92, 149], [19], [60, 149], [8], [1]]]
 h' := ![![[92, 150], [139, 138], [89, 68], [148, 46], [74, 64], [69, 105], [109, 92], [0, 1]], ![[0, 1], [0, 13], [3, 83], [1, 105], [73, 87], [65, 46], [117, 59], [92, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [124, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [42, 59, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-490, -18, 152]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -134, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1632613057, 420620869, 56780242]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![1632613057, 420620869, 56780242]] 
 ![![151, 0, 0], ![36, 1, 0], ![107, 0, 1]] where
  M :=![![![1632613057, 420620869, 56780242], ![24188383092, 6231812659, 841241738], ![179184490194, 46164481935, 6231812659]]]
  hmulB := by decide  
  f := ![![![3647251, 147599, -53156]], ![![719580, 30829, -10718]], ![![3000881, 108784, -42027]]]
  g := ![![![-129703471, 420620869, 56780242], ![-1921653898, 6231812659, 841241738], ![-14235369629, 46164481935, 6231812659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-3647251, -147599, 53156]] ![![1632613057, 420620869, 56780242]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![18, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![18, 1, 0]] 
 ![![157, 0, 0], ![18, 1, 0], ![152, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![18, 1, 0], ![0, 18, 2], ![426, 81, 18]]]
  hmulB := by decide  
  f := ![![![1477, 82, 0], ![-12874, 0, 0]], ![![162, 9, 0], ![-1412, 0, 0]], ![![1424, 70, -1], ![-12412, 79, 0]]]
  g := ![![![1, 0, 0], ![-18, 157, 0], ![-152, 0, 157]], ![![0, 1, 0], ![-4, 18, 2], ![-24, 81, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![53, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![53, 1, 0]] 
 ![![157, 0, 0], ![53, 1, 0], ![87, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![53, 1, 0], ![0, 53, 2], ![426, 81, 53]]]
  hmulB := by decide  
  f := ![![![2863, 54, 0], ![-8478, 0, 0]], ![![901, 17, 0], ![-2668, 0, 0]], ![![1573, 3, -1], ![-4658, 79, 0]]]
  g := ![![![1, 0, 0], ![-53, 157, 0], ![-87, 0, 157]], ![![0, 1, 0], ![-19, 53, 2], ![-54, 81, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-71, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-71, 1, 0]] 
 ![![157, 0, 0], ![86, 1, 0], ![70, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-71, 1, 0], ![0, -71, 2], ![426, 81, -71]]]
  hmulB := by decide  
  f := ![![![9870, -139, 0], ![21823, 0, 0]], ![![5468, -77, 0], ![12090, 0, 0]], ![![4454, -27, -1], ![9848, 79, 0]]]
  g := ![![![1, 0, 0], ![-86, 157, 0], ![-70, 0, 157]], ![![-1, 1, 0], ![38, -71, 2], ![-10, 81, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![18, 1, 0]] ![![157, 0, 0], ![53, 1, 0]]
  ![![157, 0, 0], ![6, -43, 1]] where
 M := ![![![24649, 0, 0], ![8321, 157, 0]], ![![2826, 157, 0], ![954, 71, 2]]]
 hmul := by decide  
 g := ![![![![151, 43, -1], ![157, 0, 0]], ![![47, 44, -1], ![157, 0, 0]]], ![![![12, 44, -1], ![157, 0, 0]], ![![6, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![6, -43, 1]] ![![157, 0, 0], ![-71, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-11147, 157, 0]], ![![942, -6751, 157], ![0, 3140, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-71, 1, 0]]], ![![![6, -43, 1]], ![![0, 20, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1717847, -144069, 35100]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-1717847, -144069, 35100]] 
 ![![163, 0, 0], ![48, 1, 0], ![152, 0, 1]] where
  M :=![![![-1717847, -144069, 35100], ![14952600, 1125253, -288138], ![-61373394, -4193289, 1125253]]]
  hmulB := by decide  
  f := ![![![57948408127, 14929630557, 2015373222]], ![![22331733636, 5753471815, 776669790]], ![![93056323022, 23974714209, 3236382631]]]
  g := ![![![-845, -144069, 35100], ![29064, 1125253, -288138], ![-191006, -4193289, 1125253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-32, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-32, 1, 0]] 
 ![![163, 0, 0], ![131, 1, 0], ![140, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-32, 1, 0], ![0, -32, 2], ![426, 81, -32]]]
  hmulB := by decide  
  f := ![![![3873, -121, 0], ![19723, 0, 0]], ![![3137, -98, 0], ![15975, 0, 0]], ![![3332, -88, -1], ![16968, 82, 0]]]
  g := ![![![1, 0, 0], ![-131, 163, 0], ![-140, 0, 163]], ![![-1, 1, 0], ![24, -32, 2], ![-35, 81, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-16, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-16, 1, 0]] 
 ![![163, 0, 0], ![147, 1, 0], ![35, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-16, 1, 0], ![0, -16, 2], ![426, 81, -16]]]
  hmulB := by decide  
  f := ![![![945, -59, 0], ![9617, 0, 0]], ![![865, -54, 0], ![8803, 0, 0]], ![![209, -5, -1], ![2127, 82, 0]]]
  g := ![![![1, 0, 0], ![-147, 163, 0], ![-35, 0, 163]], ![![-1, 1, 0], ![14, -16, 2], ![-67, 81, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-1717847, -144069, 35100]] ![![163, 0, 0], ![-32, 1, 0]]
  ![![163, 0, 0], ![-116, 8, 1]] where
 M := ![![![-280009061, -23483247, 5721300], ![69923704, 5735461, -1411338]]]
 hmul := by decide  
 g := ![![![![-1144459, -183613, 30157], ![805709, 0, 0]], ![![285892, 45055, -7425], ![-201063, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-116, 8, 1]] ![![163, 0, 0], ![-16, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-2608, 163, 0]], ![![-18908, 1304, 163], ![2282, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-16, 1, 0]]], ![![![-116, 8, 1]], ![![14, -1, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![167, 0, 0], ![5, 1, 0], ![71, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 2], ![426, 81, 5]]]
  hmulB := by decide  
  f := ![![![-137, -5, 2]], ![![1, 0, 0]], ![![-71, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 5, 2], ![-2, 81, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![42, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![42, 1, 0]] 
 ![![167, 0, 0], ![42, 1, 0], ![120, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![42, 1, 0], ![0, 42, 2], ![426, 81, 42]]]
  hmulB := by decide  
  f := ![![![85, 2, 0], ![-334, 0, 0]], ![![-42, -1, 0], ![168, 0, 0]], ![![48, -20, -1], ![-188, 84, 0]]]
  g := ![![![1, 0, 0], ![-42, 167, 0], ![-120, 0, 167]], ![![0, 1, 0], ![-12, 42, 2], ![-48, 81, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-47, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-47, 1, 0]] 
 ![![167, 0, 0], ![120, 1, 0], ![148, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-47, 1, 0], ![0, -47, 2], ![426, 81, -47]]]
  hmulB := by decide  
  f := ![![![2163, -46, 0], ![7682, 0, 0]], ![![1552, -33, 0], ![5512, 0, 0]], ![![1958, -18, -1], ![6954, 84, 0]]]
  g := ![![![1, 0, 0], ![-120, 167, 0], ![-148, 0, 167]], ![![-1, 1, 0], ![32, -47, 2], ![-14, 81, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![167, 0, 0], ![42, 1, 0]]
  ![![167, 0, 0], ![-62, -60, 1]] where
 M := ![![![835, 167, 0], ![210, 47, 2]]]
 hmul := by decide  
 g := ![![![![5, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-62, -60, 1]] ![![167, 0, 0], ![-47, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-7849, 167, 0]], ![![-10354, -10020, 167], ![3340, 2839, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-47, 1, 0]]], ![![![-62, -60, 1]], ![![20, 17, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-64, 21, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-64, 21, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![109, 21, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-64, 21, 1], ![426, 17, 42], ![8946, 1914, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -21, 173]], ![![-1, 0, 1], ![-24, -5, 42], ![41, 9, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [170, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 172], [0, 1]]
 g := ![![[130, 142], [78], [54, 60], [148, 89], [121], [159, 33], [1]], ![[150, 31], [78], [99, 113], [85, 84], [121], [54, 140], [1]]]
 h' := ![![[44, 172], [9, 83], [162, 50], [98, 38], [51, 75], [131, 11], [3, 44], [0, 1]], ![[0, 1], [28, 90], [113, 123], [40, 135], [64, 98], [96, 162], [36, 129], [44, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [124, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [170, 129, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2256, 1562, 338]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-226, -32, 338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-42, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-42, 1, 0]] 
 ![![173, 0, 0], ![131, 1, 0], ![156, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-42, 1, 0], ![0, -42, 2], ![426, 81, -42]]]
  hmulB := by decide  
  f := ![![![5167, -123, 0], ![21279, 0, 0]], ![![3949, -94, 0], ![16263, 0, 0]], ![![4668, -90, -1], ![19224, 87, 0]]]
  g := ![![![1, 0, 0], ![-131, 173, 0], ![-156, 0, 173]], ![![-1, 1, 0], ![30, -42, 2], ![-21, 81, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-64, 21, 1]] ![![173, 0, 0], ![-42, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-7266, 173, 0]], ![![-11072, 3633, 173], ![3114, -865, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-42, 1, 0]]], ![![![-64, 21, 1]], ![![18, -5, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [162, 109, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 151, 131], [89, 27, 48], [0, 1]]
 g := ![![[80, 178, 125], [89, 126, 48], [40, 60], [38, 144], [123, 98, 125], [1, 17, 1], []], ![[123, 36, 137, 58], [178, 154, 125, 33], [171, 47], [130, 61], [5, 25, 58, 113], [130, 28, 60, 92], [149, 156]], ![[122, 89, 142, 14], [50, 59, 128, 16], [139, 88], [12, 151], [77, 157, 62, 88], [1, 53, 13, 42], [53, 156]]]
 h' := ![![[107, 151, 131], [81, 130, 29], [23, 54, 103], [136, 177, 66], [122, 4, 12], [17, 1, 150], [0, 0, 1], [0, 1]], ![[89, 27, 48], [72, 58, 92], [164, 49, 10], [168, 90, 88], [74, 122, 132], [81, 33, 64], [20, 109, 27], [107, 151, 131]], ![[0, 1], [63, 170, 58], [58, 76, 66], [102, 91, 25], [16, 53, 35], [59, 145, 144], [51, 70, 151], [89, 27, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147, 139], []]
 b := ![[], [15, 37, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [162, 109, 162, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56922, 5012, 5012]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-318, 28, 28]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-99, -57, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-99, -57, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![82, 124, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-99, -57, 1], ![426, -18, -114], ![-24282, -4404, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -124, 181]], ![![-1, -1, 1], ![54, 78, -114], ![-126, -12, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [89, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 180], [0, 1]]
 g := ![![[57, 161], [106], [88, 73], [161], [120, 101], [41, 25], [1]], ![[157, 20], [106], [85, 108], [161], [158, 80], [97, 156], [1]]]
 h' := ![![[176, 180], [26, 121], [132, 58], [152, 39], [180, 121], [152, 61], [92, 176], [0, 1]], ![[0, 1], [145, 60], [23, 123], [138, 142], [118, 60], [28, 120], [117, 5], [176, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [175, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [89, 5, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16283, 3424, 810]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-277, -536, 810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-67, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-67, 1, 0]] 
 ![![181, 0, 0], ![114, 1, 0], ![18, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-67, 1, 0], ![0, -67, 2], ![426, 81, -67]]]
  hmulB := by decide  
  f := ![![![11391, -170, 0], ![30770, 0, 0]], ![![7170, -107, 0], ![19368, 0, 0]], ![![1252, 15, -1], ![3382, 91, 0]]]
  g := ![![![1, 0, 0], ![-114, 181, 0], ![-18, 0, 181]], ![![-1, 1, 0], ![42, -67, 2], ![-42, 81, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-99, -57, 1]] ![![181, 0, 0], ![-67, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-12127, 181, 0]], ![![-17919, -10317, 181], ![7059, 3801, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-67, 1, 0]]], ![![![-99, -57, 1]], ![![39, 21, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [48, 96, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 64, 13], [59, 126, 178], [0, 1]]
 g := ![![[132, 182, 26], [158, 190, 4], [58, 56, 158], [41, 4, 40], [184, 66, 125], [7, 26, 1], []], ![[162, 141, 45, 107], [135, 9, 74, 90], [136, 169, 58, 117], [153, 48, 66, 36], [128, 73, 128, 118], [119, 15, 96, 108], [137, 169]], ![[46, 81, 125, 157], [182, 88, 177, 106], [170, 170, 20, 176], [7, 65, 153, 131], [51, 84, 142, 29], [133, 15, 25, 41], [163, 169]]]
 h' := ![![[158, 64, 13], [56, 36, 147], [81, 74, 189], [133, 89, 106], [145, 2, 123], [46, 181, 121], [0, 0, 1], [0, 1]], ![[59, 126, 178], [18, 123, 81], [18, 131, 137], [34, 124, 188], [172, 178, 53], [174, 153, 27], [52, 106, 126], [158, 64, 13]], ![[0, 1], [171, 32, 154], [145, 177, 56], [179, 169, 88], [110, 11, 15], [158, 48, 43], [50, 85, 64], [59, 126, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121, 128], []]
 b := ![[], [66, 178, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [48, 96, 165, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171136, -27504, 9168]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-896, -144, 48]
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

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1848481, -246118, 50066]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-1848481, -246118, 50066]] 
 ![![193, 0, 0], ![0, 193, 0], ![62, 19, 1]] where
  M :=![![![-1848481, -246118, 50066], ![21328116, 2206865, -492236], ![-104846268, -9271500, 2206865]]]
  hmulB := by decide  
  f := ![![![-1588015825, -409130990, -55229206]], ![![-23527641756, -6061581511, -818261980]], ![![-3729388478, -960826949, -129703471]]]
  g := ![![![-25661, -6204, 50066], ![268636, 59893, -492236], ![-1252186, -265295, 2206865]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [173, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 192], [0, 1]]
 g := ![![[], [], [], [], [], [14], [0, 1]], ![[], [], [], [], [], [14], [0, 192]]]
 h' := ![![[0, 192], [112], [150], [27], [42], [87], [0, 20], [0, 1]], ![[0, 1], [112], [150], [27], [42], [87], [0, 173], [0, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164]]
 b := ![[], [0, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [173, 0, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1877, 1176, 326]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95, -26, 326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1588015825, 409130990, 55229206]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![1588015825, 409130990, 55229206]] 
 ![![193, 0, 0], ![155, 1, 0], ![50, 0, 1]] where
  M :=![![![1588015825, 409130990, 55229206], ![23527641756, 6061581511, 818261980], ![174289801740, 44903431068, 6061581511]]]
  hmulB := by decide  
  f := ![![![1848481, 246118, -50066]], ![![1374023, 186225, -37658]], ![![1022126, 111800, -24405]]]
  g := ![![![-334656725, 409130990, 55229206], ![-4958189593, 6061581511, 818261980], ![-36729642950, 44903431068, 6061581511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-1848481, -246118, 50066]] ![![1588015825, 409130990, 55229206]]
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


lemma PB228I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB228I3 : PrimesBelowBoundCertificateInterval O 137 193 228 where
  m := 11
  g := ![2, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB228I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![157, 157, 157]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
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
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I157N0, I157N1, I157N2, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N1, I181N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N0, I157N1, I157N2], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N1], [], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
