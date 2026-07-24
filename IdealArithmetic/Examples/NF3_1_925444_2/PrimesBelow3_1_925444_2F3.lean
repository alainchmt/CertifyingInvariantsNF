
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-57, -35, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-57, -35, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![82, 104, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-57, -35, 1], ![302, -95, -176], ![-8272, -1080, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -104, 139]], ![![-1, -1, 1], ![106, 131, -176], ![-66, -16, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [108, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 138], [0, 1]]
 g := ![![[55, 99], [24, 120], [79], [3, 34], [5], [118], [1]], ![[104, 40], [16, 19], [79], [10, 105], [5], [118], [1]]]
 h' := ![![[37, 138], [49, 88], [117, 113], [93, 94], [67, 112], [32, 127], [31, 37], [0, 1]], ![[0, 1], [108, 51], [128, 26], [96, 45], [41, 27], [5, 12], [10, 102], [37, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [26, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [108, 102, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3458, 1660, 310]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-158, -220, 310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![37, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![37, 1, 0]] 
 ![![139, 0, 0], ![37, 1, 0], ![128, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![37, 1, 0], ![-2, 39, 5], ![232, 32, 36]]]
  hmulB := by decide  
  f := ![![![25934, -522311, -66960], ![3197, 1861488, 0]], ![![6869, -139003, -17820], ![974, 495396, 0]], ![![23883, -480977, -61661], ![2939, 1714176, 0]]]
  g := ![![![1, 0, 0], ![-37, 139, 0], ![-128, 0, 139]], ![![0, 1, 0], ![-15, 39, 5], ![-40, 32, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-57, -35, 1]] ![![139, 0, 0], ![37, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5143, 139, 0]], ![![-7923, -4865, 139], ![-1807, -1390, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![37, 1, 0]]], ![![![-57, -35, 1]], ![![-13, -10, -1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![73, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![73, 1, 0]] 
 ![![149, 0, 0], ![73, 1, 0], ![37, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![73, 1, 0], ![-2, 75, 5], ![232, 32, 72]]]
  hmulB := by decide  
  f := ![![![2747, -113929, -7595], ![596, 226331, 0]], ![![1342, -55802, -3720], ![299, 110856, 0]], ![![616, -28292, -1886], ![283, 56203, 0]]]
  g := ![![![1, 0, 0], ![-73, 149, 0], ![-37, 0, 149]], ![![0, 1, 0], ![-38, 75, 5], ![-32, 32, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-38, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-38, 1, 0]] 
 ![![149, 0, 0], ![111, 1, 0], ![24, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-38, 1, 0], ![-2, -36, 5], ![232, 32, -39]]]
  hmulB := by decide  
  f := ![![![5141, 95260, -13230], ![-596, 394254, 0]], ![![3829, 70959, -9855], ![-446, 293679, 0]], ![![862, 15343, -2131], ![37, 63504, 0]]]
  g := ![![![1, 0, 0], ![-111, 149, 0], ![-24, 0, 149]], ![![-1, 1, 0], ![26, -36, 5], ![-16, 32, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-36, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-36, 1, 0]] 
 ![![149, 0, 0], ![113, 1, 0], ![23, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-36, 1, 0], ![-2, -34, 5], ![232, 32, -37]]]
  hmulB := by decide  
  f := ![![![26809, 469222, -69000], ![-3278, 2056200, 0]], ![![20355, 355826, -52325], ![-2383, 1559285, 0]], ![![4147, 72430, -10651], ![-470, 317400, 0]]]
  g := ![![![1, 0, 0], ![-113, 149, 0], ![-23, 0, 149]], ![![-1, 1, 0], ![25, -34, 5], ![-17, 32, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![73, 1, 0]] ![![149, 0, 0], ![-38, 1, 0]]
  ![![149, 0, 0], ![11, 67, 1]] where
 M := ![![![22201, 0, 0], ![-5662, 149, 0]], ![![10877, 149, 0], ![-2776, 37, 5]]]
 hmul := by decide  
 g := ![![![![138, -67, -1], ![149, 0, 0]], ![![-38, 1, 0], ![0, 0, 0]]], ![![![62, -66, -1], ![149, 0, 0]], ![![-19, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![11, 67, 1]] ![![149, 0, 0], ![-36, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-5364, 149, 0]], ![![1639, 9983, 149], ![-298, -2235, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-36, 1, 0]]], ![![![11, 67, 1]], ![![-2, -15, 2]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-29, -69, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-29, -69, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![122, 82, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-29, -69, 1], ![370, -135, -346], ![-16160, -2168, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -82, 151]], ![![-1, -1, 1], ![282, 187, -346], ![-166, -54, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [81, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 150], [0, 1]]
 g := ![![[99, 110], [11, 29], [97, 91], [49], [105, 36], [105], [1]], ![[0, 41], [0, 122], [0, 60], [49], [133, 115], [105], [1]]]
 h' := ![![[135, 150], [15, 67], [146, 28], [93, 53], [102, 144], [19, 6], [70, 135], [0, 1]], ![[0, 1], [0, 84], [0, 123], [0, 98], [63, 7], [74, 145], [24, 16], [135, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [18, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [81, 16, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10734, 7316, 4796]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3946, -2556, 4796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![44, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![44, 1, 0]] 
 ![![151, 0, 0], ![44, 1, 0], ![78, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![44, 1, 0], ![-2, 46, 5], ![232, 32, 43]]]
  hmulB := by decide  
  f := ![![![18557, -444009, -48260], ![2567, 1457452, 0]], ![![5404, -129357, -14060], ![756, 424612, 0]], ![![9570, -229356, -24929], ![1380, 752856, 0]]]
  g := ![![![1, 0, 0], ![-44, 151, 0], ![-78, 0, 151]], ![![0, 1, 0], ![-16, 46, 5], ![-30, 32, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-29, -69, 1]] ![![151, 0, 0], ![44, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![6644, 151, 0]], ![![-4379, -10419, 151], ![-906, -3171, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![44, 1, 0]]], ![![![-29, -69, 1]], ![![-6, -21, -2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![19, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![19, 1, 0]] 
 ![![157, 0, 0], ![19, 1, 0], ![14, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![19, 1, 0], ![-2, 21, 5], ![232, 32, 18]]]
  hmulB := by decide  
  f := ![![![1718, -18229, -4340], ![157, 136276, 0]], ![![191, -2206, -525], ![158, 16485, 0]], ![![144, -1626, -387], ![90, 12152, 0]]]
  g := ![![![1, 0, 0], ![-19, 157, 0], ![-14, 0, 157]], ![![0, 1, 0], ![-3, 21, 5], ![-4, 32, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![32, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![32, 1, 0]] 
 ![![157, 0, 0], ![32, 1, 0], ![96, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![32, 1, 0], ![-2, 34, 5], ![232, 32, 31]]]
  hmulB := by decide  
  f := ![![![-14431, 249704, 36720], ![-1256, -1153008, 0]], ![![-2960, 50865, 7480], ![-156, -234872, 0]], ![![-8832, 152685, 22453], ![-729, -705024, 0]]]
  g := ![![![1, 0, 0], ![-32, 157, 0], ![-96, 0, 157]], ![![0, 1, 0], ![-10, 34, 5], ![-24, 32, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-52, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-52, 1, 0]] 
 ![![157, 0, 0], ![105, 1, 0], ![139, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-52, 1, 0], ![-2, -50, 5], ![232, 32, -53]]]
  hmulB := by decide  
  f := ![![![151, 3750, -375], ![0, 11775, 0]], ![![101, 2500, -250], ![1, 7850, 0]], ![![137, 3320, -332], ![10, 10425, 0]]]
  g := ![![![1, 0, 0], ![-105, 157, 0], ![-139, 0, 157]], ![![-1, 1, 0], ![29, -50, 5], ![27, 32, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![19, 1, 0]] ![![157, 0, 0], ![32, 1, 0]]
  ![![157, 0, 0], ![27, 42, 1]] where
 M := ![![![24649, 0, 0], ![5024, 157, 0]], ![![2983, 157, 0], ![606, 53, 5]]]
 hmul := by decide  
 g := ![![![![130, -42, -1], ![157, 0, 0]], ![![5, -41, -1], ![157, 0, 0]]], ![![![-8, -41, -1], ![157, 0, 0]], ![![3, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![27, 42, 1]] ![![157, 0, 0], ![-52, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8164, 157, 0]], ![![4239, 6594, 157], ![-1256, -2041, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-52, 1, 0]]], ![![![27, 42, 1]], ![![-8, -13, 1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-14, -8, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-14, -8, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![149, 155, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-14, -8, 1], ![248, 2, -41], ![-2008, -216, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -155, 163]], ![![-1, -1, 1], ![39, 39, -41], ![-37, -27, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [159, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 162], [0, 1]]
 g := ![![[67, 84], [118, 104], [47], [33], [161], [24, 104], [1]], ![[85, 79], [117, 59], [47], [33], [161], [23, 59], [1]]]
 h' := ![![[105, 162], [146, 128], [6, 105], [12, 84], [80, 149], [96, 18], [4, 105], [0, 1]], ![[0, 1], [57, 35], [110, 58], [30, 79], [77, 14], [30, 145], [108, 58], [105, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [62, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [159, 58, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5867725, 3187564, 1275646]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1130083, -1193482, 1275646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![41, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![41, 1, 0]] 
 ![![163, 0, 0], ![41, 1, 0], ![136, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![41, 1, 0], ![-2, 43, 5], ![232, 32, 40]]]
  hmulB := by decide  
  f := ![![![-127, 2752, 320], ![0, -10432, 0]], ![![-32, 688, 80], ![1, -2608, 0]], ![![-112, 2296, 267], ![24, -8704, 0]]]
  g := ![![![1, 0, 0], ![-41, 163, 0], ![-136, 0, 163]], ![![0, 1, 0], ![-15, 43, 5], ![-40, 32, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-14, -8, 1]] ![![163, 0, 0], ![41, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![6683, 163, 0]], ![![-2282, -1304, 163], ![-326, -326, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![41, 1, 0]]], ![![![-14, -8, 1]], ![![-2, -2, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![20, -27, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![20, -27, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![20, 140, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![20, -27, 1], ![286, -2, -136], ![-6416, -824, 80]]]
  hmulB := by decide  
  f := ![![![-19, 27, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -140, 167]], ![![0, -1, 1], ![18, 114, -136], ![-48, -72, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [46, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 166], [0, 1]]
 g := ![![[52, 147], [143, 11], [166, 76], [14], [98], [142, 77], [1]], ![[130, 20], [50, 156], [70, 91], [14], [98], [159, 90], [1]]]
 h' := ![![[113, 166], [102, 67], [46, 126], [140, 57], [28, 101], [148, 91], [121, 113], [0, 1]], ![[0, 1], [158, 100], [89, 41], [68, 110], [85, 66], [77, 76], [31, 54], [113, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [116, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [46, 54, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4861, 7890, 3957]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-503, -3270, 3957]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-31, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-31, 1, 0]] 
 ![![167, 0, 0], ![136, 1, 0], ![87, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-31, 1, 0], ![-2, -29, 5], ![232, 32, -32]]]
  hmulB := by decide  
  f := ![![![-22525, -332934, 57400], ![2338, -1917160, 0]], ![![-18354, -271103, 46740], ![1838, -1561116, 0]], ![![-11724, -173445, 29903], ![1275, -998760, 0]]]
  g := ![![![1, 0, 0], ![-136, 167, 0], ![-87, 0, 167]], ![![-1, 1, 0], ![21, -29, 5], ![-8, 32, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![20, -27, 1]] ![![167, 0, 0], ![-31, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5177, 167, 0]], ![![3340, -4509, 167], ![-334, 835, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-31, 1, 0]]], ![![![20, -27, 1]], ![![-2, 5, -1]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [111, 114, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 11, 116], [66, 161, 57], [0, 1]]
 g := ![![[150, 74, 167], [119, 117], [164, 1, 163], [171, 3, 78], [38, 163], [116, 24, 1], []], ![[75, 82, 33, 24], [38, 1], [14, 11, 152, 95], [11, 46, 42, 37], [41, 106], [41, 37, 160, 96], [83, 135]], ![[142, 100, 107, 37], [31, 73], [36, 161, 163, 29], [87, 109, 165, 29], [51, 60], [131, 10, 87, 150], [142, 135]]]
 h' := ![![[131, 11, 116], [76, 76, 72], [134, 29, 64], [49, 28, 63], [47, 73, 50], [99, 28, 110], [0, 0, 1], [0, 1]], ![[66, 161, 57], [143, 139, 167], [6, 7, 1], [146, 109, 70], [114, 170, 83], [72, 161, 25], [163, 60, 161], [131, 11, 116]], ![[0, 1], [74, 131, 107], [48, 137, 108], [58, 36, 40], [102, 103, 40], [153, 157, 38], [12, 113, 11], [66, 161, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 124], []]
 b := ![[], [50, 163, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [111, 114, 149, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1740899, -281990, -44980]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10063, -1630, -260]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-108, 55, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-108, 55, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![71, 55, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-108, 55, 1], ![122, 34, 274], ![12608, 1800, -130]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -55, 179]], ![![-1, 0, 1], ![-108, -84, 274], ![122, 50, -130]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [104, 71, 1] where
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
 g := ![![[116, 74], [], [141], [42], [172, 48], [0, 29], [1]], ![[53, 105], [], [141], [42], [165, 131], [89, 150], [1]]]
 h' := ![![[108, 178], [0, 49], [7], [72, 118], [12, 159], [0, 103], [75, 108], [0, 1]], ![[0, 1], [101, 130], [7], [107, 61], [0, 20], [26, 76], [104, 71], [108, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [58, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [104, 71, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74490, 16889, 4909]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1531, -1414, 4909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![84, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![84, 1, 0]] 
 ![![179, 0, 0], ![84, 1, 0], ![130, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![84, 1, 0], ![-2, 86, 5], ![232, 32, 83]]]
  hmulB := by decide  
  f := ![![![3481, -167705, -9750], ![895, 349050, 0]], ![![1662, -78692, -4575], ![359, 163785, 0]], ![![2522, -121797, -7081], ![663, 253500, 0]]]
  g := ![![![1, 0, 0], ![-84, 179, 0], ![-130, 0, 179]], ![![0, 1, 0], ![-44, 86, 5], ![-74, 32, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-108, 55, 1]] ![![179, 0, 0], ![84, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15036, 179, 0]], ![![-19332, 9845, 179], ![-8950, 4654, 358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![84, 1, 0]]], ![![![-108, 55, 1]], ![![-50, 26, 2]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [117, 153, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 63, 94], [18, 117, 87], [0, 1]]
 g := ![![[20, 150, 73], [160, 178], [111, 25, 38], [71, 145], [49, 165, 178], [84, 31, 1], []], ![[86, 13, 4, 81], [133, 139], [19, 86, 89, 121], [9, 139], [137, 22, 139, 4], [58, 103, 15, 37], [142, 148]], ![[127, 105, 144, 15], [64, 48], [152, 90, 170, 79], [86, 87], [164, 61, 5, 27], [106, 137, 70, 136], [149, 148]]]
 h' := ![![[13, 63, 94], [138, 164, 142], [45, 103, 97], [61, 30, 20], [59, 6, 114], [127, 173, 97], [0, 0, 1], [0, 1]], ![[18, 117, 87], [170, 92, 174], [105, 111, 35], [66, 73, 92], [24, 139, 146], [11, 177, 99], [26, 63, 117], [13, 63, 94]], ![[0, 1], [98, 106, 46], [105, 148, 49], [149, 78, 69], [16, 36, 102], [180, 12, 166], [86, 118, 63], [18, 117, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 31], []]
 b := ![[], [176, 82, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [117, 153, 150, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4586721, -1038940, -169778]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25341, -5740, -938]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-22, -55, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-22, -55, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![169, 136, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-22, -55, 1], ![342, -100, -276], ![-12912, -1720, 66]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-169, -136, 191]], ![![-1, -1, 1], ![246, 196, -276], ![-126, -56, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [86, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 190], [0, 1]]
 g := ![![[164, 20], [183, 13], [140, 59], [6, 78], [59, 20], [66, 136], [1]], ![[0, 171], [0, 178], [0, 132], [54, 113], [86, 171], [135, 55], [1]]]
 h' := ![![[30, 190], [115, 28], [184, 83], [57, 170], [83, 101], [54, 163], [105, 30], [0, 1]], ![[0, 1], [0, 163], [0, 108], [0, 21], [57, 90], [169, 28], [50, 161], [30, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [178, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [86, 161, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7408, 8015, 4855]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4257, -3415, 4855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![85, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![85, 1, 0]] 
 ![![191, 0, 0], ![85, 1, 0], ![125, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![85, 1, 0], ![-2, 87, 5], ![232, 32, 84]]]
  hmulB := by decide  
  f := ![![![-2907, 133895, 7695], ![-382, -293949, 0]], ![![-1283, 59509, 3420], ![-190, -130644, 0]], ![![-1870, 87628, 5036], ![-323, -192375, 0]]]
  g := ![![![1, 0, 0], ![-85, 191, 0], ![-125, 0, 191]], ![![0, 1, 0], ![-42, 87, 5], ![-68, 32, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-22, -55, 1]] ![![191, 0, 0], ![85, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![16235, 191, 0]], ![![-4202, -10505, 191], ![-1528, -4775, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![85, 1, 0]]], ![![![-22, -55, 1]], ![![-8, -25, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![0, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![0, 1, 0]] 
 ![![193, 0, 0], ![0, 1, 0], ![154, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![0, 1, 0], ![-2, 2, 5], ![232, 32, -1]]]
  hmulB := by decide  
  f := ![![![-193, 193, 485], ![193, -18721, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-154, 154, 387], ![154, -14938, 0]]]
  g := ![![![1, 0, 0], ![0, 193, 0], ![-154, 0, 193]], ![![0, 1, 0], ![-4, 2, 5], ![2, 32, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![53, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![53, 1, 0]] 
 ![![193, 0, 0], ![53, 1, 0], ![150, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![53, 1, 0], ![-2, 55, 5], ![232, 32, 52]]]
  hmulB := by decide  
  f := ![![![-13243, 375878, 34170], ![-1544, -1318962, 0]], ![![-3646, 103182, 9380], ![-385, -362068, 0]], ![![-10301, 292133, 26557], ![-1169, -1025100, 0]]]
  g := ![![![1, 0, 0], ![-53, 193, 0], ![-150, 0, 193]], ![![0, 1, 0], ![-19, 55, 5], ![-48, 32, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-54, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-54, 1, 0]] 
 ![![193, 0, 0], ![139, 1, 0], ![17, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-54, 1, 0], ![-2, -52, 5], ![232, 32, -55]]]
  hmulB := by decide  
  f := ![![![4689, 126103, -12125], ![-579, 468025, 0]], ![![3385, 90794, -8730], ![-385, 336978, 0]], ![![441, 11107, -1068], ![49, 41225, 0]]]
  g := ![![![1, 0, 0], ![-139, 193, 0], ![-17, 0, 193]], ![![-1, 1, 0], ![37, -52, 5], ![-17, 32, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![0, 1, 0]] ![![193, 0, 0], ![53, 1, 0]]
  ![![193, 0, 0], ![-39, 11, 1]] where
 M := ![![![37249, 0, 0], ![10229, 193, 0]], ![![0, 193, 0], ![-2, 55, 5]]]
 hmul := by decide  
 g := ![![![![193, 0, 0], ![0, 0, 0]], ![![53, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-39, 11, 1]] ![![193, 0, 0], ![-54, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-10422, 193, 0]], ![![-7527, 2123, 193], ![2316, -579, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-54, 1, 0]]], ![![![-39, 11, 1]], ![![12, -3, 0]]]]
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


lemma PB273I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB273I3 : PrimesBelowBoundCertificateInterval O 137 193 273 where
  m := 11
  g := ![2, 3, 2, 3, 2, 2, 1, 2, 1, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB273I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
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
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
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
      exact NI149N1
      exact NI149N2
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
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I149N0, I149N1, I149N2, I151N1, I157N0, I157N1, I157N2, I163N1, I167N1, I179N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [I151N1], [I157N0, I157N1, I157N2], [I163N1], [I167N1], [], [I179N1], [], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
