
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-69, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-69, 1, 0]] 
 ![![139, 0, 0], ![70, 1, 0], ![52, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-69, 1, 0], ![0, -69, 2], ![710, 117, -69]]]
  hmulB := by decide  
  f := ![![![9592, -139, 0], ![19321, 0, 0]], ![![4900, -71, 0], ![9870, 0, 0]], ![![3640, -18, -1], ![7332, 70, 0]]]
  g := ![![![1, 0, 0], ![-70, 139, 0], ![-52, 0, 139]], ![![-1, 1, 0], ![34, -69, 2], ![-28, 117, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-62, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-62, 1, 0]] 
 ![![139, 0, 0], ![77, 1, 0], ![24, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-62, 1, 0], ![0, -62, 2], ![710, 117, -62]]]
  hmulB := by decide  
  f := ![![![6201, -100, 0], ![13900, 0, 0]], ![![3535, -57, 0], ![7924, 0, 0]], ![![1068, 14, -1], ![2394, 70, 0]]]
  g := ![![![1, 0, 0], ![-77, 139, 0], ![-24, 0, 139]], ![![-1, 1, 0], ![34, -62, 2], ![-49, 117, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-8, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-8, 1, 0]] 
 ![![139, 0, 0], ![131, 1, 0], ![107, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-8, 1, 0], ![0, -8, 2], ![710, 117, -8]]]
  hmulB := by decide  
  f := ![![![729, -91, 0], ![12649, 0, 0]], ![![689, -86, 0], ![11955, 0, 0]], ![![569, -67, -1], ![9873, 70, 0]]]
  g := ![![![1, 0, 0], ![-131, 139, 0], ![-107, 0, 139]], ![![-1, 1, 0], ![6, -8, 2], ![-99, 117, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-69, 1, 0]] ![![139, 0, 0], ![-62, 1, 0]]
  ![![139, 0, 0], ![-85, 4, 1]] where
 M := ![![![19321, 0, 0], ![-8618, 139, 0]], ![![-9591, 139, 0], ![4278, -131, 2]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![23, -3, -1], ![139, 0, 0]]], ![![![16, -3, -1], ![139, 0, 0]], ![![32, -1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-85, 4, 1]] ![![139, 0, 0], ![-8, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-1112, 139, 0]], ![![-11815, 556, 139], ![1390, 0, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-8, 1, 0]]], ![![![-85, 4, 1]], ![![10, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-38, -76, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-38, -76, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![111, 73, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-38, -76, 1], ![710, 79, -152], ![-53960, -8537, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -73, 149]], ![![-1, -1, 1], ![118, 75, -152], ![-421, -96, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [62, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 148], [0, 1]]
 g := ![![[41, 54], [121], [129, 95], [37], [41, 24], [81], [1]], ![[2, 95], [121], [19, 54], [37], [123, 125], [81], [1]]]
 h' := ![![[140, 148], [17, 90], [48, 138], [22, 63], [140, 127], [14, 89], [87, 140], [0, 1]], ![[0, 1], [101, 59], [147, 11], [51, 86], [40, 22], [107, 60], [19, 9], [140, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [75, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [62, 9, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1482, 580, 110]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, -50, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![3, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![3, 1, 0]] 
 ![![149, 0, 0], ![3, 1, 0], ![70, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![3, 1, 0], ![0, 3, 2], ![710, 117, 3]]]
  hmulB := by decide  
  f := ![![![145, 48, 0], ![-7152, 0, 0]], ![![-3, -1, 0], ![150, 0, 0]], ![![68, 21, -1], ![-3354, 75, 0]]]
  g := ![![![1, 0, 0], ![-3, 149, 0], ![-70, 0, 149]], ![![0, 1, 0], ![-1, 3, 2], ![1, 117, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-38, -76, 1]] ![![149, 0, 0], ![3, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![447, 149, 0]], ![![-5662, -11324, 149], ![596, -149, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![3, 1, 0]]], ![![![-38, -76, 1]], ![![4, -1, -1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![52, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![52, 1, 0]] 
 ![![151, 0, 0], ![52, 1, 0], ![7, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![52, 1, 0], ![0, 52, 2], ![710, 117, 52]]]
  hmulB := by decide  
  f := ![![![2341, 45, 0], ![-6795, 0, 0]], ![![780, 15, 0], ![-2264, 0, 0]], ![![61, -25, -1], ![-177, 76, 0]]]
  g := ![![![1, 0, 0], ![-52, 151, 0], ![-7, 0, 151]], ![![0, 1, 0], ![-18, 52, 2], ![-38, 117, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-39, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-39, 1, 0]] 
 ![![151, 0, 0], ![112, 1, 0], ![70, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-39, 1, 0], ![0, -39, 2], ![710, 117, -39]]]
  hmulB := by decide  
  f := ![![![1678, -43, 0], ![6493, 0, 0]], ![![1288, -33, 0], ![4984, 0, 0]], ![![844, -2, -1], ![3266, 76, 0]]]
  g := ![![![1, 0, 0], ![-112, 151, 0], ![-70, 0, 151]], ![![-1, 1, 0], ![28, -39, 2], ![-64, 117, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27919, 1420, -338]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![27919, 1420, -338]] 
 ![![151, 0, 0], ![138, 1, 0], ![142, 0, 1]] where
  M :=![![![27919, 1420, -338], ![-239980, -11627, 2840], ![1008200, 46150, -11627]]]
  hmulB := by decide  
  f := ![![![4121129, 911640, 102874]], ![![4250042, 940157, 106092]], ![![8162018, 1805530, 203745]]]
  g := ![![![-795, 1420, -338], ![6366, -11627, 2840], ![-24566, 46150, -11627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![52, 1, 0]] ![![151, 0, 0], ![-39, 1, 0]]
  ![![-4121129, -911640, -102874]] where
 M := ![![![22801, 0, 0], ![-5889, 151, 0]], ![![7852, 151, 0], ![-2028, 13, 2]]]
 hmul := by decide  
 g := ![![![![-4215769, -214420, 51038]], ![![1328821, 67007, -16022]]], ![![![-1211808, -62213, 14736]], ![![382272, 19461, -4630]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-4121129, -911640, -102874]] ![![27919, 1420, -338]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![582873, 128938, 14550]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![582873, 128938, 14550]] 
 ![![157, 0, 0], ![0, 157, 0], ![106, 70, 1]] where
  M :=![![![582873, 128938, 14550], ![10330500, 2285223, 257876], ![91545980, 20250996, 2285223]]]
  hmulB := by decide  
  f := ![![![-10731, -582, 134]], ![![95140, 4947, -1164]], ![![32542, 1682, -397]]]
  g := ![![![-6111, -5666, 14550], ![-108308, -100421, 257876], ![-959794, -889902, 2285223]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [102, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [154, 156], [0, 1]]
 g := ![![[97, 76], [153], [155, 124], [90, 100], [81, 122], [9], [1]], ![[26, 81], [153], [97, 33], [104, 57], [29, 35], [9], [1]]]
 h' := ![![[154, 156], [105, 95], [47, 56], [83, 76], [59, 147], [66, 114], [55, 154], [0, 1]], ![[0, 1], [134, 62], [36, 101], [12, 81], [89, 10], [38, 43], [64, 3], [154, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [85, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [102, 3, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8420, 1789, 1064]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-772, -463, 1064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10731, -582, 134]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-10731, -582, 134]] 
 ![![157, 0, 0], ![17, 1, 0], ![91, 0, 1]] where
  M :=![![![-10731, -582, 134], ![95140, 4947, -1164], ![-413220, -20524, 4947]]]
  hmulB := by decide  
  f := ![![![582873, 128938, 14550]], ![![128913, 28517, 3218]], ![![920939, 203722, 22989]]]
  g := ![![![-83, -582, 134], ![745, 4947, -1164], ![-3277, -20524, 4947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![582873, 128938, 14550]] ![![-10731, -582, 134]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-99, 3, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-99, 3, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![64, 3, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-99, 3, 1], ![710, 18, 6], ![2130, 706, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -3, 163]], ![![-1, 0, 1], ![2, 0, 6], ![6, 4, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [92, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 162], [0, 1]]
 g := ![![[142, 54], [115, 135], [36], [77], [64], [46, 87], [1]], ![[150, 109], [135, 28], [36], [77], [64], [77, 76], [1]]]
 h' := ![![[139, 162], [15, 124], [109, 61], [18, 157], [16, 27], [6, 8], [71, 139], [0, 1]], ![[0, 1], [136, 39], [112, 102], [162, 6], [20, 136], [140, 155], [158, 24], [139, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [119, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [92, 24, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1232, 17, 223]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80, -4, 223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-6, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-6, 1, 0]] 
 ![![163, 0, 0], ![157, 1, 0], ![145, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-6, 1, 0], ![0, -6, 2], ![710, 117, -6]]]
  hmulB := by decide  
  f := ![![![829, -138, 0], ![22494, 0, 0]], ![![799, -133, 0], ![21680, 0, 0]], ![![739, -120, -1], ![20052, 82, 0]]]
  g := ![![![1, 0, 0], ![-157, 163, 0], ![-145, 0, 163]], ![![-1, 1, 0], ![4, -6, 2], ![-103, 117, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-99, 3, 1]] ![![163, 0, 0], ![-6, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-978, 163, 0]], ![![-16137, 489, 163], ![1304, 0, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-6, 1, 0]]], ![![![-99, 3, 1]], ![![8, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [88, 34, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 34, 73], [93, 132, 94], [0, 1]]
 g := ![![[9, 19, 2], [80, 108, 98], [19, 6, 22], [111, 58], [6, 63], [92, 136, 1], []], ![[45, 68, 39, 43], [108, 83, 72, 37], [140, 38, 33, 41], [55, 96], [137, 57], [76, 24, 129, 80], [85, 152]], ![[18, 8, 100, 57], [82, 161, 32, 33], [162, 87, 61, 18], [35, 14], [60, 107], [87, 122, 101, 114], [64, 152]]]
 h' := ![![[43, 34, 73], [141, 138, 13], [165, 102, 76], [146, 136, 32], [27, 136, 15], [87, 101, 118], [0, 0, 1], [0, 1]], ![[93, 132, 94], [6, 83, 100], [107, 160, 110], [150, 23, 124], [67, 51, 51], [123, 47, 70], [47, 18, 132], [43, 34, 73]], ![[0, 1], [92, 113, 54], [133, 72, 148], [120, 8, 11], [148, 147, 101], [90, 19, 146], [11, 149, 34], [93, 132, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 93], []]
 b := ![[], [120, 29, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [88, 34, 31, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4705726, -1794582, -316966]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28178, -10746, -1898]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-48, -11, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-48, -11, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![125, 162, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-48, -11, 1], ![710, 69, -22], ![-7810, -932, 69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -162, 173]], ![![-1, -1, 1], ![20, 21, -22], ![-95, -70, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [114, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 172], [0, 1]]
 g := ![![[76, 121], [35], [86, 117], [121, 169], [78], [102, 23], [1]], ![[112, 52], [35], [5, 56], [4, 4], [78], [126, 150], [1]]]
 h' := ![![[159, 172], [124, 162], [57, 30], [46, 109], [89, 13], [136, 123], [59, 159], [0, 1]], ![[0, 1], [105, 11], [156, 143], [77, 64], [80, 160], [144, 50], [82, 14], [159, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [28, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [114, 14, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1534, 575, 105]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67, -95, 105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![22, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![22, 1, 0]] 
 ![![173, 0, 0], ![22, 1, 0], ![104, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![22, 1, 0], ![0, 22, 2], ![710, 117, 22]]]
  hmulB := by decide  
  f := ![![![2113, 96, 0], ![-16608, 0, 0]], ![![242, 11, 0], ![-1902, 0, 0]], ![![1256, 46, -1], ![-9872, 87, 0]]]
  g := ![![![1, 0, 0], ![-22, 173, 0], ![-104, 0, 173]], ![![0, 1, 0], ![-4, 22, 2], ![-24, 117, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-48, -11, 1]] ![![173, 0, 0], ![22, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![3806, 173, 0]], ![![-8304, -1903, 173], ![-346, -173, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![22, 1, 0]]], ![![![-48, -11, 1]], ![![-2, -1, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-4, -44, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-4, -44, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![175, 135, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-4, -44, 1], ![710, 113, -88], ![-31240, -4793, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-175, -135, 179]], ![![-1, -1, 1], ![90, 67, -88], ![-285, -112, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [110, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 178], [0, 1]]
 g := ![![[122, 83], [123, 47], [117], [52], [], [99, 25], [1]], ![[0, 96], [0, 132], [117], [52], [], [45, 154], [1]]]
 h' := ![![[5, 178], [74, 21], [82, 91], [8, 81], [0, 125], [29], [69, 5], [0, 1]], ![[0, 1], [0, 158], [0, 88], [55, 98], [88, 54], [29], [94, 174], [5, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [69, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [110, 174, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27265, 8145, 1015]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-840, -720, 1015]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![88, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![88, 1, 0]] 
 ![![179, 0, 0], ![88, 1, 0], ![66, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![88, 1, 0], ![0, 88, 2], ![710, 117, 88]]]
  hmulB := by decide  
  f := ![![![3785, 43, 0], ![-7697, 0, 0]], ![![1848, 21, 0], ![-3758, 0, 0]], ![![1254, -30, -1], ![-2550, 90, 0]]]
  g := ![![![1, 0, 0], ![-88, 179, 0], ![-66, 0, 179]], ![![0, 1, 0], ![-44, 88, 2], ![-86, 117, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-4, -44, 1]] ![![179, 0, 0], ![88, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15752, 179, 0]], ![![-716, -7876, 179], ![358, -3759, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![88, 1, 0]]], ![![![-4, -44, 1]], ![![2, -21, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![54, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![54, 1, 0]] 
 ![![181, 0, 0], ![54, 1, 0], ![171, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![54, 1, 0], ![0, 54, 2], ![710, 117, 54]]]
  hmulB := by decide  
  f := ![![![2539, 47, 0], ![-8507, 0, 0]], ![![702, 13, 0], ![-2352, 0, 0]], ![![2385, 17, -1], ![-7991, 91, 0]]]
  g := ![![![1, 0, 0], ![-54, 181, 0], ![-171, 0, 181]], ![![0, 1, 0], ![-18, 54, 2], ![-82, 117, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6971, 1060, -164]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![6971, 1060, -164]] 
 ![![181, 0, 0], ![134, 1, 0], ![72, 0, 1]] where
  M :=![![![6971, 1060, -164], ![-116440, -12217, 2120], ![752600, 65800, -12217]]]
  hmulB := by decide  
  f := ![![![-9759089, -2158820, -243612]], ![![-8180566, -1809633, -204208]], ![![-12350368, -2732040, -308297]]]
  g := ![![![-681, 1060, -164], ![7558, -12217, 2120], ![-39696, 65800, -12217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-7, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-7, 1, 0]] 
 ![![181, 0, 0], ![174, 1, 0], ![66, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-7, 1, 0], ![0, -7, 2], ![710, 117, -7]]]
  hmulB := by decide  
  f := ![![![197, -28, 0], ![5068, 0, 0]], ![![190, -27, 0], ![4888, 0, 0]], ![![74, -7, -1], ![1904, 91, 0]]]
  g := ![![![1, 0, 0], ![-174, 181, 0], ![-66, 0, 181]], ![![-1, 1, 0], ![6, -7, 2], ![-106, 117, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![54, 1, 0]] ![![6971, 1060, -164]]
  ![![181, 0, 0], ![-2, -87, 1]] where
 M := ![![![1261751, 191860, -29684]], ![![259994, 45023, -6736]]]
 hmul := by decide  
 g := ![![![![6967, 886, -162], ![-362, 0, 0]]], ![![![1436, 230, -37], ![-39, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-2, -87, 1]] ![![181, 0, 0], ![-7, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-1267, 181, 0]], ![![-362, -15747, 181], ![724, 724, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-7, 1, 0]]], ![![![-2, -87, 1]], ![![4, 4, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-109, 2, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-109, 2, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![82, 2, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-109, 2, 1], ![710, 8, 4], ![1420, 589, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -2, 191]], ![![-1, 0, 1], ![2, 0, 4], ![4, 3, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [64, 49, 1] where
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
 g := ![![[147, 3], [90, 72], [150, 120], [183, 130], [102, 34], [167, 109], [1]], ![[0, 188], [0, 119], [0, 71], [116, 61], [155, 157], [174, 82], [1]]]
 h' := ![![[142, 190], [161, 167], [141, 151], [130, 104], [157, 148], [8, 15], [127, 142], [0, 1]], ![[0, 1], [0, 24], [0, 40], [0, 87], [163, 43], [37, 176], [45, 49], [142, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [64, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [64, 49, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4244, -206, 88]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -2, 88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-4, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-4, 1, 0]] 
 ![![191, 0, 0], ![187, 1, 0], ![183, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-4, 1, 0], ![0, -4, 2], ![710, 117, -4]]]
  hmulB := by decide  
  f := ![![![201, -50, 0], ![9550, 0, 0]], ![![197, -49, 0], ![9360, 0, 0]], ![![193, -46, -1], ![9170, 96, 0]]]
  g := ![![![1, 0, 0], ![-187, 191, 0], ![-183, 0, 191]], ![![-1, 1, 0], ![2, -4, 2], ![-107, 117, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-109, 2, 1]] ![![191, 0, 0], ![-4, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-764, 191, 0]], ![![-20819, 382, 191], ![1146, 0, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-4, 1, 0]]], ![![![-109, 2, 1]], ![![6, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-86, 43, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-86, 43, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![107, 43, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-86, 43, 1], ![710, 31, 86], ![30530, 5386, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -43, 193]], ![![-1, 0, 1], ![-44, -19, 86], ![141, 21, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [7, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 192], [0, 1]]
 g := ![![[37, 138], [189], [46], [124], [124], [187], [127, 1]], ![[0, 55], [189], [46], [124], [124], [187], [61, 192]]]
 h' := ![![[127, 192], [60, 36], [15, 31], [12, 168], [109, 33], [28, 33], [76, 103], [0, 1]], ![[0, 1], [0, 157], [92, 162], [118, 25], [54, 160], [166, 160], [33, 90], [127, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [131, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [7, 66, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2847, 1954, 602]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-319, -124, 602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-86, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-86, 1, 0]] 
 ![![193, 0, 0], ![107, 1, 0], ![162, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-86, 1, 0], ![0, -86, 2], ![710, 117, -86]]]
  hmulB := by decide  
  f := ![![![11783, -137, 0], ![26441, 0, 0]], ![![6537, -76, 0], ![14669, 0, 0]], ![![9910, -72, -1], ![22238, 97, 0]]]
  g := ![![![1, 0, 0], ![-107, 193, 0], ![-162, 0, 193]], ![![-1, 1, 0], ![46, -86, 2], ![11, 117, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-86, 43, 1]] ![![193, 0, 0], ![-86, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-16598, 193, 0]], ![![-16598, 8299, 193], ![8106, -3667, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-86, 1, 0]]], ![![![-86, 43, 1]], ![![42, -19, 0]]]]
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


lemma PB253I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB253I3 : PrimesBelowBoundCertificateInterval O 137 193 253 where
  m := 11
  g := ![3, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB253I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
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
      exact NI139N2
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
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
