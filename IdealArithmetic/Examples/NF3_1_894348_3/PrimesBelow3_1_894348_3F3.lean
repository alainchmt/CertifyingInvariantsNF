
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![41, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![41, 1, 0]] 
 ![![139, 0, 0], ![41, 1, 0], ![18, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![41, 1, 0], ![0, 41, 7], ![182, 0, 41]]]
  hmulB := by decide  
  f := ![![![2215, 54, 0], ![-7506, 0, 0]], ![![615, 15, 0], ![-2084, 0, 0]], ![![242, 0, -1], ![-820, 20, 0]]]
  g := ![![![1, 0, 0], ![-41, 139, 0], ![-18, 0, 139]], ![![0, 1, 0], ![-13, 41, 7], ![-4, 0, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![44, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![44, 1, 0]] 
 ![![139, 0, 0], ![44, 1, 0], ![61, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![44, 1, 0], ![0, 44, 7], ![182, 0, 44]]]
  hmulB := by decide  
  f := ![![![2333, 53, 0], ![-7367, 0, 0]], ![![660, 15, 0], ![-2084, 0, 0]], ![![939, 15, -1], ![-2965, 20, 0]]]
  g := ![![![1, 0, 0], ![-44, 139, 0], ![-61, 0, 139]], ![![0, 1, 0], ![-17, 44, 7], ![-18, 0, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![54, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![54, 1, 0]] 
 ![![139, 0, 0], ![54, 1, 0], ![60, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![54, 1, 0], ![0, 54, 7], ![182, 0, 54]]]
  hmulB := by decide  
  f := ![![![2647, 49, 0], ![-6811, 0, 0]], ![![1026, 19, 0], ![-2640, 0, 0]], ![![1068, 12, -1], ![-2748, 20, 0]]]
  g := ![![![1, 0, 0], ![-54, 139, 0], ![-60, 0, 139]], ![![0, 1, 0], ![-24, 54, 7], ![-22, 0, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![41, 1, 0]] ![![139, 0, 0], ![44, 1, 0]]
  ![![139, 0, 0], ![-60, 32, 1]] where
 M := ![![![19321, 0, 0], ![6116, 139, 0]], ![![5699, 139, 0], ![1804, 85, 7]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![44, 1, 0], ![0, 0, 0]]], ![![![41, 1, 0], ![0, 0, 0]], ![![16, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-60, 32, 1]] ![![139, 0, 0], ![54, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![7506, 139, 0]], ![![-8340, 4448, 139], ![-3058, 1668, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![54, 1, 0]]], ![![![-60, 32, 1]], ![![-22, 12, 2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![69, 63, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![69, 63, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![69, 63, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![69, 63, 1], ![182, 69, 441], ![11466, 26, 69]]]
  hmulB := by decide  
  f := ![![![-68, -63, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -63, 149]], ![![0, 0, 1], ![-203, -186, 441], ![45, -29, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [145, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 148], [0, 1]]
 g := ![![[53, 37], [42], [79, 81], [7], [134, 19], [95], [1]], ![[0, 112], [42], [116, 68], [7], [139, 130], [95], [1]]]
 h' := ![![[63, 148], [45, 127], [18, 108], [52, 9], [89, 93], [98, 82], [4, 63], [0, 1]], ![[0, 1], [0, 22], [117, 41], [23, 140], [137, 56], [49, 67], [99, 86], [63, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [65, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [145, 86, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![509, -60, -79]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 33, -79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![6, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![6, 1, 0]] 
 ![![149, 0, 0], ![6, 1, 0], ![80, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![6, 1, 0], ![0, 6, 7], ![182, 0, 6]]]
  hmulB := by decide  
  f := ![![![139, 23, 0], ![-3427, 0, 0]], ![![-6, -1, 0], ![150, 0, 0]], ![![76, 10, -3], ![-1874, 64, 0]]]
  g := ![![![1, 0, 0], ![-6, 149, 0], ![-80, 0, 149]], ![![0, 1, 0], ![-4, 6, 7], ![-2, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![69, 63, 1]] ![![149, 0, 0], ![6, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![894, 149, 0]], ![![10281, 9387, 149], ![596, 447, 447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![6, 1, 0]]], ![![![69, 63, 1]], ![![4, 3, 3]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [12, 108, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 35, 130], [53, 115, 21], [0, 1]]
 g := ![![[55, 33, 47], [103, 86, 138], [15, 61, 76], [16, 144], [147, 25, 137], [148, 1], []], ![[124, 112, 112, 73], [33, 58, 127, 66], [116, 7, 115, 107], [76, 80], [37, 109, 37, 89], [72, 88], [76, 139]], ![[8, 45, 8, 39], [144, 113, 101, 100], [66, 96, 48, 124], [59, 78], [22, 40, 43, 45], [24, 17], [34, 139]]]
 h' := ![![[95, 35, 130], [123, 10, 54], [122, 68, 17], [149, 148, 128], [48, 69, 12], [36, 10, 52], [0, 0, 1], [0, 1]], ![[53, 115, 21], [67, 98, 111], [147, 86, 74], [52, 103, 136], [71, 94, 82], [62, 57, 32], [110, 96, 115], [95, 35, 130]], ![[0, 1], [145, 43, 137], [149, 148, 60], [33, 51, 38], [52, 139, 57], [88, 84, 67], [136, 55, 35], [53, 115, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 39], []]
 b := ![[], [35, 94, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [12, 108, 3, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117478, 6342, -9513]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![778, 42, -63]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [48, 117, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 81, 4], [39, 75, 153], [0, 1]]
 g := ![![[152, 37, 153], [39, 64], [107, 61, 115], [78, 106, 126], [79, 146, 81], [122, 1], []], ![[86, 41, 44, 31], [13, 11], [120, 130, 54, 37], [138, 44, 133, 49], [62, 112, 133, 56], [128, 130], [88, 16]], ![[76, 96, 115, 108], [19, 108], [104, 129, 118, 147], [86, 154, 97, 113], [14, 114, 70, 36], [78, 124], [96, 16]]]
 h' := ![![[83, 81, 4], [153, 93, 56], [45, 44, 149], [24, 21, 30], [133, 88, 122], [110, 122, 9], [0, 0, 1], [0, 1]], ![[39, 75, 153], [112, 96, 19], [118, 51, 47], [77, 156, 136], [41, 60, 82], [152, 77, 64], [153, 27, 75], [83, 81, 4]], ![[0, 1], [154, 125, 82], [81, 62, 118], [78, 137, 148], [140, 9, 110], [7, 115, 84], [53, 130, 81], [39, 75, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 138], []]
 b := ![[], [66, 27, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [48, 117, 35, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72534, 3297, -8478]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-462, 21, -54]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-77, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-77, 1, 0]] 
 ![![163, 0, 0], ![86, 1, 0], ![131, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-77, 1, 0], ![0, -77, 7], ![182, 0, -77]]]
  hmulB := by decide  
  f := ![![![4467, -58, 0], ![9454, 0, 0]], ![![2388, -31, 0], ![5054, 0, 0]], ![![3625, -14, -3], ![7672, 70, 0]]]
  g := ![![![1, 0, 0], ![-86, 163, 0], ![-131, 0, 163]], ![![-1, 1, 0], ![35, -77, 7], ![63, 0, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-65, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-65, 1, 0]] 
 ![![163, 0, 0], ![98, 1, 0], ![95, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-65, 1, 0], ![0, -65, 7], ![182, 0, -65]]]
  hmulB := by decide  
  f := ![![![10531, -162, 0], ![26406, 0, 0]], ![![6306, -97, 0], ![15812, 0, 0]], ![![6235, -68, -3], ![15634, 70, 0]]]
  g := ![![![1, 0, 0], ![-98, 163, 0], ![-95, 0, 163]], ![![-1, 1, 0], ![35, -65, 7], ![39, 0, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-21, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-21, 1, 0]] 
 ![![163, 0, 0], ![142, 1, 0], ![100, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-21, 1, 0], ![0, -21, 7], ![182, 0, -21]]]
  hmulB := by decide  
  f := ![![![2941, -140, 0], ![22820, 0, 0]], ![![2542, -121, 0], ![19724, 0, 0]], ![![1786, -76, -3], ![13858, 70, 0]]]
  g := ![![![1, 0, 0], ![-142, 163, 0], ![-100, 0, 163]], ![![-1, 1, 0], ![14, -21, 7], ![14, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-77, 1, 0]] ![![163, 0, 0], ![-65, 1, 0]]
  ![![163, 0, 0], ![63, 3, 1]] where
 M := ![![![26569, 0, 0], ![-10595, 163, 0]], ![![-12551, 163, 0], ![5005, -142, 7]]]
 hmul := by decide  
 g := ![![![![100, -3, -1], ![163, 0, 0]], ![![-65, 1, 0], ![0, 0, 0]]], ![![![-77, 1, 0], ![0, 0, 0]], ![![-35, -4, -1], ![170, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![63, 3, 1]] ![![163, 0, 0], ![-21, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-3423, 163, 0]], ![![10269, 489, 163], ![-1141, 0, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-21, 1, 0]]], ![![![63, 3, 1]], ![![-7, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![58, 35, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![58, 35, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![58, 35, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![58, 35, 1], ![182, 58, 245], ![6370, 26, 58]]]
  hmulB := by decide  
  f := ![![![-57, -35, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -35, 167]], ![![0, 0, 1], ![-84, -51, 245], ![18, -12, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [96, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 166], [0, 1]]
 g := ![![[79, 127], [162, 14], [144, 96], [100], [28], [35, 85], [1]], ![[0, 40], [31, 153], [33, 71], [100], [28], [15, 82], [1]]]
 h' := ![![[98, 166], [146, 36], [37, 101], [81, 116], [50, 157], [147, 144], [71, 98], [0, 1]], ![[0, 1], [0, 131], [82, 66], [93, 51], [72, 10], [64, 23], [156, 69], [98, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [103, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [96, 69, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-926, 305, -206]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 45, -206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-78, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-78, 1, 0]] 
 ![![167, 0, 0], ![89, 1, 0], ![109, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-78, 1, 0], ![0, -78, 7], ![182, 0, -78]]]
  hmulB := by decide  
  f := ![![![2107, -27, 0], ![4509, 0, 0]], ![![1093, -14, 0], ![2339, 0, 0]], ![![1421, -7, -1], ![3041, 24, 0]]]
  g := ![![![1, 0, 0], ![-89, 167, 0], ![-109, 0, 167]], ![![-1, 1, 0], ![37, -78, 7], ![52, 0, -78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![58, 35, 1]] ![![167, 0, 0], ![-78, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-13026, 167, 0]], ![![9686, 5845, 167], ![-4342, -2672, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-78, 1, 0]]], ![![![58, 35, 1]], ![![-26, -16, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-19, -56, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-19, -56, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![154, 117, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-19, -56, 1], ![182, -19, -392], ![-10192, 26, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -117, 173]], ![![-1, -1, 1], ![350, 265, -392], ![-42, 13, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [46, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 172], [0, 1]]
 g := ![![[118, 40], [25], [172, 1], [67, 126], [118], [24, 73], [1]], ![[113, 133], [25], [107, 172], [8, 47], [118], [123, 100], [1]]]
 h' := ![![[108, 172], [101, 46], [46, 5], [32, 1], [139, 105], [107, 139], [127, 108], [0, 1]], ![[0, 1], [52, 127], [67, 168], [140, 172], [61, 68], [68, 34], [27, 65], [108, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [158, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [46, 65, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![410, -39, -58]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 39, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![46, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![46, 1, 0]] 
 ![![173, 0, 0], ![46, 1, 0], ![19, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![46, 1, 0], ![0, 46, 7], ![182, 0, 46]]]
  hmulB := by decide  
  f := ![![![2807, 61, 0], ![-10553, 0, 0]], ![![690, 15, 0], ![-2594, 0, 0]], ![![245, -21, -4], ![-921, 99, 0]]]
  g := ![![![1, 0, 0], ![-46, 173, 0], ![-19, 0, 173]], ![![0, 1, 0], ![-13, 46, 7], ![-4, 0, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-19, -56, 1]] ![![173, 0, 0], ![46, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![7958, 173, 0]], ![![-3287, -9688, 173], ![-692, -2595, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![46, 1, 0]]], ![![![-19, -56, 1]], ![![-4, -15, -2]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![11, -79, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![11, -79, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![11, 100, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![11, -79, 1], ![182, 11, -553], ![-14378, 26, 11]]]
  hmulB := by decide  
  f := ![![![-10, 79, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -100, 179]], ![![0, -1, 1], ![35, 309, -553], ![-81, -6, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [52, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 178], [0, 1]]
 g := ![![[163, 31], [66, 110], [14], [126], [141, 101], [124, 31], [1]], ![[0, 148], [117, 69], [14], [126], [43, 78], [140, 148], [1]]]
 h' := ![![[116, 178], [148, 116], [68, 162], [120, 67], [7, 22], [175, 82], [127, 116], [0, 1]], ![[0, 1], [0, 63], [65, 17], [16, 112], [53, 157], [21, 97], [158, 63], [116, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177]]
 b := ![[], [58, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [52, 63, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7032, 1261, 2592]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-120, -1441, 2592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![16, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![16, 1, 0]] 
 ![![179, 0, 0], ![16, 1, 0], ![168, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![16, 1, 0], ![0, 16, 7], ![182, 0, 16]]]
  hmulB := by decide  
  f := ![![![833, 52, 0], ![-9308, 0, 0]], ![![48, 3, 0], ![-536, 0, 0]], ![![792, 38, -5], ![-8850, 128, 0]]]
  g := ![![![1, 0, 0], ![-16, 179, 0], ![-168, 0, 179]], ![![0, 1, 0], ![-8, 16, 7], ![-14, 0, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![11, -79, 1]] ![![179, 0, 0], ![16, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![2864, 179, 0]], ![![1969, -14141, 179], ![358, -1253, -537]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![16, 1, 0]]], ![![![11, -79, 1]], ![![2, -7, -3]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5171, 477, 308]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![5171, 477, 308]] 
 ![![181, 0, 0], ![93, 1, 0], ![109, 0, 1]] where
  M :=![![![5171, 477, 308], ![56056, 5171, 3339], ![86814, 8008, 5171]]]
  hmulB := by decide  
  f := ![![![529, -103, 35]], ![![307, -50, 14]], ![![215, -57, 24]]]
  g := ![![![-402, 477, 308], ![-4358, 5171, 3339], ![-6749, 8008, 5171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, 2]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-1, -3, 2]] 
 ![![181, 0, 0], ![120, 1, 0], ![89, 0, 1]] where
  M :=![![![-1, -3, 2], ![364, -1, -21], ![-546, 52, -1]]]
  hmulB := by decide  
  f := ![![![1093, 101, 65]], ![![790, 73, 47]], ![![639, 59, 38]]]
  g := ![![![1, -3, 2], ![13, -1, -21], ![-37, 52, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 0, 1]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-17, 0, 1]] 
 ![![181, 0, 0], ![149, 1, 0], ![164, 0, 1]] where
  M :=![![![-17, 0, 1], ![182, -17, 0], ![0, 26, -17]]]
  hmulB := by decide  
  f := ![![![-289, -26, -17]], ![![-255, -23, -15]], ![![-288, -26, -17]]]
  g := ![![![-1, 0, 1], ![15, -17, 0], ![-6, 26, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![5171, 477, 308]] ![![-1, -3, 2]]
  ![![289, 26, 17]] where
 M := ![![![289, 26, 17]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![289, 26, 17]] ![![-17, 0, 1]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-77, 84, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-77, 84, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![114, 84, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-77, 84, 1], ![182, -77, 588], ![15288, 26, -77]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -84, 191]], ![![-1, 0, 1], ![-350, -259, 588], ![126, 34, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [28, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 190], [0, 1]]
 g := ![![[59, 68], [39, 125], [91, 18], [109, 16], [75, 103], [6, 96], [1]], ![[31, 123], [10, 66], [151, 173], [35, 175], [100, 88], [135, 95], [1]]]
 h' := ![![[67, 190], [54, 91], [126, 70], [4, 171], [1, 187], [23, 26], [163, 67], [0, 1]], ![[0, 1], [39, 100], [41, 121], [1, 20], [115, 4], [46, 165], [68, 124], [67, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [151, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [28, 124, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1187, 392, -59]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 28, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-15, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-15, 1, 0]] 
 ![![191, 0, 0], ![176, 1, 0], ![77, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-15, 1, 0], ![0, -15, 7], ![182, 0, -15]]]
  hmulB := by decide  
  f := ![![![856, -57, 0], ![10887, 0, 0]], ![![796, -53, 0], ![10124, 0, 0]], ![![352, -17, -3], ![4477, 82, 0]]]
  g := ![![![1, 0, 0], ![-176, 191, 0], ![-77, 0, 191]], ![![-1, 1, 0], ![11, -15, 7], ![7, 0, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-77, 84, 1]] ![![191, 0, 0], ![-15, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2865, 191, 0]], ![![-14707, 16044, 191], ![1337, -1337, 573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-15, 1, 0]]], ![![![-77, 84, 1]], ![![7, -7, 3]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [49, 66, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 63, 6], [122, 129, 187], [0, 1]]
 g := ![![[34, 105, 86], [157, 65], [134, 1], [56, 69], [164, 134], [], [1]], ![[114, 64, 122, 137], [135, 147], [150, 181], [83, 56], [81, 139], [170, 100], [63, 6, 49, 23]], ![[153, 65, 15, 48], [160, 168], [49, 86], [50, 121], [20, 124], [139, 100], [132, 24, 36, 170]]]
 h' := ![![[71, 63, 6], [73, 42, 146], [168, 10, 114], [128, 126, 192], [154, 19, 164], [85, 99, 110], [144, 127], [0, 1]], ![[122, 129, 187], [59, 109, 172], [43, 45, 98], [161, 86, 48], [102, 71, 40], [156, 106, 116], [90, 88, 183], [71, 63, 6]], ![[0, 1], [115, 42, 68], [106, 138, 174], [34, 174, 146], [174, 103, 182], [162, 181, 160], [5, 171, 10], [122, 129, 187]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 106], []]
 b := ![[], [57, 181, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [49, 66, 0, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39179, 1158, 2316]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![203, 6, 12]
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



lemma PB268I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB268I3 : PrimesBelowBoundCertificateInterval O 137 193 268 where
  m := 11
  g := ![3, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB268I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
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
  β := ![I139N0, I139N1, I139N2, I149N1, I163N0, I163N1, I163N2, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [], [], [I163N0, I163N1, I163N2], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
