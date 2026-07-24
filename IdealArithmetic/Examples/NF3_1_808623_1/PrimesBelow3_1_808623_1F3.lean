
import IdealArithmetic.Examples.NF3_1_808623_1.RI3_1_808623_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [133, 132, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 122, 17], [21, 16, 122], [0, 1]]
 g := ![![[47, 30, 64], [21, 75, 79], [2, 99], [0, 11, 9], [108, 77], [25, 1], []], ![[123, 119, 36, 82], [121, 86, 117, 61], [16, 100], [113, 98, 27, 108], [5, 117], [89, 117], [114, 11]], ![[1, 104, 80, 49], [70, 27, 8, 11], [88, 107], [38, 105, 99, 116], [72, 125], [7, 11], [9, 11]]]
 h' := ![![[4, 122, 17], [126, 46, 131], [12, 52, 94], [0, 121, 88], [74, 57, 3], [11, 42, 76], [0, 0, 1], [0, 1]], ![[21, 16, 122], [131, 66, 98], [134, 133, 25], [90, 13, 129], [39, 103, 44], [3, 126, 123], [5, 33, 16], [4, 122, 17]], ![[0, 1], [51, 27, 49], [96, 93, 20], [92, 5, 61], [115, 118, 92], [10, 110, 79], [78, 106, 122], [21, 16, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 127], []]
 b := ![[], [18, 20, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [133, 132, 114, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-727526, 1251, 2085]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5234, 9, 15]
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


def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-67, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-67, 1, 0]] 
 ![![149, 0, 0], ![82, 1, 0], ![112, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-67, 1, 0], ![-2, -65, 5], ![177, 11, -69]]]
  hmulB := by decide  
  f := ![![![241, 7800, -600], ![0, 17880, 0]], ![![133, 4290, -330], ![1, 9834, 0]], ![![187, 5863, -451], ![13, 13440, 0]]]
  g := ![![![1, 0, 0], ![-82, 149, 0], ![-112, 0, 149]], ![![-1, 1, 0], ![32, -65, 5], ![47, 11, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-15, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-15, 1, 0]] 
 ![![149, 0, 0], ![134, 1, 0], ![50, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-15, 1, 0], ![-2, -13, 5], ![177, 11, -17]]]
  hmulB := by decide  
  f := ![![![38711, 252994, -97300], ![-2086, 2899540, 0]], ![![34806, 227513, -87500], ![-1936, 2607500, 0]], ![![12995, 84897, -32651], ![-653, 973000, 0]]]
  g := ![![![1, 0, 0], ![-134, 149, 0], ![-50, 0, 149]], ![![-1, 1, 0], ![10, -13, 5], ![-3, 11, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-67, 1, 0]] ![![149, 0, 0], ![-67, 1, 0]]
  ![![149, 0, 0], ![63, 63, 1]] where
 M := ![![![22201, 0, 0], ![-9983, 149, 0]], ![![-9983, 149, 0], ![4487, -132, 5]]]
 hmul := by decide  
 g := ![![![![86, -63, -1], ![149, 0, 0]], ![![-67, 1, 0], ![0, 0, 0]]], ![![![-67, 1, 0], ![0, 0, 0]], ![![-35, -66, -1], ![154, 0, 0]]]]
 hle2 := by decide  
def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![63, 63, 1]] ![![149, 0, 0], ![-15, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-2235, 149, 0]], ![![9387, 9387, 149], ![-894, -745, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-15, 1, 0]]], ![![![63, 63, 1]], ![![-6, -5, 2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-65, -31, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-65, -31, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![86, 120, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-65, -31, 1], ![239, -116, -157], ![-5633, -310, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -120, 151]], ![![-1, -1, 1], ![91, 124, -157], ![-43, -10, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [138, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 150], [0, 1]]
 g := ![![[106, 58], [127, 49], [52, 21], [116], [147, 2], [59], [1]], ![[0, 93], [1, 102], [149, 130], [116], [34, 149], [59], [1]]]
 h' := ![![[19, 150], [141, 80], [72, 7], [135, 25], [99, 95], [30, 105], [13, 19], [0, 1]], ![[0, 1], [0, 71], [54, 144], [6, 126], [92, 56], [62, 46], [72, 132], [19, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [109, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [138, 132, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13033, 5244, 3260]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1943, -2556, 3260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![6, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![6, 1, 0]] 
 ![![151, 0, 0], ![6, 1, 0], ![141, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![6, 1, 0], ![-2, 8, 5], ![177, 11, 4]]]
  hmulB := by decide  
  f := ![![![4531, -18145, -11340], ![151, 342468, 0]], ![![174, -721, -450], ![152, 13590, 0]], ![![4233, -16943, -10589], ![89, 319788, 0]]]
  g := ![![![1, 0, 0], ![-6, 151, 0], ![-141, 0, 151]], ![![0, 1, 0], ![-5, 8, 5], ![-3, 11, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-65, -31, 1]] ![![151, 0, 0], ![6, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![906, 151, 0]], ![![-9815, -4681, 151], ![-151, -302, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![6, 1, 0]]], ![![![-65, -31, 1]], ![![-1, -2, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![53, 4, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![53, 4, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![53, 4, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![53, 4, 1], ![169, 72, 18], ![562, 75, 58]]]
  hmulB := by decide  
  f := ![![![-52, -4, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -4, 157]], ![![0, 0, 1], ![-5, 0, 18], ![-16, -1, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [138, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 156], [0, 1]]
 g := ![![[52, 33], [13], [82, 71], [43, 64], [71, 132], [75], [1]], ![[0, 124], [13], [51, 86], [4, 93], [20, 25], [75], [1]]]
 h' := ![![[46, 156], [77, 70], [145, 22], [32, 68], [93, 149], [59, 17], [19, 46], [0, 1]], ![[0, 1], [0, 87], [58, 135], [20, 89], [39, 8], [56, 140], [94, 111], [46, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [97, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [138, 111, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3308626, 1764100, 438199]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126853, 72, 438199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-18, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-18, 1, 0]] 
 ![![157, 0, 0], ![139, 1, 0], ![99, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-18, 1, 0], ![-2, -16, 5], ![177, 11, -20]]]
  hmulB := by decide  
  f := ![![![-4843, -39042, 12200], ![314, -383080, 0]], ![![-4283, -34562, 10800], ![315, -339120, 0]], ![![-3051, -24619, 7693], ![223, -241560, 0]]]
  g := ![![![1, 0, 0], ![-139, 157, 0], ![-99, 0, 157]], ![![-1, 1, 0], ![11, -16, 5], ![4, 11, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![53, 4, 1]] ![![157, 0, 0], ![-18, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-2826, 157, 0]], ![![8321, 628, 157], ![-785, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-18, 1, 0]]], ![![![53, 4, 1]], ![![-5, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -14, -5]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-85, -14, -5]] 
 ![![163, 0, 0], ![0, 163, 0], ![17, 68, 1]] where
  M :=![![![-85, -14, -5], ![-857, -168, -60], ![-1748, -309, -122]]]
  hmulB := by decide  
  f := ![![![-12, 1, 0]], ![![-2, -10, 5]], ![![-1, -4, 2]]]
  g := ![![![0, 2, -5], ![1, 24, -60], ![2, 49, -122]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [145, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 162], [0, 1]]
 g := ![![[97, 9], [35, 136], [126], [40], [41], [109, 90], [1]], ![[0, 154], [0, 27], [126], [40], [41], [117, 73], [1]]]
 h' := ![![[116, 162], [141, 3], [129, 138], [119, 146], [122, 23], [6, 81], [18, 116], [0, 1]], ![[0, 1], [0, 160], [0, 25], [103, 17], [19, 140], [111, 82], [108, 47], [116, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [47, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [145, 47, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7893, 5103, 1089]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-162, -423, 1089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-12, 1, 0]] 
 ![![163, 0, 0], ![151, 1, 0], ![106, 0, 1]] where
  M :=![![![-12, 1, 0], ![-2, -10, 5], ![177, 11, -14]]]
  hmulB := by decide  
  f := ![![![-85, -14, -5]], ![![-84, -14, -5]], ![![-66, -11, -4]]]
  g := ![![![-1, 1, 0], ![6, -10, 5], ![0, 11, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-85, -14, -5]] ![![-12, 1, 0]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![65, -20, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![65, -20, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![65, 147, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![65, -20, 1], ![217, 36, -102], ![-3686, -189, 118]]]
  hmulB := by decide  
  f := ![![![-64, 20, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -147, 167]], ![![0, -1, 1], ![41, 90, -102], ![-68, -105, 118]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [163, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 166], [0, 1]]
 g := ![![[42, 27], [166, 22], [156, 12], [84], [6], [9, 1], [1]], ![[69, 140], [21, 145], [1, 155], [84], [6], [10, 166], [1]]]
 h' := ![![[1, 166], [163, 19], [123, 135], [91, 43], [151, 90], [36, 29], [4, 1], [0, 1]], ![[0, 1], [15, 148], [91, 32], [134, 124], [74, 77], [65, 138], [5, 166], [1, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [59, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [163, 166, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2141, 613, -540]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 479, -540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-65, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-65, 1, 0]] 
 ![![167, 0, 0], ![102, 1, 0], ![49, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-65, 1, 0], ![-2, -63, 5], ![177, 11, -67]]]
  hmulB := by decide  
  f := ![![![7527, 253457, -20115], ![-1336, 671841, 0]], ![![4590, 154796, -12285], ![-834, 410319, 0]], ![![2249, 74367, -5902], ![-288, 197127, 0]]]
  g := ![![![1, 0, 0], ![-102, 167, 0], ![-49, 0, 167]], ![![-1, 1, 0], ![37, -63, 5], ![14, 11, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![65, -20, 1]] ![![167, 0, 0], ![-65, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-10855, 167, 0]], ![![10855, -3340, 167], ![-4008, 1336, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-65, 1, 0]]], ![![![65, -20, 1]], ![![-24, 8, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![45, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![45, 1, 0]] 
 ![![173, 0, 0], ![45, 1, 0], ![61, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![45, 1, 0], ![-2, 47, 5], ![177, 11, 43]]]
  hmulB := by decide  
  f := ![![![-14849, 359560, 38250], ![-1730, -1323450, 0]], ![![-3888, 93485, 9945], ![-345, -344097, 0]], ![![-5248, 126781, 13487], ![-563, -466650, 0]]]
  g := ![![![1, 0, 0], ![-45, 173, 0], ![-61, 0, 173]], ![![0, 1, 0], ![-14, 47, 5], ![-17, 11, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![49, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![49, 1, 0]] 
 ![![173, 0, 0], ![49, 1, 0], ![88, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![49, 1, 0], ![-2, 51, 5], ![177, 11, 47]]]
  hmulB := by decide  
  f := ![![![36597, -968212, -94920], ![4844, 3284232, 0]], ![![10360, -274184, -26880], ![1385, 930048, 0]], ![![18611, -492501, -48283], ![2481, 1670592, 0]]]
  g := ![![![1, 0, 0], ![-49, 173, 0], ![-88, 0, 173]], ![![0, 1, 0], ![-17, 51, 5], ![-26, 11, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![79, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![79, 1, 0]] 
 ![![173, 0, 0], ![79, 1, 0], ![0, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![79, 1, 0], ![-2, 81, 5], ![177, 11, 77]]]
  hmulB := by decide  
  f := ![![![-78, -1, 0], ![173, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-23, -49, -3], ![53, 104, 0]]]
  g := ![![![1, 0, 0], ![-79, 173, 0], ![0, 0, 173]], ![![0, 1, 0], ![-37, 81, 5], ![-4, 11, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![45, 1, 0]] ![![173, 0, 0], ![49, 1, 0]]
  ![![173, 0, 0], ![60, -50, 1]] where
 M := ![![![29929, 0, 0], ![8477, 173, 0]], ![![7785, 173, 0], ![2203, 96, 5]]]
 hmul := by decide  
 g := ![![![![113, 50, -1], ![173, 0, 0]], ![![-11, 51, -1], ![173, 0, 0]]], ![![![-15, 51, -1], ![173, 0, 0]], ![![11, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![60, -50, 1]] ![![173, 0, 0], ![79, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![13667, 173, 0]], ![![10380, -8650, 173], ![5017, -3979, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![79, 1, 0]]], ![![![60, -50, 1]], ![![29, -23, -1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1219, 324, -221]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![1219, 324, -221]] 
 ![![179, 0, 0], ![0, 179, 0], ![69, 69, 1]] where
  M :=![![![1219, 324, -221], ![-39765, -564, 2062], ![89614, -3287, -2302]]]
  hmulB := by decide  
  f := ![![![-45118, -8225, -3036]], ![![-520922, -94964, -35053]], ![![-223851, -40808, -15063]]]
  g := ![![![92, 87, -221], ![-1017, -798, 2062], ![1388, 869, -2302]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [145, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 178], [0, 1]]
 g := ![![[13, 100], [49, 74], [139], [138], [19, 149], [19, 75], [1]], ![[0, 79], [0, 105], [139], [138], [5, 30], [54, 104], [1]]]
 h' := ![![[84, 178], [55, 10], [178, 130], [105, 153], [109, 106], [109, 111], [34, 84], [0, 1]], ![[0, 1], [0, 169], [0, 49], [69, 26], [63, 73], [125, 68], [109, 95], [84, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [25, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [145, 95, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54603, 9137, 3453]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1026, -1280, 3453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45118, -8225, -3036]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-45118, -8225, -3036]] 
 ![![179, 0, 0], ![15, 1, 0], ![56, 0, 1]] where
  M :=![![![-45118, -8225, -3036], ![-520922, -94964, -35053], ![-1012569, -184591, -68136]]]
  hmulB := by decide  
  f := ![![![1219, 324, -221]], ![![-120, 24, -7]], ![![882, 83, -82]]]
  g := ![![![1387, -8225, -3036], ![16014, -94964, -35053], ![31128, -184591, -68136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![1219, 324, -221]] ![![-45118, -8225, -3036]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10686, 1948, 719]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![10686, 1948, 719]] 
 ![![181, 0, 0], ![0, 181, 0], ![71, 81, 1]] where
  M :=![![![10686, 1948, 719], ![123367, 22491, 8302], ![239822, 43717, 16137]]]
  hmulB := by decide  
  f := ![![![-7, -13, 7]], ![![1265, 44, -79]], ![![545, 15, -32]]]
  g := ![![![-223, -311, 719], ![-2575, -3591, 8302], ![-5005, -6980, 16137]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [167, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 180], [0, 1]]
 g := ![![[139, 168], [55], [180, 94], [144], [80, 62], [106, 34], [1]], ![[0, 13], [55], [113, 87], [144], [5, 119], [24, 147], [1]]]
 h' := ![![[136, 180], [61, 118], [167, 69], [95, 128], [34, 12], [36, 65], [14, 136], [0, 1]], ![[0, 1], [0, 63], [139, 112], [127, 53], [37, 169], [7, 116], [48, 45], [136, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [90, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [167, 45, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6203, 2111, 397]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-190, -166, 397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 13, -7]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![7, 13, -7]] 
 ![![181, 0, 0], ![140, 1, 0], ![78, 0, 1]] where
  M :=![![![7, 13, -7], ![-1265, -44, 79], ![3323, -74, -110]]]
  hmulB := by decide  
  f := ![![![-10686, -1948, -719]], ![![-8947, -1631, -602]], ![![-5930, -1081, -399]]]
  g := ![![![-7, 13, -7], ![-7, -44, 79], ![123, -74, -110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![10686, 1948, 719]] ![![7, 13, -7]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-71, -91, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-71, -91, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![120, 100, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-71, -91, 1], ![359, -242, -457], ![-16253, -970, 124]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -100, 191]], ![![-1, -1, 1], ![289, 238, -457], ![-163, -70, 124]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [103, 60, 1] where
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
 g := ![![[8, 102], [176, 80], [166, 50], [111, 80], [42, 103], [157, 162], [1]], ![[0, 89], [151, 111], [31, 141], [86, 111], [165, 88], [178, 29], [1]]]
 h' := ![![[131, 190], [17, 169], [92, 135], [27, 94], [67, 135], [64, 165], [88, 131], [0, 1]], ![[0, 1], [0, 22], [14, 56], [117, 97], [180, 56], [96, 26], [59, 60], [131, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [69, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [103, 60, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2929, 4510, 1745]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1081, -890, 1745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![75, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![75, 1, 0]] 
 ![![191, 0, 0], ![75, 1, 0], ![67, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![75, 1, 0], ![-2, 77, 5], ![177, 11, 73]]]
  hmulB := by decide  
  f := ![![![30426, -1255129, -81500], ![5539, 3113300, 0]], ![![11900, -492812, -32000], ![2293, 1222400, 0]], ![![10662, -440281, -28589], ![1971, 1092100, 0]]]
  g := ![![![1, 0, 0], ![-75, 191, 0], ![-67, 0, 191]], ![![0, 1, 0], ![-32, 77, 5], ![-29, 11, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-71, -91, 1]] ![![191, 0, 0], ![75, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![14325, 191, 0]], ![![-13561, -17381, 191], ![-4966, -7067, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![75, 1, 0]]], ![![![-71, -91, 1]], ![![-26, -37, -2]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![46, -3, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![46, -3, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![46, 190, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![46, -3, 1], ![183, 51, -17], ![-677, -2, 65]]]
  hmulB := by decide  
  f := ![![![-45, 3, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -190, 193]], ![![0, -1, 1], ![5, 17, -17], ![-19, -64, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [4, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 192], [0, 1]]
 g := ![![[31, 145], [144], [24], [147], [166], [185], [69, 1]], ![[0, 48], [144], [24], [147], [166], [185], [138, 192]]]
 h' := ![![[69, 192], [62, 97], [32, 181], [163, 105], [65, 95], [166, 121], [110, 125], [0, 1]], ![[0, 1], [0, 96], [169, 12], [74, 88], [58, 98], [23, 72], [50, 68], [69, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [127, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [4, 124, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20699, 9135, 815]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87, -755, 815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![17, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![17, 1, 0]] 
 ![![193, 0, 0], ![17, 1, 0], ![128, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![17, 1, 0], ![-2, 19, 5], ![177, 11, 15]]]
  hmulB := by decide  
  f := ![![![41188, -392739, -103350], ![1737, 3989310, 0]], ![![3623, -34581, -9100], ![194, 351260, 0]], ![![27323, -260469, -68543], ![1077, 2645760, 0]]]
  g := ![![![1, 0, 0], ![-17, 193, 0], ![-128, 0, 193]], ![![0, 1, 0], ![-5, 19, 5], ![-10, 11, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![46, -3, 1]] ![![193, 0, 0], ![17, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![3281, 193, 0]], ![![8878, -579, 193], ![965, 0, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![17, 1, 0]]], ![![![46, -3, 1]], ![![5, 0, 0]]]]
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


lemma PB255I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB255I3 : PrimesBelowBoundCertificateInterval O 137 193 255 where
  m := 11
  g := ![1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB255I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
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
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
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
      exact NI167N1
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
  β := ![I149N0, I149N1, I151N1, I157N1, I163N1, I167N1, I173N0, I173N1, I173N2, I179N1, I181N1, I191N1, I193N1]
  Il := ![[], [I149N0, I149N0, I149N1], [I151N1], [I157N1], [I163N1], [I167N1], [I173N0, I173N1, I173N2], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
