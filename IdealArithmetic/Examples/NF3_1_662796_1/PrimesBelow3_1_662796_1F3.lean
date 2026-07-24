
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![75, 48, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![75, 48, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![75, 48, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![75, 48, 1], ![-12, 148, 478], ![4003, -1091, -43]]]
  hmulB := by decide  
  f := ![![![-74, -48, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -48, 139]], ![![0, 0, 1], ![-258, -164, 478], ![52, 7, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [69, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 138], [0, 1]]
 g := ![![[129, 137], [83, 100], [77], [121, 116], [81], [25], [1]], ![[0, 2], [0, 39], [77], [97, 23], [81], [25], [1]]]
 h' := ![![[134, 138], [111, 50], [50, 10], [130, 63], [38, 33], [117, 9], [70, 134], [0, 1]], ![[0, 1], [0, 89], [0, 129], [93, 76], [12, 106], [72, 130], [95, 5], [134, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [41, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [69, 5, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1022, -141, -585]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![323, 201, -585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-61, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-61, 1, 0]] 
 ![![139, 0, 0], ![78, 1, 0], ![43, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-61, 1, 0], ![-2, -59, 10], ![84, -23, -63]]]
  hmulB := by decide  
  f := ![![![-9990, -321742, 54530], ![2085, -757967, 0]], ![![-5568, -180490, 30590], ![1252, -425201, 0]], ![![-3072, -99532, 16869], ![687, -234479, 0]]]
  g := ![![![1, 0, 0], ![-78, 139, 0], ![-43, 0, 139]], ![![-1, 1, 0], ![30, -59, 10], ![33, -23, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![75, 48, 1]] ![![139, 0, 0], ![-61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8479, 139, 0]], ![![10425, 6672, 139], ![-4587, -2780, 417]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-61, 1, 0]]], ![![![75, 48, 1]], ![![-33, -20, 3]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-40, -6, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-40, -6, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![109, 143, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-40, -6, 1], ![96, -75, -62], ![-533, 151, -50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -143, 149]], ![![-1, -1, 1], ![46, 59, -62], ![33, 49, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [70, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 148], [0, 1]]
 g := ![![[97, 143], [96], [93, 73], [86], [110, 46], [73], [1]], ![[11, 6], [96], [146, 76], [86], [74, 103], [73], [1]]]
 h' := ![![[64, 148], [15, 21], [46, 29], [9, 85], [48, 91], [88, 33], [79, 64], [0, 1]], ![[0, 1], [18, 128], [114, 120], [85, 64], [61, 58], [114, 116], [3, 85], [64, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [40, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [70, 85, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5860, 2548, -3206]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2306, 3094, -3206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![62, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![62, 1, 0]] 
 ![![149, 0, 0], ![62, 1, 0], ![50, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![62, 1, 0], ![-2, 64, 10], ![84, -23, 60]]]
  hmulB := by decide  
  f := ![![![27423, -946979, -147960], ![5215, 2204604, 0]], ![![11382, -393999, -61560], ![2236, 917244, 0]], ![![9214, -317778, -49651], ![1722, 739800, 0]]]
  g := ![![![1, 0, 0], ![-62, 149, 0], ![-50, 0, 149]], ![![0, 1, 0], ![-30, 64, 10], ![-10, -23, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-40, -6, 1]] ![![149, 0, 0], ![62, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![9238, 149, 0]], ![![-5960, -894, 149], ![-2384, -447, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![62, 1, 0]]], ![![![-40, -6, 1]], ![![-16, -3, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![4, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![4, 1, 0]] 
 ![![151, 0, 0], ![4, 1, 0], ![88, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![4, 1, 0], ![-2, 6, 10], ![84, -23, 2]]]
  hmulB := by decide  
  f := ![![![-2659, 7980, 13300], ![0, -200830, 0]], ![![-70, 210, 350], ![1, -5285, 0]], ![![-1552, 4650, 7751], ![90, -117040, 0]]]
  g := ![![![1, 0, 0], ![-4, 151, 0], ![-88, 0, 151]], ![![0, 1, 0], ![-6, 6, 10], ![0, -23, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![43, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![43, 1, 0]] 
 ![![151, 0, 0], ![43, 1, 0], ![63, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![43, 1, 0], ![-2, 45, 10], ![84, -23, 41]]]
  hmulB := by decide  
  f := ![![![31096, -725787, -161280], ![4077, 2435328, 0]], ![![8840, -206648, -45920], ![1209, 693392, 0]], ![![12965, -302812, -67289], ![1732, 1016064, 0]]]
  g := ![![![1, 0, 0], ![-43, 151, 0], ![-63, 0, 151]], ![![0, 1, 0], ![-17, 45, 10], ![-10, -23, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-47, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-47, 1, 0]] 
 ![![151, 0, 0], ![104, 1, 0], ![45, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-47, 1, 0], ![-2, -45, 10], ![84, -23, -49]]]
  hmulB := by decide  
  f := ![![![13382, 314833, -69960], ![-1963, 1056396, 0]], ![![9214, 216819, -48180], ![-1358, 727518, 0]], ![![4007, 93824, -20849], ![-524, 314820, 0]]]
  g := ![![![1, 0, 0], ![-104, 151, 0], ![-45, 0, 151]], ![![-1, 1, 0], ![28, -45, 10], ![31, -23, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![4, 1, 0]] ![![151, 0, 0], ![43, 1, 0]]
  ![![151, 0, 0], ![17, 20, 1]] where
 M := ![![![22801, 0, 0], ![6493, 151, 0]], ![![604, 151, 0], ![170, 49, 10]]]
 hmul := by decide  
 g := ![![![![134, -20, -1], ![151, 0, 0]], ![![26, -19, -1], ![151, 0, 0]]], ![![![-13, -19, -1], ![151, 0, 0]], ![![0, -1, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![17, 20, 1]] ![![151, 0, 0], ![-47, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-7097, 151, 0]], ![![2567, 3020, 151], ![-755, -906, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-47, 1, 0]]], ![![![17, 20, 1]], ![![-5, -6, 1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![77, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![77, 1, 0]] 
 ![![157, 0, 0], ![77, 1, 0], ![98, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![77, 1, 0], ![-2, 79, 10], ![84, -23, 75]]]
  hmulB := by decide  
  f := ![![![12004, -525841, -66560], ![2669, 1044992, 0]], ![![5835, -257865, -32640], ![1414, 512448, 0]], ![![7490, -328232, -41547], ![1672, 652288, 0]]]
  g := ![![![1, 0, 0], ![-77, 157, 0], ![-98, 0, 157]], ![![0, 1, 0], ![-45, 79, 10], ![-35, -23, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-61, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-61, 1, 0]] 
 ![![157, 0, 0], ![96, 1, 0], ![1, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-61, 1, 0], ![-2, -59, 10], ![84, -23, -63]]]
  hmulB := by decide  
  f := ![![![1416, 43543, -7380], ![-157, 115866, 0]], ![![842, 26610, -4510], ![-156, 70807, 0]], ![![30, 277, -47], ![53, 738, 0]]]
  g := ![![![1, 0, 0], ![-96, 157, 0], ![-1, 0, 157]], ![![-1, 1, 0], ![36, -59, 10], ![15, -23, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-16, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-16, 1, 0]] 
 ![![157, 0, 0], ![141, 1, 0], ![103, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-16, 1, 0], ![-2, -14, 10], ![84, -23, -18]]]
  hmulB := by decide  
  f := ![![![-4181, -29500, 21070], ![314, -330799, 0]], ![![-3751, -26490, 18920], ![315, -297044, 0]], ![![-2735, -19354, 13823], ![284, -217021, 0]]]
  g := ![![![1, 0, 0], ![-141, 157, 0], ![-103, 0, 157]], ![![-1, 1, 0], ![6, -14, 10], ![33, -23, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![77, 1, 0]] ![![157, 0, 0], ![-61, 1, 0]]
  ![![157, 0, 0], ![-46, -61, 1]] where
 M := ![![![24649, 0, 0], ![-9577, 157, 0]], ![![12089, 157, 0], ![-4699, 18, 10]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![-15, 62, -1], ![157, 0, 0]]], ![![![77, 1, 0], ![0, 0, 0]], ![![-27, 4, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-46, -61, 1]] ![![157, 0, 0], ![-16, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-2512, 157, 0]], ![![-7222, -9577, 157], ![942, 785, -628]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-16, 1, 0]]], ![![![-46, -61, 1]], ![![6, 5, -4]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-28, -13, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-28, -13, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![135, 150, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-28, -13, 1], ![110, -77, -132], ![-1121, 312, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-135, -150, 163]], ![![-1, -1, 1], ![110, 121, -132], ![13, 24, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [18, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 162], [0, 1]]
 g := ![![[108, 145], [27, 65], [158], [158], [41], [155, 144], [1]], ![[55, 18], [155, 98], [158], [158], [41], [90, 19], [1]]]
 h' := ![![[12, 162], [3, 54], [133, 37], [83, 141], [112, 22], [144, 81], [145, 12], [0, 1]], ![[0, 1], [162, 109], [88, 126], [145, 22], [50, 141], [138, 82], [126, 151], [12, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [136, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [18, 151, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![595797, -142843, -92003]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79854, 83789, -92003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-31, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-31, 1, 0]] 
 ![![163, 0, 0], ![132, 1, 0], ![24, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-31, 1, 0], ![-2, -29, 10], ![84, -23, -33]]]
  hmulB := by decide  
  f := ![![![-5671, -84046, 28980], ![652, -472374, 0]], ![![-4598, -68037, 23460], ![490, -382398, 0]], ![![-831, -12375, 4267], ![117, -69552, 0]]]
  g := ![![![1, 0, 0], ![-132, 163, 0], ![-24, 0, 163]], ![![-1, 1, 0], ![22, -29, 10], ![24, -23, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-28, -13, 1]] ![![163, 0, 0], ![-31, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-5053, 163, 0]], ![![-4564, -2119, 163], ![978, 326, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-31, 1, 0]]], ![![![-28, -13, 1]], ![![6, 2, -1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [16, 152, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 50, 155], [77, 116, 12], [0, 1]]
 g := ![![[111, 101, 57], [73, 105, 128], [69, 6, 81], [23, 28], [122, 24], [21, 138, 1], []], ![[36, 125, 114, 55], [37, 22, 110, 136], [69, 162, 78, 15], [111, 16], [125, 99], [77, 90, 148, 17], [135, 144]], ![[152, 95, 139, 94], [98, 96, 13, 154], [108, 124, 46, 66], [118, 27], [113, 50], [35, 7, 67, 107], [111, 144]]]
 h' := ![![[61, 50, 155], [1, 133, 97], [65, 135, 63], [96, 64, 158], [56, 0, 23], [165, 111, 109], [0, 0, 1], [0, 1]], ![[77, 116, 12], [46, 147, 137], [97, 61, 10], [138, 76, 25], [54, 116, 163], [65, 95, 123], [58, 143, 116], [61, 50, 155]], ![[0, 1], [92, 54, 100], [56, 138, 94], [45, 27, 151], [51, 51, 148], [135, 128, 102], [145, 24, 50], [77, 116, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 90], []]
 b := ![[], [128, 97, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [16, 152, 29, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3766852, 1378251, -1440542]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22556, 8253, -8626]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![82, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![82, 1, 0]] 
 ![![173, 0, 0], ![82, 1, 0], ![3, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![82, 1, 0], ![-2, 84, 10], ![84, -23, 80]]]
  hmulB := by decide  
  f := ![![![-2717, 124491, 14820], ![-519, -256386, 0]], ![![-1322, 58969, 7020], ![-172, -121446, 0]], ![![-113, 2158, 257], ![130, -4446, 0]]]
  g := ![![![1, 0, 0], ![-82, 173, 0], ![-3, 0, 173]], ![![0, 1, 0], ![-40, 84, 10], ![10, -23, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-69, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-69, 1, 0]] 
 ![![173, 0, 0], ![104, 1, 0], ![143, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-69, 1, 0], ![-2, -67, 10], ![84, -23, -71]]]
  hmulB := by decide  
  f := ![![![851, 28475, -4250], ![0, 73525, 0]], ![![511, 17085, -2550], ![1, 44115, 0]], ![![713, 23537, -3513], ![24, 60775, 0]]]
  g := ![![![1, 0, 0], ![-104, 173, 0], ![-143, 0, 173]], ![![-1, 1, 0], ![32, -67, 10], ![73, -23, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-13, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-13, 1, 0]] 
 ![![173, 0, 0], ![160, 1, 0], ![72, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-13, 1, 0], ![-2, -11, 10], ![84, -23, -15]]]
  hmulB := by decide  
  f := ![![![40835, 225312, -204820], ![-1730, 3543386, 0]], ![![37768, 208371, -189420], ![-1556, 3276966, 0]], ![![17001, 93771, -85243], ![-639, 1474704, 0]]]
  g := ![![![1, 0, 0], ![-160, 173, 0], ![-72, 0, 173]], ![![-1, 1, 0], ![6, -11, 10], ![28, -23, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![82, 1, 0]] ![![173, 0, 0], ![-69, 1, 0]]
  ![![173, 0, 0], ![-47, -85, 1]] where
 M := ![![![29929, 0, 0], ![-11937, 173, 0]], ![![14186, 173, 0], ![-5660, 15, 10]]]
 hmul := by decide  
 g := ![![![![173, 0, 0], ![0, 0, 0]], ![![-22, 86, -1], ![173, 0, 0]]], ![![![82, 1, 0], ![0, 0, 0]], ![![-30, 5, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-47, -85, 1]] ![![173, 0, 0], ![-13, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-2249, 173, 0]], ![![-8131, -14705, 173], ![865, 865, -865]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-13, 1, 0]]], ![![![-47, -85, 1]], ![![5, 5, -5]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![30, 23, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![30, 23, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![30, 23, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![30, 23, 1], ![38, 53, 228], ![1903, -516, -38]]]
  hmulB := by decide  
  f := ![![![-29, -23, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -23, 179]], ![![0, 0, 1], ![-38, -29, 228], ![17, 2, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [131, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 178], [0, 1]]
 g := ![![[14, 5], [142, 95], [75], [76], [171, 138], [92, 146], [1]], ![[152, 174], [79, 84], [75], [76], [6, 41], [112, 33], [1]]]
 h' := ![![[135, 178], [14, 149], [88, 51], [28, 95], [153, 75], [120, 73], [48, 135], [0, 1]], ![[0, 1], [81, 30], [171, 128], [144, 84], [75, 104], [130, 106], [15, 44], [135, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [38, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [131, 44, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1123, -219, -780]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![137, 99, -780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-49, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-49, 1, 0]] 
 ![![179, 0, 0], ![130, 1, 0], ![38, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-49, 1, 0], ![-2, -47, 10], ![84, -23, -51]]]
  hmulB := by decide  
  f := ![![![-17457, -426398, 90720], ![2506, -1623888, 0]], ![![-12685, -309646, 65880], ![1791, -1179252, 0]], ![![-3669, -90521, 19259], ![667, -344736, 0]]]
  g := ![![![1, 0, 0], ![-130, 179, 0], ![-38, 0, 179]], ![![-1, 1, 0], ![32, -47, 10], ![28, -23, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![30, 23, 1]] ![![179, 0, 0], ![-49, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-8771, 179, 0]], ![![5370, 4117, 179], ![-1432, -1074, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-49, 1, 0]]], ![![![30, 23, 1]], ![![-8, -6, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-60, -52, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-60, -52, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![121, 129, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-60, -52, 1], ![188, -187, -522], ![-4397, 1209, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-121, -129, 181]], ![![-1, -1, 1], ![350, 371, -522], ![-39, -9, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [73, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 180], [0, 1]]
 g := ![![[81, 62], [49], [69, 9], [152], [138, 5], [176, 161], [1]], ![[0, 119], [49], [66, 172], [152], [76, 176], [62, 20], [1]]]
 h' := ![![[60, 180], [99, 116], [31, 7], [169, 178], [62, 141], [3, 154], [108, 60], [0, 1]], ![[0, 1], [0, 65], [89, 174], [170, 3], [15, 40], [12, 27], [88, 121], [60, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [146, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [73, 121, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19195, -1947, 3828]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2453, -2739, 3828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-21, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-21, 1, 0]] 
 ![![181, 0, 0], ![160, 1, 0], ![159, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-21, 1, 0], ![-2, -19, 10], ![84, -23, -23]]]
  hmulB := by decide  
  f := ![![![21806, 208551, -109760], ![-1267, 1986656, 0]], ![![19279, 184344, -97020], ![-1085, 1756062, 0]], ![![19161, 183202, -96419], ![-1066, 1745184, 0]]]
  g := ![![![1, 0, 0], ![-160, 181, 0], ![-159, 0, 181]], ![![-1, 1, 0], ![8, -19, 10], ![41, -23, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-60, -52, 1]] ![![181, 0, 0], ![-21, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-3801, 181, 0]], ![![-10860, -9412, 181], ![1448, 905, -543]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-21, 1, 0]]], ![![![-60, -52, 1]], ![![8, 5, -3]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![6, 57, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![6, 57, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![6, 57, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![6, 57, 1], ![-30, 97, 568], ![4759, -1298, -130]]]
  hmulB := by decide  
  f := ![![![-5, -57, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -57, 191]], ![![0, 0, 1], ![-18, -169, 568], ![29, 32, -130]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [23, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 190], [0, 1]]
 g := ![![[80, 108], [60, 81], [44, 34], [82, 177], [182, 97], [182, 125], [1]], ![[0, 83], [0, 110], [132, 157], [57, 14], [96, 94], [146, 66], [1]]]
 h' := ![![[70, 190], [148, 47], [134, 9], [24, 15], [16, 69], [16, 80], [168, 70], [0, 1]], ![[0, 1], [0, 144], [0, 182], [119, 176], [71, 122], [77, 111], [102, 121], [70, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [60, 162]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [23, 121, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1909, 869, -1496]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37, 451, -1496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![5, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![5, 1, 0]] 
 ![![191, 0, 0], ![5, 1, 0], ![130, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![5, 1, 0], ![-2, 7, 10], ![84, -23, 3]]]
  hmulB := by decide  
  f := ![![![11012, -38557, -55080], ![191, 1052028, 0]], ![![283, -1009, -1440], ![192, 27504, 0]], ![![7495, -26243, -37489], ![133, 716040, 0]]]
  g := ![![![1, 0, 0], ![-5, 191, 0], ![-130, 0, 191]], ![![0, 1, 0], ![-7, 7, 10], ![-1, -23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![6, 57, 1]] ![![191, 0, 0], ![5, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![955, 191, 0]], ![![1146, 10887, 191], ![0, 382, 573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![5, 1, 0]]], ![![![6, 57, 1]], ![![0, 2, 3]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![44, 72, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![44, 72, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![44, 72, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![44, 72, 1], ![-60, 165, 718], ![6019, -1643, -122]]]
  hmulB := by decide  
  f := ![![![-43, -72, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -72, 193]], ![![0, 0, 1], ![-164, -267, 718], ![59, 37, -122]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [40, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [156, 192], [0, 1]]
 g := ![![[54, 130], [137], [67], [97], [93], [98], [156, 1]], ![[69, 63], [137], [67], [97], [93], [98], [119, 192]]]
 h' := ![![[156, 192], [153, 55], [187, 152], [92, 158], [43, 167], [176, 155], [129, 171], [0, 1]], ![[0, 1], [48, 138], [160, 41], [36, 35], [40, 26], [38, 38], [171, 22], [156, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174]]
 b := ![[], [162, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [40, 37, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2092, 37, -1900]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![444, 709, -1900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![54, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![54, 1, 0]] 
 ![![193, 0, 0], ![54, 1, 0], ![122, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![54, 1, 0], ![-2, 56, 10], ![84, -23, 52]]]
  hmulB := by decide  
  f := ![![![10375, -301063, -53760], ![1351, 1037568, 0]], ![![2900, -84226, -15040], ![387, 290272, 0]], ![![6518, -190310, -33983], ![998, 655872, 0]]]
  g := ![![![1, 0, 0], ![-54, 193, 0], ![-122, 0, 193]], ![![0, 1, 0], ![-22, 56, 10], ![-26, -23, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![44, 72, 1]] ![![193, 0, 0], ![54, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![10422, 193, 0]], ![![8492, 13896, 193], ![2316, 4053, 772]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![54, 1, 0]]], ![![![44, 72, 1]], ![![12, 21, 4]]]]
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


lemma PB231I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB231I3 : PrimesBelowBoundCertificateInterval O 137 193 231 where
  m := 11
  g := ![2, 2, 3, 3, 2, 1, 3, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB231I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
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
      exact NI139N1
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
      exact NI157N2
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
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I163N1, I173N0, I173N1, I173N2, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [I163N1], [], [I173N0, I173N1, I173N2], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
