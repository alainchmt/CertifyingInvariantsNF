
import IdealArithmetic.Examples.NF3_3_582169_2.RI3_3_582169_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [66, 62, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 102, 64], [74, 36, 75], [0, 1]]
 g := ![![[131, 132, 67], [84, 48, 96], [84, 77], [80, 41, 38], [81, 127], [46, 1], []], ![[81, 17, 42, 34], [9, 21, 45, 41], [93, 7], [15, 43, 55, 52], [134, 125], [136, 45], [61, 65]], ![[94, 108, 37, 39], [33, 42, 29, 82], [5, 44], [78, 23, 62, 87], [112, 7], [112, 118], [50, 65]]]
 h' := ![![[111, 102, 64], [16, 86, 117], [20, 87, 42], [2, 127, 63], [3, 123, 49], [22, 1, 108], [0, 0, 1], [0, 1]], ![[74, 36, 75], [127, 104, 125], [3, 124, 130], [5, 107, 110], [53, 21, 45], [138, 120, 60], [94, 116, 36], [111, 102, 64]], ![[0, 1], [69, 88, 36], [133, 67, 106], [121, 44, 105], [81, 134, 45], [55, 18, 110], [91, 23, 102], [74, 36, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 48], []]
 b := ![[], [101, 94, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [66, 62, 93, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1048894, 437850, -35445]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7546, 3150, -255]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![0, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![0, 1, 0]] 
 ![![149, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![0, 1, 0], ![0, 0, 1], ![-1639, 254, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![0, 1, 0], ![0, 0, 1], ![-11, 254, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![23, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![23, 1, 0]] 
 ![![149, 0, 0], ![23, 1, 0], ![67, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![23, 1, 0], ![0, 23, 1], ![-1639, 254, 24]]]
  hmulB := by decide  
  f := ![![![254, 11, 0], ![-1639, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![96, 4, 0], ![-619, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 149, 0], ![-67, 0, 149]], ![![0, 1, 0], ![-4, 23, 1], ![-61, 254, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-24, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-24, 1, 0]] 
 ![![149, 0, 0], ![125, 1, 0], ![20, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-24, 1, 0], ![0, -24, 1], ![-1639, 254, -23]]]
  hmulB := by decide  
  f := ![![![3025, -126, 0], ![18774, 0, 0]], ![![2569, -107, 0], ![15944, 0, 0]], ![![436, -18, 0], ![2706, 1, 0]]]
  g := ![![![1, 0, 0], ![-125, 149, 0], ![-20, 0, 149]], ![![-1, 1, 0], ![20, -24, 1], ![-221, 254, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![0, 1, 0]] ![![149, 0, 0], ![23, 1, 0]]
  ![![149, 0, 0], ![-149, 23, 1]] where
 M := ![![![22201, 0, 0], ![3427, 149, 0]], ![![0, 149, 0], ![0, 23, 1]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![23, 1, 0], ![0, 0, 0]]], ![![![149, -22, -1], ![149, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-149, 23, 1]] ![![149, 0, 0], ![-24, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3576, 149, 0]], ![![-22201, 3427, 149], ![1937, -447, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-24, 1, 0]]], ![![![-149, 23, 1]], ![![13, -3, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![17, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![17, 1, 0]] 
 ![![151, 0, 0], ![17, 1, 0], ![13, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![17, 1, 0], ![0, 17, 1], ![-1639, 254, 18]]]
  hmulB := by decide  
  f := ![![![1191, 70, 0], ![-10570, 0, 0]], ![![119, 7, 0], ![-1056, 0, 0]], ![![87, 5, 0], ![-772, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 151, 0], ![-13, 0, 151]], ![![0, 1, 0], ![-2, 17, 1], ![-41, 254, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![19, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![19, 1, 0]] 
 ![![151, 0, 0], ![19, 1, 0], ![92, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![19, 1, 0], ![0, 19, 1], ![-1639, 254, 20]]]
  hmulB := by decide  
  f := ![![![115, 6, 0], ![-906, 0, 0]], ![![-19, -1, 0], ![152, 0, 0]], ![![60, 3, 0], ![-472, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 151, 0], ![-92, 0, 151]], ![![0, 1, 0], ![-3, 19, 1], ![-55, 254, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-37, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-37, 1, 0]] 
 ![![151, 0, 0], ![114, 1, 0], ![141, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-37, 1, 0], ![0, -37, 1], ![-1639, 254, -36]]]
  hmulB := by decide  
  f := ![![![2406, -65, 0], ![9815, 0, 0]], ![![1814, -49, 0], ![7400, 0, 0]], ![![2230, -60, 0], ![9097, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 151, 0], ![-141, 0, 151]], ![![-1, 1, 0], ![27, -37, 1], ![-169, 254, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![17, 1, 0]] ![![151, 0, 0], ![19, 1, 0]]
  ![![151, 0, 0], ![-130, 36, 1]] where
 M := ![![![22801, 0, 0], ![2869, 151, 0]], ![![2567, 151, 0], ![323, 36, 1]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-130, 36, 1]] ![![151, 0, 0], ![-37, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5587, 151, 0]], ![![-19630, 5436, 151], ![3171, -1208, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-37, 1, 0]]], ![![![-130, 36, 1]], ![![21, -8, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [37, 31, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 65, 20], [111, 91, 137], [0, 1]]
 g := ![![[34, 55, 105], [127, 140], [84, 94, 132], [139, 144, 110], [69, 88, 130], [109, 1], []], ![[84, 76, 5, 125], [60, 132], [33, 120, 57, 77], [25, 31, 75, 149], [85, 14, 7, 135], [128, 117], [42, 86]], ![[44, 32, 153, 85], [100, 40], [100, 43, 20, 23], [27, 136, 59, 96], [15, 49, 147, 43], [68, 143], [82, 86]]]
 h' := ![![[155, 65, 20], [93, 44, 24], [32, 72, 53], [38, 51, 140], [116, 146, 96], [49, 38, 75], [0, 0, 1], [0, 1]], ![[111, 91, 137], [14, 3, 81], [6, 52, 140], [67, 125, 101], [17, 103, 38], [60, 77, 49], [20, 123, 91], [155, 65, 20]], ![[0, 1], [58, 110, 52], [33, 33, 121], [110, 138, 73], [100, 65, 23], [101, 42, 33], [24, 34, 65], [111, 91, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156, 134], []]
 b := ![[], [138, 50, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [37, 31, 48, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72750346, -23192982, 1846948]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![463378, -147726, 11764]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [11, 9, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 112, 8], [34, 50, 155], [0, 1]]
 g := ![![[126, 154, 60], [147, 55, 93], [156, 62], [40, 10], [19, 133], [13, 115, 1], []], ![[137, 77, 14, 114], [144, 72, 39, 52], [60, 38], [69, 111], [99, 93], [87, 19, 31, 114], [24, 64]], ![[48, 120, 82, 100], [29, 21, 9, 56], [27, 60], [147, 65], [96, 39], [122, 143, 113, 56], [40, 64]]]
 h' := ![![[81, 112, 8], [13, 111, 68], [75, 75, 16], [18, 137, 15], [28, 136, 93], [20, 85, 123], [0, 0, 1], [0, 1]], ![[34, 50, 155], [34, 121, 50], [137, 38, 96], [109, 27, 53], [85, 104, 33], [14, 107, 147], [103, 109, 50], [81, 112, 8]], ![[0, 1], [152, 94, 45], [63, 50, 51], [94, 162, 95], [9, 86, 37], [24, 134, 56], [64, 54, 112], [34, 50, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 118], []]
 b := ![[], [2, 50, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [11, 9, 48, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3404744, 1177512, -108884]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20888, 7224, -668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [157, 4, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 111, 118], [25, 55, 49], [0, 1]]
 g := ![![[79, 59, 121], [67, 159, 108], [148, 114, 24], [152, 112], [138, 27], [62, 147, 1], []], ![[76, 107, 10, 153], [80, 88, 148, 17], [134, 47, 161, 129], [52, 54], [15, 63], [63, 115, 121, 71], [53, 63]], ![[133, 70, 101, 121], [80, 92, 83, 84], [143, 132, 70, 133], [92, 154], [53, 65], [33, 71, 40, 24], [122, 63]]]
 h' := ![![[122, 111, 118], [2, 14, 11], [144, 42, 129], [117, 159, 109], [10, 141, 121], [119, 53, 19], [0, 0, 1], [0, 1]], ![[25, 55, 49], [89, 136, 86], [28, 163, 27], [82, 15, 41], [49, 53, 80], [20, 33, 118], [50, 114, 55], [122, 111, 118]], ![[0, 1], [106, 17, 70], [55, 129, 11], [121, 160, 17], [161, 140, 133], [93, 81, 30], [8, 53, 111], [25, 55, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 31], []]
 b := ![[], [104, 84, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [157, 4, 20, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61390202, 20429611, -1654302]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-367606, 122333, -9906]
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



lemma PB170I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 169 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 169 (by omega)

def PB170I3 : PrimesBelowBoundCertificateInterval O 137 169 170 where
  m := 6
  g := ![1, 3, 3, 1, 1, 1]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB170I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
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
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
  β := ![I149N0, I149N1, I149N2, I151N0, I151N1, I151N2]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N0, I151N1, I151N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
