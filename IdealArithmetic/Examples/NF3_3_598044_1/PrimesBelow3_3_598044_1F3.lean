
import IdealArithmetic.Examples.NF3_3_598044_1.RI3_3_598044_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [85, 27, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 103, 131], [4, 35, 8], [0, 1]]
 g := ![![[57, 74, 9], [85, 57, 117], [104, 11], [26, 84, 44], [40, 49], [24, 1], []], ![[54, 120, 118, 28], [123, 68, 28, 124], [63, 31], [14, 21, 31, 29], [60, 6], [89, 113], [27, 64]], ![[50, 49, 67, 133], [4, 2, 13, 119], [106, 7], [105, 75, 110, 18], [61, 63], [58, 45], [11, 64]]]
 h' := ![![[20, 103, 131], [3, 69, 3], [113, 99, 123], [14, 28, 17], [15, 92, 34], [45, 101, 132], [0, 0, 1], [0, 1]], ![[4, 35, 8], [7, 126, 109], [26, 30, 38], [51, 21, 93], [114, 136, 37], [40, 4, 59], [51, 36, 35], [20, 103, 131]], ![[0, 1], [24, 83, 27], [62, 10, 117], [71, 90, 29], [134, 50, 68], [71, 34, 87], [54, 103, 103], [4, 35, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 24], []]
 b := ![[], [128, 116, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [85, 27, 115, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4726, -35167, -6116]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, -253, -44]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![280, 1, -7]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![280, 1, -7]] 
 ![![149, 0, 0], ![49, 1, 0], ![116, 0, 1]] where
  M :=![![![280, 1, -7], ![42, -13, 2], ![-27, 63, -14]]]
  hmulB := by decide  
  f := ![![![56, -427, -89]], ![![22, -168, -35]], ![![59, -451, -94]]]
  g := ![![![7, 1, -7], ![3, -13, 2], ![-10, 63, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19816, -33, -471]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![19816, -33, -471]] 
 ![![149, 0, 0], ![110, 1, 0], ![4, 0, 1]] where
  M :=![![![19816, -33, -471], ![2826, 1, -66], ![-1215, 27, 34]]]
  hmulB := by decide  
  f := ![![![-1816, 11595, -2649]], ![![-1234, 7879, -1800]], ![![-569, 3633, -830]]]
  g := ![![![170, -33, -471], ![20, 1, -66], ![-29, 27, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13040, 5975, -1703]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![13040, 5975, -1703]] 
 ![![149, 0, 0], ![138, 1, 0], ![94, 0, 1]] where
  M :=![![![13040, 5975, -1703], ![10218, -52511, 11950], ![-40959, 256059, -58486]]]
  hmulB := by decide  
  f := ![![![-11253296, 86614627, 18024983]], ![![-11148354, 85806907, 17856892]], ![![-10224313, 78694727, 16376808]]]
  g := ![![![-4372, 5975, -1703], ![41164, -52511, 11950], ![-200533, 256059, -58486]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![280, 1, -7]] ![![19816, -33, -471]]
  ![![5559811, -9428, -132184]] where
 M := ![![![5559811, -9428, -132184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![5559811, -9428, -132184]] ![![13040, 5975, -1703]]
  ![![149, 0, 0]] where
 M := ![![![77817724592, -131958423, -1850109309]]]
 hmul := by decide  
 g := ![![![![522266608, -885627, -12416841]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![160, -1235, -257]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![160, -1235, -257]] 
 ![![151, 0, 0], ![30, 1, 0], ![139, 0, 1]] where
  M :=![![![160, -1235, -257], ![1542, -11869, -2470], ![6639, -51099, -10634]]]
  hmulB := by decide  
  f := ![![![-416, 547, -117]], ![![-78, 77, -16]], ![![-407, 658, -143]]]
  g := ![![![483, -1235, -257], ![4642, -11869, -2470], ![19985, -51099, -10634]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 15, -3]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-20, 15, -3]] 
 ![![151, 0, 0], ![54, 1, 0], ![25, 0, 1]] where
  M :=![![![-20, 15, -3], ![18, -131, 30], ![-99, 639, -146]]]
  hmulB := by decide  
  f := ![![![-44, 273, 57]], ![![-18, 115, 24]], ![![-17, 120, 25]]]
  g := ![![![-5, 15, -3], ![42, -131, 30], ![-205, 639, -146]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 2, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-19, 2, 0]] 
 ![![151, 0, 0], ![66, 1, 0], ![54, 0, 1]] where
  M :=![![![-19, 2, 0], ![0, -17, 4], ![-12, 84, -19]]]
  hmulB := by decide  
  f := ![![![-13, 38, 8]], ![![-6, 19, 4]], ![![-6, 24, 5]]]
  g := ![![![-1, 2, 0], ![6, -17, 4], ![-30, 84, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![160, -1235, -257]] ![![-20, 15, -3]]
  ![![13, -38, -8]] where
 M := ![![![13, -38, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![13, -38, -8]] ![![-19, 2, 0]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [116, 29, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 86, 80], [25, 70, 77], [0, 1]]
 g := ![![[42, 65, 148], [41, 143], [14, 78, 86], [3, 12, 154], [145, 80, 109], [20, 1], []], ![[135, 78, 52, 50], [112, 11], [136, 5], [105, 37, 59, 78], [115, 154, 24, 91], [7, 33], [146, 120]], ![[66, 134, 55, 7], [114, 10], [41, 28, 109, 28], [0, 14, 70, 2], [70, 150, 19, 28], [124, 17], [149, 120]]]
 h' := ![![[152, 86, 80], [44, 149, 73], [103, 23, 65], [123, 61, 20], [136, 143, 132], [35, 89, 57], [0, 0, 1], [0, 1]], ![[25, 70, 77], [72, 112, 74], [87, 88, 110], [90, 39], [23, 6, 113], [114, 91, 120], [45, 140, 70], [152, 86, 80]], ![[0, 1], [16, 53, 10], [44, 46, 139], [52, 57, 137], [54, 8, 69], [35, 134, 137], [140, 17, 86], [25, 70, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 148], []]
 b := ![[], [37, 37, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [116, 29, 137, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2669, 107545, 203158]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, 685, 1294]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [137, 25, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 125, 66], [162, 37, 97], [0, 1]]
 g := ![![[96, 149, 131], [153, 6, 69], [116, 146], [9, 134], [73, 55], [30, 50, 1], []], ![[51, 107, 76, 13], [93, 146, 74, 70], [140, 81], [162, 58], [122, 152], [147, 27, 6, 52], [69, 118]], ![[56, 137, 124, 90], [30, 121, 115, 61], [131, 133], [16, 126], [15, 49], [124, 77, 73, 51], [38, 118]]]
 h' := ![![[51, 125, 66], [66, 32, 91], [142, 60, 118], [95, 126, 31], [26, 62, 42], [128, 61, 113], [0, 0, 1], [0, 1]], ![[162, 37, 97], [11, 67, 100], [49, 50, 13], [141, 145, 9], [2, 142, 104], [116, 126, 57], [157, 75, 37], [51, 125, 66]], ![[0, 1], [57, 64, 135], [76, 53, 32], [147, 55, 123], [100, 122, 17], [6, 139, 156], [11, 88, 125], [162, 37, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 5], []]
 b := ![[], [65, 6, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [137, 25, 113, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![198860, 489, -2934]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1220, 3, -18]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1516, -17, -39]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1516, -17, -39]] 
 ![![167, 0, 0], ![0, 167, 0], ![111, 9, 1]] where
  M :=![![![1516, -17, -39], ![234, -139, -34], ![-15, -597, -122]]]
  hmulB := by decide  
  f := ![![![20, -127, 29]], ![![-174, 1111, -254]], ![![9, -57, 13]]]
  g := ![![![35, 2, -39], ![24, 1, -34], ![81, 3, -122]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [53, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 166], [0, 1]]
 g := ![![[122, 8], [7, 121], [55, 154], [6], [133], [144, 38], [1]], ![[164, 159], [16, 46], [112, 13], [6], [133], [93, 129], [1]]]
 h' := ![![[47, 166], [130, 26], [91, 11], [113, 133], [127, 29], [50, 48], [114, 47], [0, 1]], ![[0, 1], [16, 141], [107, 156], [18, 34], [154, 138], [135, 119], [152, 120], [47, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [41, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [53, 120, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129, 525, 448]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-297, -21, 448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 127, -29]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-20, 127, -29]] 
 ![![167, 0, 0], ![149, 1, 0], ![14, 0, 1]] where
  M :=![![![-20, 127, -29], ![174, -1111, 254], ![-849, 5421, -1238]]]
  hmulB := by decide  
  f := ![![![-1516, 17, 39]], ![![-1354, 16, 35]], ![![-127, 5, 4]]]
  g := ![![![-111, 127, -29], ![971, -1111, 254], ![-4738, 5421, -1238]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1516, -17, -39]] ![![-20, 127, -29]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB172I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 171 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 171 (by omega)

def PB172I3 : PrimesBelowBoundCertificateInterval O 137 171 172 where
  m := 6
  g := ![1, 3, 3, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB172I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
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
    · exact ![27889, 167]
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
      exact NI167N1
  β := ![I149N0, I149N1, I149N2, I151N0, I151N1, I151N2, I167N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N0, I151N1, I151N2], [], [], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
