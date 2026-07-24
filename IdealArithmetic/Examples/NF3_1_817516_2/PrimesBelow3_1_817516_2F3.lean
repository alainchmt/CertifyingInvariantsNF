
import IdealArithmetic.Examples.NF3_1_817516_2.RI3_1_817516_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![5, 34, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![5, 34, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![5, 34, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![5, 34, 1], ![-71, 101, 236], ![-5761, -227, -68]]]
  hmulB := by decide  
  f := ![![![-4, -34, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -34, 139]], ![![0, 0, 1], ![-9, -57, 236], ![-39, 15, -68]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [69, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 138], [0, 1]]
 g := ![![[97, 137], [15, 100], [38], [25, 127], [127], [24], [1]], ![[0, 2], [0, 39], [38], [138, 12], [127], [24], [1]]]
 h' := ![![[118, 138], [77, 50], [71, 10], [82, 49], [118, 108], [47, 31], [70, 118], [0, 1]], ![[0, 1], [0, 89], [0, 129], [26, 90], [74, 31], [91, 108], [94, 21], [118, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [58, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [69, 21, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3696, -1475, -350]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 75, -350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![42, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![42, 1, 0]] 
 ![![139, 0, 0], ![42, 1, 0], ![68, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![42, 1, 0], ![3, 45, 7], ![-173, -6, 40]]]
  hmulB := by decide  
  f := ![![![985, 17276, 2688], ![556, -53376, 0]], ![![306, 5219, 812], ![140, -16124, 0]], ![![500, 8452, 1315], ![212, -26112, 0]]]
  g := ![![![1, 0, 0], ![-42, 139, 0], ![-68, 0, 139]], ![![0, 1, 0], ![-17, 45, 7], ![-19, -6, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![5, 34, 1]] ![![139, 0, 0], ![42, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5838, 139, 0]], ![![695, 4726, 139], ![139, 1529, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![42, 1, 0]]], ![![![5, 34, 1]], ![![1, 11, 2]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [33, 144, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 90, 80], [53, 58, 69], [0, 1]]
 g := ![![[147, 59, 145], [15, 86], [42, 18, 67], [141, 120], [70, 92, 121], [119, 1], []], ![[89, 89, 37, 86], [22, 80], [132, 22, 40, 125], [64, 113], [46, 114, 102, 88], [78, 86], [8, 142]], ![[64, 123, 90, 124], [126, 53], [119, 14, 119, 86], [127, 86], [96, 116, 19, 29], [10, 54], [19, 142]]]
 h' := ![![[66, 90, 80], [40, 75, 88], [104, 38, 91], [78, 49, 118], [74, 123, 57], [96, 115, 11], [0, 0, 1], [0, 1]], ![[53, 58, 69], [36, 109, 78], [100, 5, 123], [130, 80, 36], [56, 99, 34], [101, 77, 4], [69, 82, 58], [66, 90, 80]], ![[0, 1], [96, 114, 132], [126, 106, 84], [146, 20, 144], [145, 76, 58], [95, 106, 134], [96, 67, 90], [53, 58, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 20], []]
 b := ![[], [97, 47, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [33, 144, 30, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28966345, 1382869, 166284]
  a := ![8, 6, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![194405, 9281, 1116]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-32, 21, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-32, 21, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![119, 21, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-32, 21, 1], ![-110, 25, 145], ![-3512, -149, -79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -21, 151]], ![![-1, 0, 1], ![-115, -20, 145], ![39, 10, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [60, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 150], [0, 1]]
 g := ![![[22, 11], [46, 128], [136, 40], [29], [0, 76], [11], [1]], ![[149, 140], [55, 23], [35, 111], [29], [95, 75], [11], [1]]]
 h' := ![![[39, 150], [109, 39], [145, 85], [72, 74], [0, 28], [71, 128], [91, 39], [0, 1]], ![[0, 1], [120, 112], [138, 66], [89, 77], [35, 123], [80, 23], [102, 112], [39, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [75, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [60, 112, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-867522, -511575, -93303]
  a := ![-67, -66, -135]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67785, 9588, -93303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![6, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![6, 1, 0]] 
 ![![151, 0, 0], ![6, 1, 0], ![79, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![6, 1, 0], ![3, 9, 7], ![-173, -6, 4]]]
  hmulB := by decide  
  f := ![![![3391, 10204, 7938], ![302, -171234, 0]], ![![129, 404, 315], ![152, -6795, 0]], ![![1771, 5338, 4153], ![236, -89586, 0]]]
  g := ![![![1, 0, 0], ![-6, 151, 0], ![-79, 0, 151]], ![![0, 1, 0], ![-4, 9, 7], ![-3, -6, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-32, 21, 1]] ![![151, 0, 0], ![6, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![906, 151, 0]], ![![-4832, 3171, 151], ![-302, 151, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![6, 1, 0]]], ![![![-32, 21, 1]], ![![-2, 1, 1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [153, 112, 136, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36, 42], [7, 120, 115], [0, 1]]
 g := ![![[82, 106, 81], [65, 141], [32, 84, 57], [82, 104, 153], [149, 68, 68], [21, 1], []], ![[53, 22, 149, 31], [21, 58], [14, 115, 20, 12], [126, 128, 132, 140], [64, 132, 106, 71], [49, 113], [33, 37]], ![[7, 151, 1, 81], [17, 13], [76, 146, 86, 56], [91, 55, 39, 108], [66, 67, 146, 1], [30, 40], [117, 37]]]
 h' := ![![[14, 36, 42], [2, 112, 9], [128, 88, 112], [14, 106, 34], [125, 60, 101], [84, 7, 15], [0, 0, 1], [0, 1]], ![[7, 120, 115], [126, 12, 132], [102, 32, 23], [90, 38, 54], [24, 117, 39], [78, 146, 53], [14, 129, 120], [14, 36, 42]], ![[0, 1], [101, 33, 16], [87, 37, 22], [122, 13, 69], [10, 137, 17], [38, 4, 89], [46, 28, 36], [7, 120, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 81], []]
 b := ![[], [49, 67, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [153, 112, 136, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29918391, -2925852, -256224]
  a := ![-8, -7, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-190563, -18636, -1632]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![82, -18, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![82, -18, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![82, 145, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![82, -18, 1], ![-227, 22, -128], ![3235, 85, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -145, 163]], ![![0, -1, 1], ![63, 114, -128], ![-37, -100, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [106, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 162], [0, 1]]
 g := ![![[89, 47], [144, 55], [111], [25], [24], [11, 74], [1]], ![[51, 116], [103, 108], [111], [25], [24], [24, 89], [1]]]
 h' := ![![[20, 162], [58, 84], [10, 50], [23, 130], [37, 158], [138, 26], [57, 20], [0, 1]], ![[0, 1], [108, 79], [32, 113], [15, 33], [100, 5], [6, 137], [131, 143], [20, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [135, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [106, 143, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4025, -1963, -1204]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![581, 1059, -1204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-35, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-35, 1, 0]] 
 ![![163, 0, 0], ![128, 1, 0], ![50, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-35, 1, 0], ![3, -32, 7], ![-173, -6, -37]]]
  hmulB := by decide  
  f := ![![![20679, -233597, 51107], ![-5705, -1190063, 0]], ![![16220, -183428, 40131], ![-4563, -934479, 0]], ![![6360, -71656, 15677], ![-1672, -365050, 0]]]
  g := ![![![1, 0, 0], ![-128, 163, 0], ![-50, 0, 163]], ![![-1, 1, 0], ![23, -32, 7], ![15, -6, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![82, -18, 1]] ![![163, 0, 0], ![-35, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-5705, 163, 0]], ![![13366, -2934, 163], ![-3097, 652, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-35, 1, 0]]], ![![![82, -18, 1]], ![![-19, 4, -1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [47, 96, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 126, 49], [24, 40, 118], [0, 1]]
 g := ![![[144, 84, 128], [114, 51, 32], [148, 150, 84], [152, 75], [65, 31], [159, 103, 1], []], ![[141, 9, 78, 32], [86, 53, 160, 72], [68, 72, 69, 24], [55, 126], [90, 2], [105, 103, 95, 77], [133, 63]], ![[7, 118, 128, 103], [127, 94, 37, 34], [139, 2, 31, 136], [76, 19], [6, 42], [7, 58, 160, 129], [64, 63]]]
 h' := ![![[79, 126, 49], [153, 43, 104], [58, 142, 115], [58, 153, 77], [45, 36, 143], [42, 102, 96], [0, 0, 1], [0, 1]], ![[24, 40, 118], [5, 156, 88], [106, 149, 35], [19, 47, 56], [123, 98, 136], [126, 43, 154], [157, 4, 40], [79, 126, 49]], ![[0, 1], [93, 135, 142], [4, 43, 17], [166, 134, 34], [159, 33, 55], [146, 22, 84], [73, 163, 126], [24, 40, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 48], []]
 b := ![[], [4, 19, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [47, 96, 64, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7607685, -2473604, -967932]
  a := ![4, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45555, -14812, -5796]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-63, 26, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-63, 26, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![110, 26, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-63, 26, 1], ![-95, 9, 180], ![-4377, -179, -120]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-110, -26, 173]], ![![-1, 0, 1], ![-115, -27, 180], ![51, 17, -120]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [92, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 172], [0, 1]]
 g := ![![[163, 126], [29], [144, 57], [85, 84], [109], [36, 84], [1]], ![[0, 47], [29], [165, 116], [34, 89], [109], [158, 89], [1]]]
 h' := ![![[55, 172], [66, 68], [73, 95], [138, 149], [112, 118], [148, 121], [81, 55], [0, 1]], ![[0, 1], [0, 105], [108, 78], [29, 24], [28, 55], [56, 52], [165, 118], [55, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [26, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [92, 118, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6326, -2078, -1424]
  a := ![-4, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![942, 202, -1424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-7, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-7, 1, 0]] 
 ![![173, 0, 0], ![166, 1, 0], ![120, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-7, 1, 0], ![3, -4, 7], ![-173, -6, -9]]]
  hmulB := by decide  
  f := ![![![13744, -18349, 32116], ![-519, -793724, 0]], ![![13186, -17605, 30814], ![-518, -761546, 0]], ![![9536, -12728, 22277], ![-296, -550560, 0]]]
  g := ![![![1, 0, 0], ![-166, 173, 0], ![-120, 0, 173]], ![![-1, 1, 0], ![-1, -4, 7], ![11, -6, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-63, 26, 1]] ![![173, 0, 0], ![-7, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-1211, 173, 0]], ![![-10899, 4498, 173], ![346, -173, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-7, 1, 0]]], ![![![-63, 26, 1]], ![![2, -1, 1]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [148, 24, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 29, 135], [175, 149, 44], [0, 1]]
 g := ![![[123, 26, 116], [100, 16, 48], [105, 56], [92, 177], [88, 57, 77], [149, 50, 1], []], ![[81, 92, 156, 51], [127, 151, 46, 149], [127, 14], [120, 59], [17, 145, 17, 60], [116, 42, 56, 138], [94, 146]], ![[145, 166, 94, 163], [122, 0, 131, 94], [15, 14], [94, 142], [14, 109, 49, 122], [121, 79, 25, 130], [6, 146]]]
 h' := ![![[54, 29, 135], [57, 130, 37], [94, 22, 76], [47, 20, 134], [43, 164, 101], [144, 122, 16], [0, 0, 1], [0, 1]], ![[175, 149, 44], [111, 121, 151], [84, 27, 153], [117, 35, 112], [48, 112, 136], [130, 112, 59], [102, 32, 149], [54, 29, 135]], ![[0, 1], [30, 107, 170], [143, 130, 129], [6, 124, 112], [99, 82, 121], [24, 124, 104], [23, 147, 29], [175, 149, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 41], []]
 b := ![[], [34, 83, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [148, 24, 129, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11325867, -149107, -298214]
  a := ![6, 7, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63273, -833, -1666]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![75, -42, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![75, -42, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![75, 139, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![75, -42, 1], ![-299, -57, -296], ![7387, 229, 154]]]
  hmulB := by decide  
  f := ![![![-74, 42, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -139, 181]], ![![0, -1, 1], ![121, 227, -296], ![-23, -117, 154]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [10, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 180], [0, 1]]
 g := ![![[75, 56], [15], [156, 79], [165], [173, 39], [139, 133], [1]], ![[67, 125], [15], [93, 102], [165], [64, 142], [120, 48], [1]]]
 h' := ![![[155, 180], [86, 31], [69, 167], [44, 21], [80, 105], [58, 43], [171, 155], [0, 1]], ![[0, 1], [4, 150], [71, 14], [41, 160], [65, 76], [26, 138], [123, 26], [155, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [62, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [10, 26, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5220, -2905, -685]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![255, 510, -685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-66, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-66, 1, 0]] 
 ![![181, 0, 0], ![115, 1, 0], ![27, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-66, 1, 0], ![3, -63, 7], ![-173, -6, -68]]]
  hmulB := by decide  
  f := ![![![31045, -771034, 85680], ![-15566, -2215440, 0]], ![![19765, -489834, 54432], ![-9773, -1407456, 0]], ![![4689, -115017, 12781], ![-2163, -330480, 0]]]
  g := ![![![1, 0, 0], ![-115, 181, 0], ![-27, 0, 181]], ![![-1, 1, 0], ![39, -63, 7], ![13, -6, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![75, -42, 1]] ![![181, 0, 0], ![-66, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-11946, 181, 0]], ![![13575, -7602, 181], ![-5249, 2715, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-66, 1, 0]]], ![![![75, -42, 1]], ![![-29, 15, -2]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-65, -89, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-65, -89, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![126, 102, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-65, -89, 1], ![-440, -338, -625], ![15518, 511, 108]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -102, 191]], ![![-1, -1, 1], ![410, 332, -625], ![10, -55, 108]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [181, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 190], [0, 1]]
 g := ![![[6, 2], [19, 15], [144, 92], [52, 102], [172, 75], [33, 162], [1]], ![[126, 189], [155, 176], [125, 99], [60, 89], [88, 116], [12, 29], [1]]]
 h' := ![![[60, 190], [190, 57], [103, 145], [138, 130], [1, 22], [139, 71], [10, 60], [0, 1]], ![[0, 1], [172, 134], [17, 46], [107, 61], [175, 169], [6, 120], [172, 131], [60, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [127, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [181, 131, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52965, -7302, 1198]
  a := ![8, -2, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-513, -678, 1198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![52, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![52, 1, 0]] 
 ![![191, 0, 0], ![52, 1, 0], ![83, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![52, 1, 0], ![3, 55, 7], ![-173, -6, 50]]]
  hmulB := by decide  
  f := ![![![43537, 881013, 112140], ![16617, -3059820, 0]], ![![11835, 239831, 30527], ![4585, -832951, 0]], ![![18889, 382848, 48731], ![7332, -1329660, 0]]]
  g := ![![![1, 0, 0], ![-52, 191, 0], ![-83, 0, 191]], ![![0, 1, 0], ![-18, 55, 7], ![-21, -6, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-65, -89, 1]] ![![191, 0, 0], ![52, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![9932, 191, 0]], ![![-12415, -16999, 191], ![-3820, -4966, -573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![52, 1, 0]]], ![![![-65, -89, 1]], ![![-20, -26, -3]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [118, 115, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 45, 138], [117, 147, 55], [0, 1]]
 g := ![![[172, 144, 97], [59, 157], [47, 4], [119, 56], [155, 42], [27, 62], [1]], ![[86, 180, 107, 139], [157, 161], [164, 169], [7, 4], [43, 27], [62, 107], [44, 158, 178, 184]], ![[159, 77, 10, 151], [21, 138], [51, 121], [50, 27], [65, 95], [58, 21], [86, 189, 11, 9]]]
 h' := ![![[162, 45, 138], [95, 117, 26], [63, 18, 93], [165, 167, 2], [120, 37, 153], [123, 121, 87], [75, 78, 86], [0, 1]], ![[117, 147, 55], [146, 61, 89], [12, 115, 136], [185, 137, 180], [25, 36, 191], [9, 57, 151], [143, 74, 53], [162, 45, 138]], ![[0, 1], [141, 15, 78], [127, 60, 157], [82, 82, 11], [81, 120, 42], [80, 15, 148], [180, 41, 54], [117, 147, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 131], []]
 b := ![[], [128, 164, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [118, 115, 107, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![157524284, 4388241, -2087295]
  a := ![16, 15, 33]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![816188, 22737, -10815]
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



lemma PB256I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB256I3 : PrimesBelowBoundCertificateInterval O 137 193 256 where
  m := 11
  g := ![2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB256I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
  β := ![I139N1, I151N1, I163N1, I173N1, I181N1, I191N1]
  Il := ![[I139N1], [], [I151N1], [], [I163N1], [], [I173N1], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
