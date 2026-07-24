
import IdealArithmetic.Examples.NF3_1_439052_1.RI3_1_439052_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![26, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![26, 1, 0]] 
 ![![139, 0, 0], ![26, 1, 0], ![10, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![26, 1, 0], ![1, 26, 2], ![-272, 54, 27]]]
  hmulB := by decide  
  f := ![![![-4950, -137501, -10578], ![-1807, 735171, 0]], ![![-937, -25712, -1978], ![-277, 137471, 0]], ![![-378, -9893, -761], ![-13, 52890, 0]]]
  g := ![![![1, 0, 0], ![-26, 139, 0], ![-10, 0, 139]], ![![0, 1, 0], ![-5, 26, 2], ![-14, 54, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-16, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-16, 1, 0]] 
 ![![139, 0, 0], ![123, 1, 0], ![81, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-16, 1, 0], ![1, -16, 2], ![-272, 54, -15]]]
  hmulB := by decide  
  f := ![![![-2415, 39931, -4992], ![695, 346944, 0]], ![![-2143, 35324, -4416], ![557, 306912, 0]], ![![-1405, 23269, -2909], ![425, 202176, 0]]]
  g := ![![![1, 0, 0], ![-123, 139, 0], ![-81, 0, 139]], ![![-1, 1, 0], ![13, -16, 2], ![-41, 54, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58, -7, -2]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![58, -7, -2]] 
 ![![139, 0, 0], ![128, 1, 0], ![79, 0, 1]] where
  M :=![![![58, -7, -2], ![537, -50, -16], ![2122, -160, -57]]]
  hmulB := by decide  
  f := ![![![-290, 79, -12]], ![![-243, 66, -10]], ![![-310, 85, -13]]]
  g := ![![![8, -7, -2], ![59, -50, -16], ![195, -160, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![26, 1, 0]] ![![139, 0, 0], ![-16, 1, 0]]
  ![![-290, 79, -12]] where
 M := ![![![19321, 0, 0], ![-2224, 139, 0]], ![![3614, 139, 0], ![-415, 10, 2]]]
 hmul := by decide  
 g := ![![![![8062, -973, -278]], ![![-391, 62, 16]]], ![![![2045, -232, -68]], ![![-104, 15, 4]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-290, 79, -12]] ![![58, -7, -2]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-11, -34, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-11, -34, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![138, 115, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-11, -34, 1], ![-306, 43, -67], ![9139, -1945, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-138, -115, 149]], ![![-1, -1, 1], ![60, 52, -67], ![53, -20, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [134, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 148], [0, 1]]
 g := ![![[2, 121], [145], [43, 121], [80], [12, 28], [6], [1]], ![[56, 28], [145], [97, 28], [80], [107, 121], [6], [1]]]
 h' := ![![[30, 148], [106, 11], [49, 88], [75, 138], [31, 26], [17, 37], [15, 30], [0, 1]], ![[0, 1], [138, 138], [7, 61], [43, 11], [66, 123], [84, 112], [21, 119], [30, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [14, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [134, 119, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1507, -337, -12]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 7, -12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![67, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![67, 1, 0]] 
 ![![149, 0, 0], ![67, 1, 0], ![140, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![67, 1, 0], ![1, 67, 2], ![-272, 54, 68]]]
  hmulB := by decide  
  f := ![![![-11776, -1184003, -35346], ![-13112, 2633277, 0]], ![![-5333, -532343, -15892], ![-5810, 1183954, 0]], ![![-11062, -1112486, -33211], ![-12326, 2474220, 0]]]
  g := ![![![1, 0, 0], ![-67, 149, 0], ![-140, 0, 149]], ![![0, 1, 0], ![-32, 67, 2], ![-90, 54, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-11, -34, 1]] ![![149, 0, 0], ![67, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![9983, 149, 0]], ![![-1639, -5066, 149], ![-1043, -2235, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![67, 1, 0]]], ![![![-11, -34, 1]], ![![-7, -15, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-76, -53, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-76, -53, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![75, 98, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-76, -53, 1], ![-325, -22, -105], ![14307, -2971, -75]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -98, 151]], ![![-1, -1, 1], ![50, 68, -105], ![132, 29, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [6, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 150], [0, 1]]
 g := ![![[8, 86], [2, 21], [99, 5], [44], [17, 43], [39], [1]], ![[108, 65], [51, 130], [10, 146], [44], [67, 108], [39], [1]]]
 h' := ![![[103, 150], [139, 29], [10, 126], [23, 96], [49, 78], [104, 63], [145, 103], [0, 1]], ![[0, 1], [106, 122], [2, 25], [96, 55], [80, 73], [100, 88], [33, 48], [103, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [27, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [6, 48, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2825, -3909, 1598]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-775, -1063, 1598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-46, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-46, 1, 0]] 
 ![![151, 0, 0], ![105, 1, 0], ![75, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-46, 1, 0], ![1, -46, 2], ![-272, 54, -45]]]
  hmulB := by decide  
  f := ![![![11187, -618191, 26880], ![-7399, -2029440, 0]], ![![7782, -429836, 18690], ![-5133, -1411095, 0]], ![![5579, -307049, 13351], ![-3601, -1008000, 0]]]
  g := ![![![1, 0, 0], ![-105, 151, 0], ![-75, 0, 151]], ![![-1, 1, 0], ![31, -46, 2], ![-17, 54, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-76, -53, 1]] ![![151, 0, 0], ![-46, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-6946, 151, 0]], ![![-11476, -8003, 151], ![3171, 2416, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-46, 1, 0]]], ![![![-76, -53, 1]], ![![21, 16, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96, -3, -2]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![96, -3, -2]] 
 ![![157, 0, 0], ![0, 157, 0], ![109, 80, 1]] where
  M :=![![![96, -3, -2], ![541, -12, -8], ![1034, 56, -15]]]
  hmulB := by decide  
  f := ![![![-4, 1, 0]], ![![1, -4, 2]], ![![-4, -1, 1]]]
  g := ![![![2, 1, -2], ![9, 4, -8], ![17, 8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [71, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 156], [0, 1]]
 g := ![![[155, 115], [27], [75, 113], [35, 49], [45, 121], [68], [1]], ![[0, 42], [27], [107, 44], [85, 108], [114, 36], [68], [1]]]
 h' := ![![[142, 156], [136, 30], [13, 59], [27, 120], [102, 150], [56, 11], [86, 142], [0, 1]], ![[0, 1], [0, 127], [70, 98], [111, 37], [50, 7], [48, 146], [154, 15], [142, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [120, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [71, 15, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-435578, -482047, 242684]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-171262, -126731, 242684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![157, 0, 0], ![153, 1, 0], ![71, 0, 1]] where
  M :=![![![-4, 1, 0], ![1, -4, 2], ![-272, 54, -3]]]
  hmulB := by decide  
  f := ![![![96, -3, -2]], ![![97, -3, -2]], ![![50, -1, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 2], ![-53, 54, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![96, -3, -2]] ![![-4, 1, 0]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-692, 193, -30]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-692, 193, -30]] 
 ![![163, 0, 0], ![0, 163, 0], ![110, 162, 1]] where
  M :=![![![-692, 193, -30], ![8353, -2312, 356], ![-49226, 13692, -2119]]]
  hmulB := by decide  
  f := ![![![-152, 11, 4]], ![![-1077, 64, 26]], ![![-1194, 72, 29]]]
  g := ![![![16, 31, -30], ![-189, -368, 356], ![1128, 2190, -2119]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [156, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 162], [0, 1]]
 g := ![![[39, 93], [135, 21], [155], [134], [81], [15, 38], [1]], ![[0, 70], [0, 142], [155], [134], [81], [120, 125], [1]]]
 h' := ![![[110, 162], [130, 147], [132, 64], [158, 36], [19, 42], [105, 9], [7, 110], [0, 1]], ![[0, 1], [0, 16], [0, 99], [43, 127], [75, 121], [117, 154], [45, 53], [110, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [56, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [156, 53, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50, -3216, 1097]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-740, -1110, 1097]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152, 11, 4]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-152, 11, 4]] 
 ![![163, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-152, 11, 4], ![-1077, 64, 26], ![-3428, 158, 75]]]
  hmulB := by decide  
  f := ![![![-692, 193, -30]], ![![47, -13, 2]], ![![-302, 84, -13]]]
  g := ![![![-1, 11, 4], ![-7, 64, 26], ![-22, 158, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-692, 193, -30]] ![![-152, 11, 4]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![22, 32, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![22, 32, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![22, 32, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![22, 32, 1], ![-240, 76, 65], ![-8813, 1619, 108]]]
  hmulB := by decide  
  f := ![![![-21, -32, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -32, 167]], ![![0, 0, 1], ![-10, -12, 65], ![-67, -11, 108]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [142, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 166], [0, 1]]
 g := ![![[96, 93], [57, 7], [57, 100], [65], [75], [113, 3], [1]], ![[17, 74], [157, 160], [78, 67], [65], [75], [132, 164], [1]]]
 h' := ![![[62, 166], [89, 107], [89, 72], [102, 10], [67, 137], [153, 24], [25, 62], [0, 1]], ![[0, 1], [43, 60], [44, 95], [54, 157], [44, 30], [138, 143], [28, 105], [62, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [46, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [142, 105, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1485, -323, 16]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -5, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-65, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-65, 1, 0]] 
 ![![167, 0, 0], ![102, 1, 0], ![59, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-65, 1, 0], ![1, -65, 2], ![-272, 54, -64]]]
  hmulB := by decide  
  f := ![![![14851, -1307394, 40230], ![-13527, -3359205, 0]], ![![9101, -798476, 24570], ![-8182, -2051595, 0]], ![![5267, -461894, 14213], ![-4727, -1186785, 0]]]
  g := ![![![1, 0, 0], ![-102, 167, 0], ![-59, 0, 167]], ![![-1, 1, 0], ![39, -65, 2], ![-12, 54, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![22, 32, 1]] ![![167, 0, 0], ![-65, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-10855, 167, 0]], ![![3674, 5344, 167], ![-1670, -2004, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-65, 1, 0]]], ![![![22, 32, 1]], ![![-10, -12, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [133, 113, 170, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 147, 109], [165, 25, 64], [0, 1]]
 g := ![![[143, 108, 148], [155, 140], [75, 60, 51], [65, 116, 106], [157, 160], [69, 3, 1], []], ![[30, 142, 80, 122], [70, 96], [38, 92, 140, 116], [90, 74, 118, 57], [134, 119], [9, 58, 48, 136], [46, 117]], ![[123, 112, 29, 148], [115, 149], [121, 86, 159, 77], [60, 111, 91, 33], [96, 60], [10, 28, 105, 14], [91, 117]]]
 h' := ![![[11, 147, 109], [166, 93, 54], [59, 5, 60], [5, 25, 140], [116, 79, 25], [165, 108, 81], [0, 0, 1], [0, 1]], ![[165, 25, 64], [169, 137, 69], [134, 37, 142], [96, 28, 170], [13, 106, 67], [169, 73, 130], [58, 121, 25], [11, 147, 109]], ![[0, 1], [142, 116, 50], [127, 131, 144], [57, 120, 36], [48, 161, 81], [35, 165, 135], [71, 52, 147], [165, 25, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 60], []]
 b := ![[], [112, 24, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [133, 113, 170, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16954346, 2087591, 591660]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98002, 12067, 3420]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2840, 789, -122]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-2840, 789, -122]] 
 ![![179, 0, 0], ![0, 179, 0], ![170, 174, 1]] where
  M :=![![![-2840, 789, -122], ![33973, -9428, 1456], ![-201310, 55904, -8639]]]
  hmulB := by decide  
  f := ![![![-292, 23, 8]], ![![-2153, 140, 54]], ![![-2410, 160, 61]]]
  g := ![![![100, 123, -122], ![-1193, -1468, 1456], ![7080, 8710, -8639]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [153, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 178], [0, 1]]
 g := ![![[62, 117], [10, 169], [177], [15], [173, 89], [53, 1], [1]], ![[0, 62], [0, 10], [177], [15], [83, 90], [54, 178], [1]]]
 h' := ![![[1, 178], [81, 98], [166, 13], [24, 101], [23, 33], [125, 39], [26, 1], [0, 1]], ![[0, 1], [0, 81], [0, 166], [125, 78], [56, 146], [164, 140], [27, 178], [1, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [104, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [153, 178, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3725, -1431, -36]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 27, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-292, 23, 8]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-292, 23, 8]] 
 ![![179, 0, 0], ![9, 1, 0], ![139, 0, 1]] where
  M :=![![![-292, 23, 8], ![-2153, 140, 54], ![-7128, 370, 163]]]
  hmulB := by decide  
  f := ![![![-2840, 789, -122]], ![![47, -13, 2]], ![![-3330, 925, -143]]]
  g := ![![![-9, 23, 8], ![-61, 140, 54], ![-185, 370, 163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-2840, 789, -122]] ![![-292, 23, 8]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-68, -54, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-68, -54, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![113, 127, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-68, -54, 1], ![-326, -14, -107], ![14579, -3025, -68]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -127, 181]], ![![-1, -1, 1], ![65, 75, -107], ![123, 31, -68]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [97, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 180], [0, 1]]
 g := ![![[139, 125], [165], [15, 147], [136], [149, 161], [97, 138], [1]], ![[55, 56], [165], [145, 34], [136], [119, 20], [123, 43], [1]]]
 h' := ![![[92, 180], [153, 135], [174, 105], [26, 50], [27, 91], [3, 60], [84, 92], [0, 1]], ![[0, 1], [84, 46], [60, 76], [101, 131], [73, 90], [93, 121], [41, 89], [92, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [59, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [97, 89, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3640, -1219, 1246]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-798, -881, 1246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-74, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-74, 1, 0]] 
 ![![181, 0, 0], ![107, 1, 0], ![68, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-74, 1, 0], ![1, -74, 2], ![-272, 54, -73]]]
  hmulB := by decide  
  f := ![![![-1007, 107442, -2904], ![1086, 262812, 0]], ![![-561, 63488, -1716], ![725, 155298, 0]], ![![-382, 40365, -1091], ![399, 98736, 0]]]
  g := ![![![1, 0, 0], ![-107, 181, 0], ![-68, 0, 181]], ![![-1, 1, 0], ![43, -74, 2], ![-6, 54, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-68, -54, 1]] ![![181, 0, 0], ![-74, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-13394, 181, 0]], ![![-12308, -9774, 181], ![4706, 3982, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-74, 1, 0]]], ![![![-68, -54, 1]], ![![26, 22, -1]]]]
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


lemma PB188I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 187 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 187 (by omega)

def PB188I3 : PrimesBelowBoundCertificateInterval O 137 187 188 where
  m := 9
  g := ![3, 2, 2, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB188I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I157N1, I163N1, I167N1, I179N1, I181N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [I157N1], [I163N1], [I167N1], [], [I179N1], [I181N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
