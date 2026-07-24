
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-108, 69, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-108, 69, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![31, 69, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-108, 69, 1], ![-332, -35, 70], ![-23240, 4778, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -69, 139]], ![![-1, 0, 1], ![-18, -35, 70], ![-175, 17, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [104, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 138], [0, 1]]
 g := ![![[106, 106], [25, 29], [81], [29, 129], [38], [42], [1]], ![[135, 33], [29, 110], [81], [42, 10], [38], [42], [1]]]
 h' := ![![[96, 138], [41, 84], [12, 53], [42, 9], [76, 44], [54, 49], [35, 96], [0, 1]], ![[0, 1], [43, 55], [96, 86], [72, 130], [130, 95], [32, 90], [77, 43], [96, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [138, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [104, 43, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-892, -156, 34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -18, 34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![69, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![69, 1, 0]] 
 ![![139, 0, 0], ![69, 1, 0], ![104, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![69, 1, 0], ![0, 69, 1], ![-332, 73, 70]]]
  hmulB := by decide  
  f := ![![![2002, 29, 0], ![-4031, 0, 0]], ![![966, 14, 0], ![-1945, 0, 0]], ![![1484, 21, 0], ![-2988, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 139, 0], ![-104, 0, 139]], ![![0, 1, 0], ![-35, 69, 1], ![-91, 73, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-108, 69, 1]] ![![139, 0, 0], ![69, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![9591, 139, 0]], ![![-15012, 9591, 139], ![-7784, 4726, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![69, 1, 0]]], ![![![-108, 69, 1]], ![![-56, 34, 1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [30, 148, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 88, 130], [83, 60, 19], [0, 1]]
 g := ![![[23, 2, 95], [79, 9], [36, 135, 123], [93, 80], [20, 6, 133], [138, 1], []], ![[94, 144], [30, 104], [99, 106, 34, 107], [125, 148], [40, 123, 55, 120], [116, 24], [135, 63]], ![[134, 117, 117, 17], [127, 46], [12, 78, 12, 143], [83, 132], [53, 107, 1, 30], [33, 145], [97, 63]]]
 h' := ![![[55, 88, 130], [42, 97, 63], [112, 129, 3], [57, 19, 47], [145, 119, 26], [32, 108, 122], [0, 0, 1], [0, 1]], ![[83, 60, 19], [104, 19], [109, 112, 113], [11, 8, 75], [6, 25, 44], [122, 106, 53], [18, 28, 60], [55, 88, 130]], ![[0, 1], [106, 33, 86], [108, 57, 33], [13, 122, 27], [87, 5, 79], [52, 84, 123], [105, 121, 88], [83, 60, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 123], []]
 b := ![[], [102, 50, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [30, 148, 11, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2983576, -1337573, 150192]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20024, -8977, 1008]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-90, -51, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-90, -51, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![61, 100, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-90, -51, 1], ![-332, -17, -50], ![16600, -3982, -67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -100, 151]], ![![-1, -1, 1], ![18, 33, -50], ![137, 18, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [99, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 150], [0, 1]]
 g := ![![[67, 90], [38, 74], [63, 47], [31], [86, 8], [121], [1]], ![[0, 61], [97, 77], [127, 104], [31], [23, 143], [121], [1]]]
 h' := ![![[11, 150], [13, 40], [105, 15], [144, 54], [93, 22], [87, 59], [52, 11], [0, 1]], ![[0, 1], [0, 111], [119, 136], [134, 97], [33, 129], [132, 92], [22, 140], [11, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [6, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [99, 140, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4433, -393, 61]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -43, 61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![50, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![50, 1, 0]] 
 ![![151, 0, 0], ![50, 1, 0], ![67, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![50, 1, 0], ![0, 50, 1], ![-332, 73, 51]]]
  hmulB := by decide  
  f := ![![![3001, 60, 0], ![-9060, 0, 0]], ![![950, 19, 0], ![-2868, 0, 0]], ![![1317, 26, 0], ![-3976, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 151, 0], ![-67, 0, 151]], ![![0, 1, 0], ![-17, 50, 1], ![-49, 73, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-90, -51, 1]] ![![151, 0, 0], ![50, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![7550, 151, 0]], ![![-13590, -7701, 151], ![-4832, -2567, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![50, 1, 0]]], ![![![-90, -51, 1]], ![![-32, -17, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [81, 135, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 64, 91], [96, 92, 66], [0, 1]]
 g := ![![[119, 55, 143], [16, 124], [142, 39, 51], [104, 97, 148], [152, 126, 118], [34, 1], []], ![[88, 8, 143, 107], [110, 143], [6, 48, 43, 87], [149, 135, 5, 66], [124, 30, 26, 60], [63, 143], [83, 117]], ![[78, 69, 36, 128], [56, 99], [97, 101, 36, 142], [32, 66, 113, 50], [31, 148, 101, 78], [142, 14], [108, 117]]]
 h' := ![![[95, 64, 91], [71, 85, 65], [116, 55, 76], [54, 43, 88], [91, 49, 73], [72, 39, 79], [0, 0, 1], [0, 1]], ![[96, 92, 66], [148, 68, 56], [57, 19, 65], [103, 136, 77], [92, 81, 28], [61, 119, 141], [104, 113, 92], [95, 64, 91]], ![[0, 1], [29, 4, 36], [144, 83, 16], [150, 135, 149], [23, 27, 56], [125, 156, 94], [154, 44, 64], [96, 92, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 53], []]
 b := ![[], [126, 122, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [81, 135, 123, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2444176, 818755, -55421]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15568, 5215, -353]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![18, 53, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![18, 53, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![18, 53, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![18, 53, 1], ![-332, 91, 54], ![-17928, 3610, 145]]]
  hmulB := by decide  
  f := ![![![-17, -53, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -53, 163]], ![![0, 0, 1], ![-8, -17, 54], ![-126, -25, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [40, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 162], [0, 1]]
 g := ![![[68, 53], [88, 144], [14], [77], [143], [127, 156], [1]], ![[0, 110], [97, 19], [14], [77], [143], [96, 7], [1]]]
 h' := ![![[51, 162], [66, 85], [85, 151], [112, 103], [62, 27], [136, 44], [123, 51], [0, 1]], ![[0, 1], [0, 78], [125, 12], [149, 60], [135, 136], [98, 119], [116, 112], [51, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [28, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [40, 112, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-956, -225, -35]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 10, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-54, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-54, 1, 0]] 
 ![![163, 0, 0], ![109, 1, 0], ![18, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-54, 1, 0], ![0, -54, 1], ![-332, 73, -53]]]
  hmulB := by decide  
  f := ![![![8749, -162, 0], ![26406, 0, 0]], ![![5887, -109, 0], ![17768, 0, 0]], ![![990, -18, 0], ![2988, 1, 0]]]
  g := ![![![1, 0, 0], ![-109, 163, 0], ![-18, 0, 163]], ![![-1, 1, 0], ![36, -54, 1], ![-45, 73, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![18, 53, 1]] ![![163, 0, 0], ![-54, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-8802, 163, 0]], ![![2934, 8639, 163], ![-1304, -2771, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-54, 1, 0]]], ![![![18, 53, 1]], ![![-8, -17, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [4, 17, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 93, 153], [92, 73, 14], [0, 1]]
 g := ![![[106, 0, 6], [129, 105, 98], [112, 112, 16], [61, 114], [133, 88], [154, 2, 1], []], ![[42, 114, 120, 140], [22, 140, 65, 92], [47, 8, 149, 23], [18, 127], [81, 116], [69, 92, 97, 43], [126, 29]], ![[67, 112, 88, 31], [81, 34, 166, 157], [110, 83, 73, 24], [69, 18], [166, 127], [143, 159, 20, 11], [98, 29]]]
 h' := ![![[77, 93, 153], [152, 29, 138], [53, 84, 76], [91, 10, 4], [1, 0, 75], [52, 46, 103], [0, 0, 1], [0, 1]], ![[92, 73, 14], [36, 34, 149], [152, 164, 30], [16, 88, 152], [64, 161, 131], [80, 48, 28], [81, 40, 73], [77, 93, 153]], ![[0, 1], [27, 104, 47], [13, 86, 61], [66, 69, 11], [26, 6, 128], [32, 73, 36], [56, 127, 93], [92, 73, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 136], []]
 b := ![[], [154, 41, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [4, 17, 165, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6150777, 900297, 161155]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36831, 5391, 965]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [13, 90, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 90, 112], [54, 82, 61], [0, 1]]
 g := ![![[82, 110, 57], [89, 9], [93, 35, 13], [156, 158, 52], [164, 160], [67, 26, 1], []], ![[134, 3, 139, 61], [64, 15], [126, 153, 79, 105], [40, 142, 140, 72], [17, 34], [36, 44, 2, 19], [131, 88]], ![[54, 85, 75, 131], [141, 138], [68, 111, 158, 147], [75, 71, 153, 44], [157, 137], [69, 147, 118, 12], [9, 88]]]
 h' := ![![[145, 90, 112], [58, 43, 149], [2, 53, 170], [48, 49, 94], [153, 64, 15], [167, 33, 81], [0, 0, 1], [0, 1]], ![[54, 82, 61], [150, 151, 80], [64, 45, 154], [1, 47, 48], [146, 148, 94], [59, 103, 131], [119, 18, 82], [145, 90, 112]], ![[0, 1], [79, 152, 117], [3, 75, 22], [72, 77, 31], [95, 134, 64], [135, 37, 134], [31, 155, 90], [54, 82, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 161], []]
 b := ![[], [56, 10, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [13, 90, 147, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43423, -8304, 2768]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -48, 16]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -10, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![17, -10, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![17, 169, 1]] where
  M :=![![![17, -10, 1], ![-332, 90, -9], ![2988, -989, 81]]]
  hmulB := by decide  
  f := ![![![-9, -1, 0]], ![![0, -9, -1]], ![![1, -9, -1]]]
  g := ![![![0, -1, 1], ![-1, 9, -9], ![9, -82, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [81, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 178], [0, 1]]
 g := ![![[122, 42], [66, 138], [66], [12], [12, 31], [91, 116], [1]], ![[0, 137], [151, 41], [66], [12], [118, 148], [95, 63], [1]]]
 h' := ![![[142, 178], [24, 20], [6, 73], [124, 148], [102, 38], [147, 63], [98, 142], [0, 1]], ![[0, 1], [0, 159], [169, 106], [18, 31], [128, 141], [143, 116], [35, 37], [142, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [63, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [81, 37, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2575, -707, 375]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -358, 375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![179, 0, 0], ![9, 1, 0], ![98, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 1], ![-332, 73, 10]]]
  hmulB := by decide  
  f := ![![![-17, 10, -1]], ![![1, 0, 0]], ![![-26, 11, -1]]]
  g := ![![![0, 1, 0], ![-1, 9, 1], ![-11, 73, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![17, -10, 1]] ![![9, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [50, 84, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 55, 74], [4, 125, 107], [0, 1]]
 g := ![![[16, 117, 16], [174, 101], [159, 35, 178], [49, 80], [1, 77, 46], [32, 109, 1], []], ![[137, 17, 142, 164], [133, 94], [38, 34, 8, 115], [108, 167], [41, 169, 2, 130], [159, 35, 118, 22], [122, 46]], ![[0, 76, 127, 124], [158, 145], [72, 77, 21, 40], [121, 147], [160, 161, 167, 95], [9, 36, 174, 47], [89, 46]]]
 h' := ![![[105, 55, 74], [3, 45, 177], [14, 64, 61], [50, 0, 84], [131, 165, 73], [29, 7, 74], [0, 0, 1], [0, 1]], ![[4, 125, 107], [51, 132, 115], [2, 19, 53], [165, 152, 2], [139, 114, 158], [137, 19, 175], [38, 88, 125], [105, 55, 74]], ![[0, 1], [0, 4, 70], [29, 98, 67], [92, 29, 95], [13, 83, 131], [94, 155, 113], [91, 93, 55], [4, 125, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 160], []]
 b := ![[], [143, 132, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [50, 84, 72, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4505090, -1453792, 133216]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24890, -8032, 736]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![17, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![17, 1, 0]] 
 ![![191, 0, 0], ![17, 1, 0], ![93, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![17, 1, 0], ![0, 17, 1], ![-332, 73, 18]]]
  hmulB := by decide  
  f := ![![![732, 43, 0], ![-8213, 0, 0]], ![![34, 2, 0], ![-381, 0, 0]], ![![342, 20, 0], ![-3837, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 191, 0], ![-93, 0, 191]], ![![0, 1, 0], ![-2, 17, 1], ![-17, 73, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![73, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![73, 1, 0]] 
 ![![191, 0, 0], ![73, 1, 0], ![19, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![73, 1, 0], ![0, 73, 1], ![-332, 73, 74]]]
  hmulB := by decide  
  f := ![![![5038, 69, 0], ![-13179, 0, 0]], ![![1898, 26, 0], ![-4965, 0, 0]], ![![466, 6, 0], ![-1219, 1, 0]]]
  g := ![![![1, 0, 0], ![-73, 191, 0], ![-19, 0, 191]], ![![0, 1, 0], ![-28, 73, 1], ![-37, 73, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-91, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-91, 1, 0]] 
 ![![191, 0, 0], ![100, 1, 0], ![123, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-91, 1, 0], ![0, -91, 1], ![-332, 73, -90]]]
  hmulB := by decide  
  f := ![![![3368, -37, 0], ![7067, 0, 0]], ![![1730, -19, 0], ![3630, 0, 0]], ![![2228, -24, 0], ![4675, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 191, 0], ![-123, 0, 191]], ![![-1, 1, 0], ![47, -91, 1], ![18, 73, -90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![17, 1, 0]] ![![191, 0, 0], ![73, 1, 0]]
  ![![191, 0, 0], ![-96, 90, 1]] where
 M := ![![![36481, 0, 0], ![13943, 191, 0]], ![![3247, 191, 0], ![1241, 90, 1]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![73, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-96, 90, 1]] ![![191, 0, 0], ![-91, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-17381, 191, 0]], ![![-18336, 17190, 191], ![8404, -8213, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-91, 1, 0]]], ![![![-96, 90, 1]], ![![44, -43, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [126, 36, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 185, 146], [77, 7, 47], [0, 1]]
 g := ![![[137, 147, 72], [173, 186], [156, 161], [132, 134], [27, 134], [64, 64], [1]], ![[29, 160, 105, 22], [], [30, 54], [13, 131], [163, 101], [23, 165], [167, 148, 164, 11]], ![[104, 191, 176, 140], [107, 186], [165, 28], [186, 172], [106, 59], [121, 108], [6, 53, 157, 182]]]
 h' := ![![[108, 185, 146], [38, 119, 119], [42, 26, 147], [165, 116, 136], [44, 177, 83], [92, 55, 110], [67, 157, 185], [0, 1]], ![[77, 7, 47], [92, 145, 65], [142, 114], [107, 50, 132], [89, 126, 175], [13, 141, 115], [189, 151, 92], [108, 185, 146]], ![[0, 1], [10, 122, 9], [102, 53, 46], [137, 27, 118], [42, 83, 128], [9, 190, 161], [104, 78, 109], [77, 7, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 86], []]
 b := ![[], [154, 29, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [126, 36, 8, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154207, -73919, 9843]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![799, -383, 51]
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



lemma PB280I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB280I3 : PrimesBelowBoundCertificateInterval O 137 193 280 where
  m := 11
  g := ![2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB280I3_primes
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
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![191, 191, 191]
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
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I151N1, I163N1, I179N1, I191N0, I191N1, I191N2]
  Il := ![[I139N1], [], [I151N1], [], [I163N1], [], [], [I179N1], [], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
