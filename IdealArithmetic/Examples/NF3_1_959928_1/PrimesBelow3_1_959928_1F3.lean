
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [132, 83, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 52, 102], [9, 86, 37], [0, 1]]
 g := ![![[136, 82, 38], [67, 79, 96], [5, 136], [60, 92, 118], [13, 107], [127, 1], []], ![[32, 50, 90, 22], [1, 49, 106, 68], [81, 122], [42, 111, 112, 50], [89, 44], [56, 29], [18, 118]], ![[26, 122, 100, 5], [24, 83, 102, 45], [131, 55], [0, 108, 56, 57], [72, 34], [60, 63], [83, 118]]]
 h' := ![![[118, 52, 102], [52, 125, 90], [44, 126, 97], [3, 1, 54], [58, 51, 102], [55, 30, 61], [0, 0, 1], [0, 1]], ![[9, 86, 37], [85, 20, 57], [133, 124, 66], [20, 56, 20], [109, 34, 74], [96, 87, 105], [11, 67, 86], [118, 52, 102]], ![[0, 1], [14, 133, 131], [62, 28, 115], [37, 82, 65], [70, 54, 102], [119, 22, 112], [106, 72, 52], [9, 86, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 42], []]
 b := ![[], [95, 110, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [132, 83, 12, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1276854, -434514, -70612]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9186, -3126, -508]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-104, -37, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-104, -37, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![45, 112, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-104, -37, 1], ![246, -93, -74], ![-9225, -1653, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -112, 149]], ![![-1, -1, 1], ![24, 55, -74], ![-45, 31, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [29, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 148], [0, 1]]
 g := ![![[97, 36], [22], [36, 132], [37], [101, 102], [26], [1]], ![[0, 113], [22], [28, 17], [37], [0, 47], [26], [1]]]
 h' := ![![[18, 148], [108, 143], [148, 52], [38, 79], [51, 22], [87, 20], [120, 18], [0, 1]], ![[0, 1], [0, 6], [41, 97], [119, 70], [0, 127], [0, 129], [146, 131], [18, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [119, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [29, 131, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4382, 123, 45]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -33, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![74, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![74, 1, 0]] 
 ![![149, 0, 0], ![74, 1, 0], ![56, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![74, 1, 0], ![0, 75, 2], ![246, 48, 74]]]
  hmulB := by decide  
  f := ![![![10731, 145, 0], ![-21605, 0, 0]], ![![5254, 71, 0], ![-10578, 0, 0]], ![![3904, 15, -1], ![-7860, 75, 0]]]
  g := ![![![1, 0, 0], ![-74, 149, 0], ![-56, 0, 149]], ![![0, 1, 0], ![-38, 75, 2], ![-50, 48, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-104, -37, 1]] ![![149, 0, 0], ![74, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![11026, 149, 0]], ![![-15496, -5513, 149], ![-7450, -2831, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![74, 1, 0]]], ![![![-104, -37, 1]], ![![-50, -19, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-79, 8, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-79, 8, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![72, 8, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-79, 8, 1], ![246, -23, 16], ![1845, 507, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -8, 151]], ![![-1, 0, 1], ![-6, -1, 16], ![27, 5, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [60, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 150], [0, 1]]
 g := ![![[78, 121], [125, 39], [51, 95], [9], [27, 118], [1], [1]], ![[48, 30], [13, 112], [146, 56], [9], [145, 33], [1], [1]]]
 h' := ![![[1, 150], [50, 140], [111, 48], [84, 104], [41, 3], [67, 32], [91, 1], [0, 1]], ![[0, 1], [39, 11], [8, 103], [37, 47], [44, 148], [99, 119], [92, 150], [1, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [12, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [60, 150, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2056, 3735, 448]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-200, 1, 448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-16, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-16, 1, 0]] 
 ![![151, 0, 0], ![135, 1, 0], ![31, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-16, 1, 0], ![0, -15, 2], ![246, 48, -16]]]
  hmulB := by decide  
  f := ![![![1585, -99, 0], ![14949, 0, 0]], ![![1409, -88, 0], ![13289, 0, 0]], ![![329, -13, -1], ![3103, 76, 0]]]
  g := ![![![1, 0, 0], ![-135, 151, 0], ![-31, 0, 151]], ![![-1, 1, 0], ![13, -15, 2], ![-38, 48, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-79, 8, 1]] ![![151, 0, 0], ![-16, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-2416, 151, 0]], ![![-11929, 1208, 151], ![1510, -151, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-16, 1, 0]]], ![![![-79, 8, 1]], ![![10, -1, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [114, 49, 133, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 55, 65], [32, 101, 92], [0, 1]]
 g := ![![[113, 109, 145], [86, 75], [54, 61, 118], [49, 126, 9], [4, 21, 153], [24, 1], []], ![[18, 72, 18, 119], [11, 120], [92, 141, 36, 125], [20, 43, 3, 83], [35, 96, 140, 78], [126, 153], [63, 143]], ![[145, 47, 148, 28], [122, 19], [50, 37, 104, 133], [76, 152, 114, 7], [95, 101, 89, 18], [99, 42], [36, 143]]]
 h' := ![![[149, 55, 65], [77, 29, 107], [124, 94, 46], [66, 102, 78], [15, 15, 154], [90, 123, 56], [0, 0, 1], [0, 1]], ![[32, 101, 92], [140, 40, 132], [74, 38, 80], [140, 123, 64], [54, 88, 44], [63, 60, 149], [104, 141, 101], [149, 55, 65]], ![[0, 1], [46, 88, 75], [83, 25, 31], [3, 89, 15], [1, 54, 116], [7, 131, 109], [60, 16, 55], [32, 101, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 153], []]
 b := ![[], [22, 85, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [114, 49, 133, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1053627, -230319, -17270]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6711, -1467, -110]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-34, -18, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-34, -18, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![129, 145, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-34, -18, 1], ![246, -4, -36], ![-4551, -741, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -145, 163]], ![![-1, -1, 1], ![30, 32, -36], ![-39, -17, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [56, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 162], [0, 1]]
 g := ![![[119, 131], [92, 155], [133], [161], [96], [4, 35], [1]], ![[0, 32], [103, 8], [133], [161], [96], [17, 128], [1]]]
 h' := ![![[19, 162], [64, 91], [103, 36], [85, 40], [138, 18], [102, 111], [107, 19], [0, 1]], ![[0, 1], [0, 72], [135, 127], [30, 123], [154, 145], [92, 52], [142, 144], [19, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [156, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [56, 144, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![152598, 97883, 25034]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18876, -21669, 25034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![36, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![36, 1, 0]] 
 ![![163, 0, 0], ![36, 1, 0], ![149, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![36, 1, 0], ![0, 37, 2], ![246, 48, 36]]]
  hmulB := by decide  
  f := ![![![1693, 47, 0], ![-7661, 0, 0]], ![![324, 9, 0], ![-1466, 0, 0]], ![![1571, 25, -1], ![-7109, 82, 0]]]
  g := ![![![1, 0, 0], ![-36, 163, 0], ![-149, 0, 163]], ![![0, 1, 0], ![-10, 37, 2], ![-42, 48, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-34, -18, 1]] ![![163, 0, 0], ![36, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![5868, 163, 0]], ![![-5542, -2934, 163], ![-978, -652, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![36, 1, 0]]], ![![![-34, -18, 1]], ![![-6, -4, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-40, -49, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-40, -49, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![127, 118, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-40, -49, 1], ![246, -41, -98], ![-12177, -2229, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -118, 167]], ![![-1, -1, 1], ![76, 69, -98], ![-79, -19, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [38, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 166], [0, 1]]
 g := ![![[98, 22], [130, 36], [80, 66], [94], [56], [42, 162], [1]], ![[0, 145], [0, 131], [120, 101], [94], [56], [125, 5], [1]]]
 h' := ![![[117, 166], [70, 135], [133, 6], [166, 147], [8, 42], [74, 35], [129, 117], [0, 1]], ![[0, 1], [0, 32], [0, 161], [164, 20], [79, 125], [161, 132], [124, 50], [117, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [162, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [38, 50, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![850, 415, 104]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, -71, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-69, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-69, 1, 0]] 
 ![![167, 0, 0], ![98, 1, 0], ![159, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-69, 1, 0], ![0, -68, 2], ![246, 48, -69]]]
  hmulB := by decide  
  f := ![![![8143, -118, 0], ![19706, 0, 0]], ![![4762, -69, 0], ![11524, 0, 0]], ![![7743, -78, -1], ![18738, 84, 0]]]
  g := ![![![1, 0, 0], ![-98, 167, 0], ![-159, 0, 167]], ![![-1, 1, 0], ![38, -68, 2], ![39, 48, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-40, -49, 1]] ![![167, 0, 0], ![-69, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11523, 167, 0]], ![![-6680, -8183, 167], ![3006, 3340, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-69, 1, 0]]], ![![![-40, -49, 1]], ![![18, 20, -1]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [57, 156, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 91, 114], [119, 81, 59], [0, 1]]
 g := ![![[27, 76, 92], [8, 157], [162, 78, 6], [124, 160, 132], [74, 83], [102, 137, 1], []], ![[118, 82, 170, 94], [84, 152], [58, 110, 78, 72], [87, 17, 60, 97], [170, 135], [75, 44, 163, 75], [97, 21]], ![[41, 41, 3, 76], [68, 89], [24, 23, 13, 75], [19, 52, 23, 2], [103, 124], [88, 150, 4, 27], [152, 21]]]
 h' := ![![[18, 91, 114], [136, 147, 28], [108, 144, 147], [25, 48, 122], [60, 35, 85], [68, 153, 157], [0, 0, 1], [0, 1]], ![[119, 81, 59], [113, 121, 169], [149, 81, 124], [97, 42, 130], [107, 15, 149], [121, 120, 57], [158, 95, 81], [18, 91, 114]], ![[0, 1], [102, 78, 149], [93, 121, 75], [114, 83, 94], [45, 123, 112], [42, 73, 132], [134, 78, 91], [119, 81, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 15], []]
 b := ![[], [120, 90, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [57, 156, 36, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5869371, 2200041, 385617]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33927, 12717, 2229]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [123, 139, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 106, 104], [144, 72, 75], [0, 1]]
 g := ![![[83, 127, 14], [175, 52, 12], [151, 126], [106, 88], [50, 49, 64], [110, 138, 1], []], ![[75, 121, 141, 115], [102, 130, 51, 166], [134, 59], [82, 144], [53, 69, 91, 127], [43, 32, 91, 167], [137, 76]], ![[40, 113, 22, 51], [138, 88, 119, 27], [166, 108], [125, 169], [20, 128, 13, 117], [82, 27, 120, 147], [166, 76]]]
 h' := ![![[173, 106, 104], [134, 60, 67], [107, 26, 38], [8, 11, 22], [115, 17, 25], [74, 135, 171], [0, 0, 1], [0, 1]], ![[144, 72, 75], [153, 111, 145], [11, 40, 70], [5, 140, 43], [109, 34, 167], [71, 119, 39], [11, 51, 72], [173, 106, 104]], ![[0, 1], [8, 8, 146], [4, 113, 71], [175, 28, 114], [131, 128, 166], [144, 104, 148], [139, 128, 106], [144, 72, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 117], []]
 b := ![[], [170, 108, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [123, 139, 41, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14812071, -4504356, -709914]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82749, -25164, -3966]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-4, -76, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-4, -76, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![177, 105, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-4, -76, 1], ![246, -32, -152], ![-18819, -3525, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-177, -105, 181]], ![![-1, -1, 1], ![150, 88, -152], ![-147, -45, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [79, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 180], [0, 1]]
 g := ![![[54, 55], [13], [36, 36], [180], [28, 177], [135, 111], [1]], ![[0, 126], [13], [129, 145], [180], [78, 4], [105, 70], [1]]]
 h' := ![![[78, 180], [48, 69], [52, 111], [50, 175], [141, 162], [14, 38], [102, 78], [0, 1]], ![[0, 1], [0, 112], [22, 70], [125, 6], [107, 19], [82, 143], [32, 103], [78, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [42, 166]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [79, 103, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1464, 123, 177]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -102, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-29, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-29, 1, 0]] 
 ![![181, 0, 0], ![152, 1, 0], ![137, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-29, 1, 0], ![0, -28, 2], ![246, 48, -29]]]
  hmulB := by decide  
  f := ![![![1480, -51, 0], ![9231, 0, 0]], ![![1248, -43, 0], ![7784, 0, 0]], ![![1134, -25, -1], ![7073, 91, 0]]]
  g := ![![![1, 0, 0], ![-152, 181, 0], ![-137, 0, 181]], ![![-1, 1, 0], ![22, -28, 2], ![-17, 48, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-4, -76, 1]] ![![181, 0, 0], ![-29, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-5249, 181, 0]], ![![-724, -13756, 181], ![362, 2172, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-29, 1, 0]]], ![![![-4, -76, 1]], ![![2, 12, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-125, 80, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-125, 80, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![66, 80, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-125, 80, 1], ![246, 3, 160], ![19557, 3963, -77]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -80, 191]], ![![-1, 0, 1], ![-54, -67, 160], ![129, 53, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [41, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 190], [0, 1]]
 g := ![![[127, 153], [135, 115], [82, 48], [14, 40], [23, 125], [3, 17], [1]], ![[117, 38], [115, 76], [165, 143], [115, 151], [76, 66], [108, 174], [1]]]
 h' := ![![[141, 190], [4, 41], [76, 45], [190, 96], [12, 68], [68, 70], [150, 141], [0, 1]], ![[0, 1], [55, 150], [118, 146], [165, 95], [50, 123], [6, 121], [167, 50], [141, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [77, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [41, 50, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10424, 7073, 1466]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-452, -577, 1466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![31, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![31, 1, 0]] 
 ![![191, 0, 0], ![31, 1, 0], ![77, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![31, 1, 0], ![0, 32, 2], ![246, 48, 31]]]
  hmulB := by decide  
  f := ![![![1086, 35, 0], ![-6685, 0, 0]], ![![124, 4, 0], ![-763, 0, 0]], ![![406, -3, -1], ![-2499, 96, 0]]]
  g := ![![![1, 0, 0], ![-31, 191, 0], ![-77, 0, 191]], ![![0, 1, 0], ![-6, 32, 2], ![-19, 48, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-125, 80, 1]] ![![191, 0, 0], ![31, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![5921, 191, 0]], ![![-23875, 15280, 191], ![-3629, 2483, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![31, 1, 0]]], ![![![-125, 80, 1]], ![![-19, 13, 1]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [137, 135, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 186, 153], [174, 6, 40], [0, 1]]
 g := ![![[157, 20, 28], [], [166, 63], [22, 169], [85, 143], [161, 24], [1]], ![[94, 5, 95, 82], [124, 147], [121, 124], [77, 12], [63, 147], [146, 130], [135, 146, 108, 76]], ![[142, 155, 156, 30], [107, 147], [87, 96], [27, 32], [100, 166], [132, 124], [96, 31, 110, 117]]]
 h' := ![![[107, 186, 153], [31, 187, 75], [80, 123], [137, 156, 177], [177, 186, 13], [186, 1, 23], [56, 58, 88], [0, 1]], ![[174, 6, 40], [175, 2, 111], [117, 104, 98], [17, 126, 33], [12, 145, 165], [94, 148, 98], [105, 36, 138], [107, 186, 153]], ![[0, 1], [16, 4, 7], [59, 159, 95], [165, 104, 176], [2, 55, 15], [112, 44, 72], [61, 99, 160], [174, 6, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 124], []]
 b := ![[], [184, 134, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [137, 135, 105, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35512, 0, 2895]
  a := ![-3, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-184, 0, 15]
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



lemma PB278I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB278I3 : PrimesBelowBoundCertificateInterval O 137 193 278 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB278I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
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
  β := ![I149N1, I151N1, I163N1, I167N1, I181N1, I191N1]
  Il := ![[], [I149N1], [I151N1], [], [I163N1], [I167N1], [], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
