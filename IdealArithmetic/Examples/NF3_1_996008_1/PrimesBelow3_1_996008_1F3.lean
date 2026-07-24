
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [119, 6, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 126, 48], [52, 12, 91], [0, 1]]
 g := ![![[120, 3, 106], [122, 73, 7], [90, 55], [26, 88, 67], [20, 64], [89, 1], []], ![[75, 93, 47, 68], [92, 3, 82, 26], [118, 42], [81, 109, 110, 22], [135, 120], [19, 5], [34, 80]], ![[58, 86, 2, 44], [119, 78, 74, 129], [105, 127], [8, 4, 34, 100], [37, 44], [54, 30], [130, 80]]]
 h' := ![![[37, 126, 48], [77, 87, 84], [38, 67, 110], [103, 86, 65], [17, 4, 117], [112, 42, 131], [0, 0, 1], [0, 1]], ![[52, 12, 91], [133, 19, 41], [86, 26, 88], [111, 126, 43], [123, 130, 67], [8, 13, 113], [103, 17, 12], [37, 126, 48]], ![[0, 1], [55, 33, 14], [104, 46, 80], [28, 66, 31], [19, 5, 94], [35, 84, 34], [22, 122, 126], [52, 12, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 35], []]
 b := ![[], [115, 61, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [119, 6, 50, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34333, 0, 0]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-247, 0, 0]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![4, -25, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![4, -25, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![4, 124, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![4, -25, 1], ![198, 29, -25], ![-4950, -427, 29]]]
  hmulB := by decide  
  f := ![![![-3, 25, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -124, 149]], ![![0, -1, 1], ![2, 21, -25], ![-34, -27, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [144, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 148], [0, 1]]
 g := ![![[32, 119], [85], [19, 107], [37], [133, 17], [121], [1]], ![[0, 30], [85], [4, 42], [37], [22, 132], [121], [1]]]
 h' := ![![[11, 148], [63, 62], [95, 95], [29, 16], [69, 22], [34, 100], [5, 11], [0, 1]], ![[0, 1], [0, 87], [97, 54], [56, 133], [13, 127], [91, 49], [126, 138], [11, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [129, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [144, 138, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2369, 1210, 637]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -522, 637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![25, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![25, 1, 0]] 
 ![![149, 0, 0], ![25, 1, 0], ![120, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![25, 1, 0], ![0, 25, 1], ![198, 25, 25]]]
  hmulB := by decide  
  f := ![![![101, 4, 0], ![-596, 0, 0]], ![![-25, -1, 0], ![150, 0, 0]], ![![80, 3, 0], ![-472, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 149, 0], ![-120, 0, 149]], ![![0, 1, 0], ![-5, 25, 1], ![-23, 25, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![4, -25, 1]] ![![149, 0, 0], ![25, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![3725, 149, 0]], ![![596, -3725, 149], ![298, -596, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![25, 1, 0]]], ![![![4, -25, 1]], ![![2, -4, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [77, 101, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 79, 125], [5, 71, 26], [0, 1]]
 g := ![![[64, 68, 47], [51, 9, 138], [62, 61, 18], [99, 118], [72, 31, 72], [60, 1], []], ![[77, 32, 91, 4], [96, 120, 133, 72], [142, 130, 114, 10], [19, 8], [127, 52, 96, 25], [113, 58], [61, 72]], ![[92, 101, 77, 67], [65, 115, 139, 33], [121, 123, 14, 3], [90, 125], [16, 139, 8, 112], [96, 50], [9, 72]]]
 h' := ![![[55, 79, 125], [150, 87, 97], [58, 1, 17], [115, 106, 13], [43, 102, 119], [61, 54, 26], [0, 0, 1], [0, 1]], ![[5, 71, 26], [93, 110, 95], [77, 13, 124], [64, 134, 130], [116, 46, 59], [27, 17, 140], [140, 5, 71], [55, 79, 125]], ![[0, 1], [115, 105, 110], [32, 137, 10], [115, 62, 8], [34, 3, 124], [26, 80, 136], [87, 146, 79], [5, 71, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 143], []]
 b := ![[], [18, 58, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [77, 101, 91, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![120045, -22801, -3473]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![795, -151, -23]
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


def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![37, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![37, 1, 0]] 
 ![![157, 0, 0], ![37, 1, 0], ![44, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![37, 1, 0], ![0, 37, 1], ![198, 25, 37]]]
  hmulB := by decide  
  f := ![![![556, 15, 0], ![-2355, 0, 0]], ![![74, 2, 0], ![-313, 0, 0]], ![![120, 3, 0], ![-508, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 157, 0], ![-44, 0, 157]], ![![0, 1, 0], ![-9, 37, 1], ![-15, 25, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-645973, -170832, -23608]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-645973, -170832, -23608]] 
 ![![157, 0, 0], ![83, 1, 0], ![19, 0, 1]] where
  M :=![![![-645973, -170832, -23608], ![-4674384, -1236173, -170832], ![-33824736, -8945184, -1236173]]]
  hmulB := by decide  
  f := ![![![-12841, 2064, -40]], ![![-6839, 1003, -8]], ![![1049, 528, -93]]]
  g := ![![![89055, -170832, -23608], ![644419, -1236173, -170832], ![4663139, -8945184, -1236173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![37, 1, 0]] ![![157, 0, 0], ![37, 1, 0]]
  ![![12841, -2064, 40]] where
 M := ![![![24649, 0, 0], ![5809, 157, 0]], ![![5809, 157, 0], ![1369, 74, 1]]]
 hmul := by decide  
 g := ![![![![101417761, 26820624, 3706456]], ![![28575385, 7556957, 1044328]]], ![![![28575385, 7556957, 1044328]], ![![8051377, 2129242, 294249]]]]
 hle2 := by decide  
def MulI157N1 : IdealMulLeCertificate' Table 
  ![![12841, -2064, 40]] ![![-645973, -170832, -23608]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [104, 76, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 117], [13, 158, 46], [0, 1]]
 g := ![![[152, 59, 49], [26, 137, 104], [26, 104], [7, 115], [143, 10], [17, 16, 1], []], ![[25, 86, 16, 122], [94, 43, 113, 98], [114, 95], [95, 57], [52, 104], [161, 94, 3, 154], [73, 160]], ![[37, 66, 143, 74], [69, 30, 8, 24], [44, 16], [46, 47], [91, 144], [81, 145, 118, 84], [144, 160]]]
 h' := ![![[3, 4, 117], [67, 53, 7], [38, 23, 105], [42, 73, 58], [97, 32, 142], [25, 141, 93], [0, 0, 1], [0, 1]], ![[13, 158, 46], [120, 77, 135], [147, 23, 47], [58, 35, 101], [22, 44, 100], [41, 121, 58], [78, 4, 158], [3, 4, 117]], ![[0, 1], [123, 33, 21], [133, 117, 11], [54, 55, 4], [130, 87, 84], [38, 64, 12], [26, 159, 4], [13, 158, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 40], []]
 b := ![[], [12, 150, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [104, 76, 147, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1102532, -7009, 21027]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6764, -43, 129]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![54, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![54, 1, 0]] 
 ![![167, 0, 0], ![54, 1, 0], ![90, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![54, 1, 0], ![0, 54, 1], ![198, 25, 54]]]
  hmulB := by decide  
  f := ![![![3727, 69, 0], ![-11523, 0, 0]], ![![1134, 21, 0], ![-3506, 0, 0]], ![![1962, 36, 0], ![-6066, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 167, 0], ![-90, 0, 167]], ![![0, 1, 0], ![-18, 54, 1], ![-36, 25, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-30, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-30, 1, 0]] 
 ![![167, 0, 0], ![137, 1, 0], ![102, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-30, 1, 0], ![0, -30, 1], ![198, 25, -30]]]
  hmulB := by decide  
  f := ![![![1531, -51, 0], ![8517, 0, 0]], ![![1261, -42, 0], ![7015, 0, 0]], ![![906, -30, 0], ![5040, 1, 0]]]
  g := ![![![1, 0, 0], ![-137, 167, 0], ![-102, 0, 167]], ![![-1, 1, 0], ![24, -30, 1], ![-1, 25, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-24, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-24, 1, 0]] 
 ![![167, 0, 0], ![143, 1, 0], ![92, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-24, 1, 0], ![0, -24, 1], ![198, 25, -24]]]
  hmulB := by decide  
  f := ![![![217, -9, 0], ![1503, 0, 0]], ![![193, -8, 0], ![1337, 0, 0]], ![![148, -6, 0], ![1026, 1, 0]]]
  g := ![![![1, 0, 0], ![-143, 167, 0], ![-92, 0, 167]], ![![-1, 1, 0], ![20, -24, 1], ![-7, 25, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![54, 1, 0]] ![![167, 0, 0], ![-30, 1, 0]]
  ![![167, 0, 0], ![50, 24, 1]] where
 M := ![![![27889, 0, 0], ![-5010, 167, 0]], ![![9018, 167, 0], ![-1620, 24, 1]]]
 hmul := by decide  
 g := ![![![![117, -24, -1], ![167, 0, 0]], ![![-30, 1, 0], ![0, 0, 0]]], ![![![4, -23, -1], ![167, 0, 0]], ![![-10, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![50, 24, 1]] ![![167, 0, 0], ![-24, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-4008, 167, 0]], ![![8350, 4008, 167], ![-1002, -501, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-24, 1, 0]]], ![![![50, 24, 1]], ![![-6, -3, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [25, 6, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 49, 114], [101, 123, 59], [0, 1]]
 g := ![![[96, 133, 89], [115, 138], [64, 152, 160], [121, 110, 95], [53, 60], [72, 123, 1], []], ![[162, 168, 114, 115], [72, 15], [154, 103, 21, 20], [80, 118, 92, 87], [84, 4], [58, 66, 158, 69], [88, 21]], ![[120, 53, 43, 19], [39, 124], [88, 112, 151, 44], [67, 59, 79, 12], [77, 85], [27, 153, 127, 145], [143, 21]]]
 h' := ![![[22, 49, 114], [12, 64, 75], [130, 104, 151], [89, 61, 81], [115, 91, 21], [103, 126, 135], [0, 0, 1], [0, 1]], ![[101, 123, 59], [48, 53, 86], [34, 33, 154], [143, 123, 136], [162, 115, 155], [94, 71, 2], [14, 65, 123], [22, 49, 114]], ![[0, 1], [169, 56, 12], [148, 36, 41], [82, 162, 129], [18, 140, 170], [127, 149, 36], [52, 108, 49], [101, 123, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 101], []]
 b := ![[], [155, 96, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [25, 6, 50, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34427, 0, 0]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-199, 0, 0]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-55, 68, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-55, 68, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![124, 68, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-55, 68, 1], ![198, -30, 68], ![13464, 1898, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -68, 179]], ![![-1, 0, 1], ![-46, -26, 68], ![96, 22, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [35, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 178], [0, 1]]
 g := ![![[9, 144], [8, 22], [169], [60], [14, 27], [64, 59], [1]], ![[115, 35], [59, 157], [169], [60], [101, 152], [95, 120], [1]]]
 h' := ![![[43, 178], [78, 12], [59, 77], [109, 13], [47, 66], [87, 122], [144, 43], [0, 1]], ![[0, 1], [57, 167], [148, 102], [131, 166], [21, 113], [142, 57], [24, 136], [43, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [163, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [35, 136, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7696, 3770, 524]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-320, -178, 524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-68, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-68, 1, 0]] 
 ![![179, 0, 0], ![111, 1, 0], ![30, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-68, 1, 0], ![0, -68, 1], ![198, 25, -68]]]
  hmulB := by decide  
  f := ![![![10405, -153, 0], ![27387, 0, 0]], ![![6529, -96, 0], ![17185, 0, 0]], ![![1794, -26, 0], ![4722, 1, 0]]]
  g := ![![![1, 0, 0], ![-111, 179, 0], ![-30, 0, 179]], ![![-1, 1, 0], ![42, -68, 1], ![-3, 25, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-55, 68, 1]] ![![179, 0, 0], ![-68, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-12172, 179, 0]], ![![-9845, 12172, 179], ![3938, -4654, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-68, 1, 0]]], ![![![-55, 68, 1]], ![![22, -26, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![2, -82, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![2, -82, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![2, 99, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![2, -82, 1], ![198, 27, -82], ![-16236, -1852, 27]]]
  hmulB := by decide  
  f := ![![![-1, 82, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -99, 181]], ![![0, -1, 1], ![2, 45, -82], ![-90, -25, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [32, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 180], [0, 1]]
 g := ![![[44, 168], [65], [180, 27], [176], [98, 172], [81, 152], [1]], ![[67, 13], [65], [174, 154], [176], [100, 9], [7, 29], [1]]]
 h' := ![![[40, 180], [30, 118], [32, 80], [21, 82], [122, 151], [123, 124], [149, 40], [0, 1]], ![[0, 1], [44, 63], [155, 101], [43, 99], [8, 30], [15, 57], [120, 141], [40, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [62, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [32, 141, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1296, 465, -105]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 60, -105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![82, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![82, 1, 0]] 
 ![![181, 0, 0], ![82, 1, 0], ![154, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![82, 1, 0], ![0, 82, 1], ![198, 25, 82]]]
  hmulB := by decide  
  f := ![![![4839, 59, 0], ![-10679, 0, 0]], ![![2214, 27, 0], ![-4886, 0, 0]], ![![4138, 50, 0], ![-9132, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 181, 0], ![-154, 0, 181]], ![![0, 1, 0], ![-38, 82, 1], ![-80, 25, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![2, -82, 1]] ![![181, 0, 0], ![82, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![14842, 181, 0]], ![![362, -14842, 181], ![362, -6697, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![82, 1, 0]]], ![![![2, -82, 1]], ![![2, -37, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-54, 60, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-54, 60, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![137, 60, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-54, 60, 1], ![198, -29, 60], ![11880, 1698, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-137, -60, 191]], ![![-1, 0, 1], ![-42, -19, 60], ![83, 18, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [136, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 190], [0, 1]]
 g := ![![[165, 125], [101, 36], [156, 184], [125, 27], [97, 108], [28, 54], [1]], ![[0, 66], [0, 155], [43, 7], [97, 164], [176, 83], [163, 137], [1]]]
 h' := ![![[98, 190], [16, 70], [176, 6], [190, 152], [178, 119], [12, 144], [55, 98], [0, 1]], ![[0, 1], [0, 121], [0, 185], [188, 39], [189, 72], [181, 47], [109, 93], [98, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [38, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [136, 93, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![928, 985, 287]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-201, -85, 287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-60, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-60, 1, 0]] 
 ![![191, 0, 0], ![131, 1, 0], ![29, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-60, 1, 0], ![0, -60, 1], ![198, 25, -60]]]
  hmulB := by decide  
  f := ![![![10441, -174, 0], ![33234, 0, 0]], ![![7141, -119, 0], ![22730, 0, 0]], ![![1579, -26, 0], ![5026, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 191, 0], ![-29, 0, 191]], ![![-1, 1, 0], ![41, -60, 1], ![-7, 25, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-54, 60, 1]] ![![191, 0, 0], ![-60, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-11460, 191, 0]], ![![-10314, 11460, 191], ![3438, -3629, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-60, 1, 0]]], ![![![-54, 60, 1]], ![![18, -19, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [143, 133, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 132, 180], [44, 60, 13], [0, 1]]
 g := ![![[63, 30, 43], [26, 134], [36, 85], [118, 92], [113, 98], [188, 42], [1]], ![[82, 95, 72, 38], [57, 24], [161, 24], [125, 161], [188, 6], [155, 96], [178, 7, 22, 119]], ![[76, 15, 164, 38], [11, 25], [114, 170], [179, 84], [42, 110], [176, 8], [39, 99, 50, 74]]]
 h' := ![![[62, 132, 180], [16, 156, 129], [158, 11, 110], [45, 64, 144], [163, 155, 142], [127, 80, 171], [50, 60, 106], [0, 1]], ![[44, 60, 13], [85, 119, 115], [138, 169, 88], [192, 38, 88], [73, 174, 136], [55, 163, 149], [188, 62, 176], [62, 132, 180]], ![[0, 1], [132, 111, 142], [57, 13, 188], [95, 91, 154], [122, 57, 108], [97, 143, 66], [91, 71, 104], [44, 60, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 83], []]
 b := ![[], [159, 22, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [143, 133, 87, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1214163, 73726, 15826]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6291, 382, 82]
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



lemma PB283I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB283I3 : PrimesBelowBoundCertificateInterval O 137 193 283 where
  m := 11
  g := ![1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB283I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I157N0, I157N1, I167N0, I167N1, I167N2, I179N1, I181N1, I191N1]
  Il := ![[], [I149N1], [], [I157N0, I157N0, I157N1], [], [I167N0, I167N1, I167N2], [], [I179N1], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
