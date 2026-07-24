
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![1, 63, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![1, 63, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![1, 63, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![1, 63, 1], ![49, 29, 188], ![6993, -2156, -96]]]
  hmulB := by decide  
  f := ![![![0, 3, -4], ![-8, 3, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -63, 139]], ![![0, 0, 1], ![-1, -85, 188], ![51, 28, -96]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [102, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 138], [0, 1]]
 g := ![![[132, 9], [28, 96], [79], [58, 41], [65], [83], [1]], ![[25, 130], [45, 43], [79], [3, 98], [65], [83], [1]]]
 h' := ![![[19, 138], [63, 3], [111, 42], [61, 94], [106, 72], [131, 64], [37, 19], [0, 1]], ![[0, 1], [120, 136], [75, 97], [40, 45], [84, 67], [96, 75], [120, 120], [19, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [41, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [102, 120, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![996, -219, -672]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 303, -672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-49, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-49, 1, 0]] 
 ![![139, 0, 0], ![90, 1, 0], ![96, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-49, 1, 0], ![-1, -48, 3], ![112, -35, -50]]]
  hmulB := by decide  
  f := ![![![154, 7344, -459], ![0, 21267, 0]], ![![100, 4752, -297], ![1, 13761, 0]], ![![112, 5072, -317], ![16, 14688, 0]]]
  g := ![![![1, 0, 0], ![-90, 139, 0], ![-96, 0, 139]], ![![-1, 1, 0], ![29, -48, 3], ![58, -35, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![1, 63, 1]] ![![139, 0, 0], ![-49, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-6811, 139, 0]], ![![139, 8757, 139], ![0, -3058, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-49, 1, 0]]], ![![![1, 63, 1]], ![![0, -22, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120, 5, 3]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![120, 5, 3]] 
 ![![149, 0, 0], ![0, 149, 0], ![40, 101, 1]] where
  M :=![![![120, 5, 3], ![331, 20, 12], ![371, -28, 13]]]
  hmulB := by decide  
  f := ![![![4, -1, 0]], ![![1, 3, -3]], ![![1, 2, -2]]]
  g := ![![![0, -2, 3], ![-1, -8, 12], ![-1, -9, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [9, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 148], [0, 1]]
 g := ![![[110, 116], [133], [19, 100], [118], [129, 113], [127], [1]], ![[0, 33], [133], [104, 49], [118], [9, 36], [127], [1]]]
 h' := ![![[53, 148], [32, 50], [127, 27], [48, 139], [31, 72], [130, 115], [140, 53], [0, 1]], ![[0, 1], [0, 99], [68, 122], [114, 10], [122, 77], [116, 34], [118, 96], [53, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [89, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [9, 96, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4302, 3136, -1456]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![362, 1008, -1456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![149, 0, 0], ![145, 1, 0], ![95, 0, 1]] where
  M :=![![![-4, 1, 0], ![-1, -3, 3], ![112, -35, -5]]]
  hmulB := by decide  
  f := ![![![-120, -5, -3]], ![![-119, -5, -3]], ![![-79, -3, -2]]]
  g := ![![![-1, 1, 0], ![1, -3, 3], ![38, -35, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![120, 5, 3]] ![![-4, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![9, -55, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![9, -55, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![9, 96, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![9, -55, 1], ![167, -81, -166], ![-6223, 1974, 30]]]
  hmulB := by decide  
  f := ![![![-8, 55, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -96, 151]], ![![0, -1, 1], ![11, 105, -166], ![-43, -6, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [53, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 150], [0, 1]]
 g := ![![[118, 40], [141, 36], [71, 86], [1], [63, 37], [43], [1]], ![[14, 111], [138, 115], [89, 65], [1], [148, 114], [43], [1]]]
 h' := ![![[88, 150], [77, 74], [12, 6], [85, 122], [134, 150], [77, 43], [98, 88], [0, 1]], ![[0, 1], [96, 77], [87, 145], [100, 29], [46, 1], [86, 108], [141, 63], [88, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [79, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [53, 63, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![673726, -80263, -153269]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13597, 96911, -153269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![15, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![15, 1, 0]] 
 ![![151, 0, 0], ![15, 1, 0], ![121, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![15, 1, 0], ![-1, 16, 3], ![112, -35, 14]]]
  hmulB := by decide  
  f := ![![![3526, -56400, -10575], ![0, 532275, 0]], ![![350, -5600, -1050], ![1, 52850, 0]], ![![2821, -45195, -8474], ![45, 426525, 0]]]
  g := ![![![1, 0, 0], ![-15, 151, 0], ![-121, 0, 151]], ![![0, 1, 0], ![-4, 16, 3], ![-7, -35, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![9, -55, 1]] ![![151, 0, 0], ![15, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![2265, 151, 0]], ![![1359, -8305, 151], ![302, -906, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![15, 1, 0]]], ![![![9, -55, 1]], ![![2, -6, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![51, -2, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![51, -2, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![51, 155, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![51, -2, 1], ![114, 14, -7], ![-287, 119, 19]]]
  hmulB := by decide  
  f := ![![![-50, 2, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -155, 157]], ![![0, -1, 1], ![3, 7, -7], ![-8, -18, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [139, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 156], [0, 1]]
 g := ![![[135, 89], [42], [156, 132], [138, 1], [41, 11], [130], [1]], ![[59, 68], [42], [8, 25], [56, 156], [81, 146], [130], [1]]]
 h' := ![![[75, 156], [138, 106], [139, 102], [129, 17], [110, 1], [152, 47], [18, 75], [0, 1]], ![[0, 1], [81, 51], [96, 55], [148, 140], [28, 156], [66, 110], [148, 82], [75, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [54, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [139, 82, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1847, 2489, -2893]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![928, 2872, -2893]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![7, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![7, 1, 0]] 
 ![![157, 0, 0], ![7, 1, 0], ![138, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![7, 1, 0], ![-1, 8, 3], ![112, -35, 6]]]
  hmulB := by decide  
  f := ![![![-3606, 28799, 10800], ![157, -565200, 0]], ![![-167, 1279, 480], ![158, -25120, 0]], ![![-3168, 25314, 9493], ![102, -496800, 0]]]
  g := ![![![1, 0, 0], ![-7, 157, 0], ![-138, 0, 157]], ![![0, 1, 0], ![-3, 8, 3], ![-3, -35, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![51, -2, 1]] ![![157, 0, 0], ![7, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![1099, 157, 0]], ![![8007, -314, 157], ![471, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![7, 1, 0]]], ![![![51, -2, 1]], ![![3, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![28, 40, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![28, 40, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![28, 40, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![28, 40, 1], ![72, 33, 119], ![4417, -1351, -46]]]
  hmulB := by decide  
  f := ![![![-27, -40, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -40, 163]], ![![0, 0, 1], ![-20, -29, 119], ![35, 3, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [129, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 162], [0, 1]]
 g := ![![[81, 88], [27, 152], [33], [21], [91], [125, 126], [1]], ![[52, 75], [51, 11], [33], [21], [91], [102, 37], [1]]]
 h' := ![![[146, 162], [103, 67], [133, 57], [57, 14], [141, 99], [12, 55], [34, 146], [0, 1]], ![[0, 1], [105, 96], [142, 106], [145, 149], [88, 64], [55, 108], [160, 17], [146, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [13, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [129, 17, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![920, -13, -363]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 89, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![44, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![44, 1, 0]] 
 ![![163, 0, 0], ![44, 1, 0], ![46, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![44, 1, 0], ![-1, 45, 3], ![112, -35, 43]]]
  hmulB := by decide  
  f := ![![![-5083, 226799, 15120], ![163, -821520, 0]], ![![-1404, 61199, 4080], ![164, -221680, 0]], ![![-1462, 64004, 4267], ![148, -231840, 0]]]
  g := ![![![1, 0, 0], ![-44, 163, 0], ![-46, 0, 163]], ![![0, 1, 0], ![-13, 45, 3], ![-2, -35, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![28, 40, 1]] ![![163, 0, 0], ![44, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![7172, 163, 0]], ![![4564, 6520, 163], ![1304, 1793, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![44, 1, 0]]], ![![![28, 40, 1]], ![![8, 11, 1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [115, 105, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 153, 96], [14, 13, 71], [0, 1]]
 g := ![![[4, 112, 152], [14, 140, 144], [77, 56, 127], [0, 48], [125, 115], [81, 55, 1], []], ![[144, 101, 136, 8], [73, 51, 161, 144], [77, 28, 65, 72], [158, 6], [142, 99], [96, 44, 96, 25], [19, 31]], ![[36, 49, 57, 139], [67, 20, 114, 52], [118, 61, 96, 105], [91, 32], [161, 19], [85, 15, 9, 55], [44, 31]]]
 h' := ![![[41, 153, 96], [60, 148, 94], [163, 18, 155], [66, 80, 131], [20, 140, 86], [37, 33, 68], [0, 0, 1], [0, 1]], ![[14, 13, 71], [1, 139, 66], [102, 84, 69], [114, 55, 31], [158, 141, 29], [17, 139, 44], [164, 139, 13], [41, 153, 96]], ![[0, 1], [158, 47, 7], [166, 65, 110], [105, 32, 5], [7, 53, 52], [73, 162, 55], [146, 28, 153], [14, 13, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 125], []]
 b := ![[], [128, 78, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [115, 105, 112, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1188539, 79492, -234969]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7117, 476, -1407]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [61, 103, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 139, 133], [6, 33, 40], [0, 1]]
 g := ![![[143, 104, 96], [67, 16], [107, 106, 22], [108, 15, 164], [116, 52], [61, 106, 1], []], ![[84, 59, 155, 84], [87, 37], [5, 156, 90, 49], [122, 6, 102, 4], [18, 54], [144, 112, 105, 36], [12, 43]], ![[86, 58, 115, 22], [155, 10], [60, 139, 106, 140], [86, 139, 132, 122], [158, 14], [119, 113, 163, 49], [105, 43]]]
 h' := ![![[100, 139, 133], [25, 62, 142], [47, 9, 169], [159, 128, 117], [149, 118, 106], [85, 53, 158], [0, 0, 1], [0, 1]], ![[6, 33, 40], [42, 140, 130], [32, 118, 27], [149, 27, 125], [126, 149, 162], [94, 134, 153], [99, 67, 33], [100, 139, 133]], ![[0, 1], [97, 144, 74], [146, 46, 150], [0, 18, 104], [97, 79, 78], [96, 159, 35], [32, 106, 139], [6, 33, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 55], []]
 b := ![[], [123, 148, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [61, 103, 67, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-805315, 346173, -95150]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4655, 2001, -550]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [81, 130, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 46, 106], [104, 132, 73], [0, 1]]
 g := ![![[170, 69, 57], [170, 133, 129], [172, 89], [150, 51], [32, 85, 125], [134, 117, 1], []], ![[171, 107, 159, 161], [162, 161, 120, 16], [29, 60], [21, 45], [93, 8, 83, 169], [177, 127, 167, 22], [122, 138]], ![[44, 17, 108, 91], [130, 33, 109, 123], [88, 106], [127, 9], [35, 177, 103, 133], [150, 65, 145, 170], [155, 138]]]
 h' := ![![[13, 46, 106], [13, 99, 86], [6, 169, 32], [79, 50, 39], [93, 161, 87], [65, 132, 29], [0, 0, 1], [0, 1]], ![[104, 132, 73], [122, 131, 8], [162, 113, 121], [149, 84, 66], [66, 53, 89], [60, 41, 99], [132, 113, 132], [13, 46, 106]], ![[0, 1], [17, 128, 85], [61, 76, 26], [108, 45, 74], [152, 144, 3], [57, 6, 51], [51, 66, 46], [104, 132, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 44], []]
 b := ![[], [134, 162, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [81, 130, 62, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![493324, -305553, 197616]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2756, -1707, 1104]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-42, -44, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-42, -44, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![139, 137, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-42, -44, 1], ![156, -121, -133], ![-4991, 1589, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -137, 181]], ![![-1, -1, 1], ![103, 100, -133], ![-3, 33, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [44, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 180], [0, 1]]
 g := ![![[159, 144], [132], [3, 167], [138], [89, 38], [153, 168], [1]], ![[0, 37], [132], [26, 14], [138], [130, 143], [58, 13], [1]]]
 h' := ![![[63, 180], [32, 169], [49, 48], [94, 23], [66, 92], [146, 20], [137, 63], [0, 1]], ![[0, 1], [0, 12], [177, 133], [95, 158], [70, 89], [139, 161], [124, 118], [63, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [60, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [44, 118, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4044, -1090, -1415]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1109, 1065, -1415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-48, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-48, 1, 0]] 
 ![![181, 0, 0], ![133, 1, 0], ![32, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-48, 1, 0], ![-1, -47, 3], ![112, -35, -49]]]
  hmulB := by decide  
  f := ![![![-4410, -209574, 13377], ![181, -807079, 0]], ![![-3227, -153973, 9828], ![182, -592956, 0]], ![![-768, -37052, 2365], ![76, -142688, 0]]]
  g := ![![![1, 0, 0], ![-133, 181, 0], ![-32, 0, 181]], ![![-1, 1, 0], ![34, -47, 3], ![35, -35, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-42, -44, 1]] ![![181, 0, 0], ![-48, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-8688, 181, 0]], ![![-7602, -7964, 181], ![2172, 1991, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-48, 1, 0]]], ![![![-42, -44, 1]], ![![12, 11, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-19, -46, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-19, -46, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![172, 145, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-19, -46, 1], ![158, -100, -139], ![-5215, 1659, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-172, -145, 191]], ![![-1, -1, 1], ![126, 105, -139], ![-21, 14, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [53, 188, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 190], [0, 1]]
 g := ![![[54, 109], [132, 6], [144, 156], [108, 149], [88, 177], [91, 9], [1]], ![[190, 82], [150, 185], [39, 35], [173, 42], [46, 14], [118, 182], [1]]]
 h' := ![![[3, 190], [71, 142], [8, 31], [6, 164], [111, 63], [143, 122], [138, 3], [0, 1]], ![[0, 1], [115, 49], [101, 160], [116, 27], [109, 128], [127, 69], [147, 188], [3, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [143, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [53, 188, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15139, 5428, -500]
  a := ![-2, -6, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![371, 408, -500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-52, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-52, 1, 0]] 
 ![![191, 0, 0], ![139, 1, 0], ![7, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-52, 1, 0], ![-1, -51, 3], ![112, -35, -53]]]
  hmulB := by decide  
  f := ![![![474, 24123, -1419], ![0, 90343, 0]], ![![345, 17544, -1032], ![1, 65704, 0]], ![![22, 884, -52], ![17, 3311, 0]]]
  g := ![![![1, 0, 0], ![-139, 191, 0], ![-7, 0, 191]], ![![-1, 1, 0], ![37, -51, 3], ![28, -35, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-19, -46, 1]] ![![191, 0, 0], ![-52, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-9932, 191, 0]], ![![-3629, -8786, 191], ![1146, 2292, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-52, 1, 0]]], ![![![-19, -46, 1]], ![![6, 12, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![113, -93, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![113, -93, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![113, 100, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![113, -93, 1], ![205, -15, -280], ![-10479, 3304, 172]]]
  hmulB := by decide  
  f := ![![![-112, 93, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -100, 193]], ![![0, -1, 1], ![165, 145, -280], ![-155, -72, 172]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [149, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 192], [0, 1]]
 g := ![![[74, 137], [143], [81], [169], [46], [187], [168, 1]], ![[123, 56], [143], [81], [169], [46], [187], [143, 192]]]
 h' := ![![[168, 192], [158, 41], [106, 170], [4, 9], [45, 180], [12, 168], [58, 90], [0, 1]], ![[0, 1], [98, 152], [102, 23], [165, 184], [177, 13], [58, 25], [124, 103], [168, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [79, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [149, 25, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30420, -1548, -8245]
  a := ![-1, 13, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4985, 4264, -8245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![87, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![87, 1, 0]] 
 ![![193, 0, 0], ![87, 1, 0], ![21, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![87, 1, 0], ![-1, 88, 3], ![112, -35, 86]]]
  hmulB := by decide  
  f := ![![![-1293, 106215, 3621], ![193, -232951, 0]], ![![-631, 47871, 1632], ![194, -104992, 0]], ![![-147, 11557, 394], ![35, -25347, 0]]]
  g := ![![![1, 0, 0], ![-87, 193, 0], ![-21, 0, 193]], ![![0, 1, 0], ![-40, 88, 3], ![7, -35, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![113, -93, 1]] ![![193, 0, 0], ![87, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![16791, 193, 0]], ![![21809, -17949, 193], ![10036, -8106, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![87, 1, 0]]], ![![![113, -93, 1]], ![![52, -42, -1]]]]
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


lemma PB262I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB262I3 : PrimesBelowBoundCertificateInterval O 137 193 262 where
  m := 11
  g := ![2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB262I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
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
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
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
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [], [], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
