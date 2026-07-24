
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![69, 69, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![69, 69, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![69, 69, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![69, 69, 1], ![278, 0, 278], ![9765, 35, 208]]]
  hmulB := by decide  
  f := ![![![-68, -69, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -69, 139]], ![![0, 0, 1], ![-136, -138, 278], ![-33, -103, 208]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [32, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 138], [0, 1]]
 g := ![![[96, 77], [62, 116], [79], [1, 99], [13], [57], [1]], ![[130, 62], [106, 23], [79], [5, 40], [13], [57], [1]]]
 h' := ![![[125, 138], [101, 76], [25, 106], [107, 94], [45, 88], [34, 98], [107, 125], [0, 1]], ![[0, 1], [10, 63], [70, 33], [42, 45], [64, 51], [52, 41], [25, 14], [125, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [102, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [32, 14, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2101, 1267, -32]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 25, -32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![0, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![0, 1, 0]] 
 ![![139, 0, 0], ![0, 1, 0], ![70, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![0, 1, 0], ![2, -1, 4], ![140, 0, 2]]]
  hmulB := by decide  
  f := ![![![-139, 69, -280], ![139, 9730, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-70, 35, -141], ![35, 4900, 0]]]
  g := ![![![1, 0, 0], ![0, 139, 0], ![-70, 0, 139]], ![![0, 1, 0], ![-2, -1, 4], ![0, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![69, 69, 1]] ![![139, 0, 0], ![0, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![0, 139, 0]], ![![9591, 9591, 139], ![278, 0, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![0, 1, 0]]], ![![![69, 69, 1]], ![![2, 0, 2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-35, 30, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-35, 30, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![114, 30, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-35, 30, 1], ![200, -65, 122], ![4305, 35, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -30, 149]], ![![-1, 0, 1], ![-92, -25, 122], ![9, -5, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [82, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 148], [0, 1]]
 g := ![![[143, 20], [85], [132, 39], [148], [85, 49], [88], [1]], ![[0, 129], [85], [99, 110], [148], [55, 100], [88], [1]]]
 h' := ![![[45, 148], [11, 13], [53, 54], [128, 28], [33, 44], [104, 7], [67, 45], [0, 1]], ![[0, 1], [0, 136], [99, 95], [47, 121], [76, 105], [121, 142], [6, 104], [45, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [65, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [82, 104, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-314, 1376, 771]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-592, -146, 771]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![27, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![27, 1, 0]] 
 ![![149, 0, 0], ![27, 1, 0], ![123, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![27, 1, 0], ![2, 26, 4], ![140, 0, 29]]]
  hmulB := by decide  
  f := ![![![15502, 211663, 32568], ![4321, -1213158, 0]], ![![2788, 38344, 5900], ![895, -219775, 0]], ![![12810, 174729, 26885], ![3495, -1001466, 0]]]
  g := ![![![1, 0, 0], ![-27, 149, 0], ![-123, 0, 149]], ![![0, 1, 0], ![-8, 26, 4], ![-23, 0, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-35, 30, 1]] ![![149, 0, 0], ![27, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![4023, 149, 0]], ![![-5215, 4470, 149], ![-745, 745, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![27, 1, 0]]], ![![![-35, 30, 1]], ![![-5, 5, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1053, -108, -64]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-1053, -108, -64]] 
 ![![151, 0, 0], ![0, 151, 0], ![66, 30, 1]] where
  M :=![![![-1053, -108, -64], ![-9176, -945, -560], ![-21840, -2240, -1333]]]
  hmulB := by decide  
  f := ![![![-35, 4, 0]], ![![8, -39, 16]], ![![-10, -6, 3]]]
  g := ![![![21, 12, -64], ![184, 105, -560], ![438, 250, -1333]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [114, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 150], [0, 1]]
 g := ![![[18, 38], [47, 22], [32, 32], [136], [71, 37], [69], [1]], ![[109, 113], [52, 129], [53, 119], [136], [100, 114], [69], [1]]]
 h' := ![![[62, 150], [78, 76], [127, 18], [25, 118], [60, 49], [147, 108], [37, 62], [0, 1]], ![[0, 1], [109, 75], [35, 133], [93, 33], [78, 102], [48, 43], [106, 89], [62, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [65, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [114, 89, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![437456, 152418, 6802]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -342, 6802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -4, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![35, -4, 0]] 
 ![![151, 0, 0], ![29, 1, 0], ![24, 0, 1]] where
  M :=![![![35, -4, 0], ![-8, 39, -16], ![-560, 0, 27]]]
  hmulB := by decide  
  f := ![![![1053, 108, 64]], ![![263, 27, 16]], ![![312, 32, 19]]]
  g := ![![![1, -4, 0], ![-5, 39, -16], ![-8, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-1053, -108, -64]] ![![35, -4, 0]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![65, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![65, 1, 0]] 
 ![![157, 0, 0], ![65, 1, 0], ![138, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![65, 1, 0], ![2, 64, 4], ![140, 0, 67]]]
  hmulB := by decide  
  f := ![![![5909, 243110, 15196], ![4082, -596443, 0]], ![![2429, 100597, 6288], ![1728, -246804, 0]], ![![5191, 213689, 13357], ![3595, -524262, 0]]]
  g := ![![![1, 0, 0], ![-65, 157, 0], ![-138, 0, 157]], ![![0, 1, 0], ![-30, 64, 4], ![-58, 0, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-43, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-43, 1, 0]] 
 ![![157, 0, 0], ![114, 1, 0], ![77, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-43, 1, 0], ![2, -44, 4], ![140, 0, -41]]]
  hmulB := by decide  
  f := ![![![2517, -61022, 5548], ![-942, -217759, 0]], ![![1843, -44304, 4028], ![-627, -158099, 0]], ![![1235, -29928, 2721], ![-460, -106799, 0]]]
  g := ![![![1, 0, 0], ![-114, 157, 0], ![-77, 0, 157]], ![![-1, 1, 0], ![30, -44, 4], ![21, 0, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-23, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-23, 1, 0]] 
 ![![157, 0, 0], ![134, 1, 0], ![98, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-23, 1, 0], ![2, -24, 4], ![140, 0, -21]]]
  hmulB := by decide  
  f := ![![![24948, -308989, 51504], ![-5495, -2021532, 0]], ![![21289, -263706, 43956], ![-4709, -1725273, 0]], ![![15570, -192872, 32149], ![-3448, -1261848, 0]]]
  g := ![![![1, 0, 0], ![-134, 157, 0], ![-98, 0, 157]], ![![-1, 1, 0], ![18, -24, 4], ![14, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![65, 1, 0]] ![![157, 0, 0], ![-43, 1, 0]]
  ![![157, 0, 0], ![-31, -34, 1]] where
 M := ![![![24649, 0, 0], ![-6751, 157, 0]], ![![10205, 157, 0], ![-2793, 21, 4]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![-12, 35, -1], ![157, 0, 0]]], ![![![65, 1, 0], ![0, 0, 0]], ![![-17, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-31, -34, 1]] ![![157, 0, 0], ![-23, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-3611, 157, 0]], ![![-4867, -5338, 157], ![785, 785, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-23, 1, 0]]], ![![![-31, -34, 1]], ![![5, 5, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![68, -35, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![68, -35, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![68, 128, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![68, -35, 1], ![70, 103, -138], ![-4795, 35, -1]]]
  hmulB := by decide  
  f := ![![![-67, 35, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -128, 163]], ![![0, -1, 1], ![58, 109, -138], ![-29, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [39, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 162], [0, 1]]
 g := ![![[107, 46], [162, 158], [118], [118], [119], [116, 150], [1]], ![[0, 117], [0, 5], [118], [118], [119], [86, 13], [1]]]
 h' := ![![[65, 162], [39, 32], [126, 141], [1, 66], [56, 66], [40, 114], [124, 65], [0, 1]], ![[0, 1], [0, 131], [0, 22], [53, 97], [108, 97], [115, 49], [111, 98], [65, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [125, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [39, 98, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![626, 3096, -801]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![338, 648, -801]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-25, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-25, 1, 0]] 
 ![![163, 0, 0], ![138, 1, 0], ![1, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-25, 1, 0], ![2, -26, 4], ![140, 0, -23]]]
  hmulB := by decide  
  f := ![![![-2890, 39203, -6032], ![815, 245804, 0]], ![![-2451, 33172, -5104], ![653, 207988, 0]], ![![-5, 240, -37], ![88, 1508, 0]]]
  g := ![![![1, 0, 0], ![-138, 163, 0], ![-1, 0, 163]], ![![-1, 1, 0], ![22, -26, 4], ![1, 0, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![68, -35, 1]] ![![163, 0, 0], ![-25, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4075, 163, 0]], ![![11084, -5705, 163], ![-1630, 978, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-25, 1, 0]]], ![![![68, -35, 1]], ![![-10, 6, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![26, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![26, 1, 0]] 
 ![![167, 0, 0], ![26, 1, 0], ![5, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![26, 1, 0], ![2, 25, 4], ![140, 0, 28]]]
  hmulB := by decide  
  f := ![![![-1567, -20248, -3240], ![-334, 135270, 0]], ![![-252, -3150, -504], ![1, 21042, 0]], ![![-67, -607, -97], ![119, 4050, 0]]]
  g := ![![![1, 0, 0], ![-26, 167, 0], ![-5, 0, 167]], ![![0, 1, 0], ![-4, 25, 4], ![0, 0, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![51, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![51, 1, 0]] 
 ![![167, 0, 0], ![51, 1, 0], ![31, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![51, 1, 0], ![2, 50, 4], ![140, 0, 53]]]
  hmulB := by decide  
  f := ![![![32200, 923457, 73884], ![15531, -3084657, 0]], ![![9801, 281971, 22560], ![4844, -941880, 0]], ![![5969, 171420, 13715], ![2910, -572601, 0]]]
  g := ![![![1, 0, 0], ![-51, 167, 0], ![-31, 0, 167]], ![![0, 1, 0], ![-16, 50, 4], ![-9, 0, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-78, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-78, 1, 0]] 
 ![![167, 0, 0], ![89, 1, 0], ![130, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-78, 1, 0], ![2, -79, 4], ![140, 0, -76]]]
  hmulB := by decide  
  f := ![![![20481, -1104640, 55936], ![-16032, -2335328, 0]], ![![10927, -588657, 29808], ![-8516, -1244484, 0]], ![![15912, -859899, 43543], ![-12547, -1817920, 0]]]
  g := ![![![1, 0, 0], ![-89, 167, 0], ![-130, 0, 167]], ![![-1, 1, 0], ![39, -79, 4], ![60, 0, -76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![26, 1, 0]] ![![167, 0, 0], ![51, 1, 0]]
  ![![167, 0, 0], ![-2, 19, 1]] where
 M := ![![![27889, 0, 0], ![8517, 167, 0]], ![![4342, 167, 0], ![1328, 76, 4]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![51, 1, 0], ![0, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-2, 19, 1]] ![![167, 0, 0], ![-78, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-13026, 167, 0]], ![![-334, 3173, 167], ![334, -1503, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-78, 1, 0]]], ![![![-2, 19, 1]], ![![2, -9, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-19, 82, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-19, 82, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![154, 82, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-19, 82, 1], ![304, -101, 330], ![11585, 35, 146]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -82, 173]], ![![-1, 0, 1], ![-292, -157, 330], ![-63, -69, 146]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [46, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 172], [0, 1]]
 g := ![![[120, 31], [121], [32, 160], [85, 159], [37], [29, 83], [1]], ![[97, 142], [121], [170, 13], [34, 14], [37], [146, 90], [1]]]
 h' := ![![[16, 172], [102, 66], [85, 162], [69, 92], [106, 141], [50, 146], [127, 16], [0, 1]], ![[0, 1], [120, 107], [82, 11], [157, 81], [113, 32], [137, 27], [37, 157], [16, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [154, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [46, 157, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1686, 1410, -890]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![802, 430, -890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![16, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![16, 1, 0]] 
 ![![173, 0, 0], ![16, 1, 0], ![27, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![16, 1, 0], ![2, 15, 4], ![140, 0, 18]]]
  hmulB := by decide  
  f := ![![![30081, 228456, 60928], ![4152, -2635136, 0]], ![![2768, 21117, 5632], ![520, -243584, 0]], ![![4695, 35655, 9509], ![645, -411264, 0]]]
  g := ![![![1, 0, 0], ![-16, 173, 0], ![-27, 0, 173]], ![![0, 1, 0], ![-2, 15, 4], ![-2, 0, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-19, 82, 1]] ![![173, 0, 0], ![16, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![2768, 173, 0]], ![![-3287, 14186, 173], ![0, 1211, 346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![16, 1, 0]]], ![![![-19, 82, 1]], ![![0, 7, 2]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-69, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-69, 1, 0]] 
 ![![179, 0, 0], ![110, 1, 0], ![46, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-69, 1, 0], ![2, -70, 4], ![140, 0, -67]]]
  hmulB := by decide  
  f := ![![![21026, -912097, 52124], ![-13067, -2332549, 0]], ![![12910, -560445, 32028], ![-8054, -1433253, 0]], ![![5428, -234394, 13395], ![-3294, -599426, 0]]]
  g := ![![![1, 0, 0], ![-110, 179, 0], ![-46, 0, 179]], ![![-1, 1, 0], ![42, -70, 4], ![18, 0, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, -5, -3]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-48, -5, -3]] 
 ![![179, 0, 0], ![137, 1, 0], ![86, 0, 1]] where
  M :=![![![-48, -5, -3], ![-430, -43, -26], ![-1015, -105, -61]]]
  hmulB := by decide  
  f := ![![![107, -10, -1]], ![![81, -7, -1]], ![![43, -5, 0]]]
  g := ![![![5, -5, -3], ![43, -43, -26], ![104, -105, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-69, 1, 0]] ![![179, 0, 0], ![-69, 1, 0]]
  ![![-107, 10, 1]] where
 M := ![![![32041, 0, 0], ![-12351, 179, 0]], ![![-12351, 179, 0], ![4763, -139, 4]]]
 hmul := by decide  
 g := ![![![![8592, 895, 537]], ![![-2882, -302, -181]]], ![![![-2882, -302, -181]], ![![966, 102, 61]]]]
 hle2 := by decide  
def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-107, 10, 1]] ![![-48, -5, -3]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![52, -42, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![52, -42, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![52, 139, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![52, -42, 1], ![56, 94, -166], ![-5775, 35, -31]]]
  hmulB := by decide  
  f := ![![![-51, 42, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -139, 181]], ![![0, -1, 1], ![48, 128, -166], ![-23, 24, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [173, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 180], [0, 1]]
 g := ![![[134, 167], [33], [94, 87], [15], [48, 14], [109, 15], [1]], ![[149, 14], [33], [143, 94], [15], [33, 167], [80, 166], [1]]]
 h' := ![![[167, 180], [143, 158], [28, 24], [61, 79], [22, 167], [148, 106], [8, 167], [0, 1]], ![[0, 1], [103, 23], [54, 157], [41, 102], [37, 14], [112, 75], [23, 14], [167, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [173, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [173, 14, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![183072, 64656, 4175]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188, -2849, 4175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-15, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-15, 1, 0]] 
 ![![181, 0, 0], ![166, 1, 0], ![31, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-15, 1, 0], ![2, -16, 4], ![140, 0, -13]]]
  hmulB := by decide  
  f := ![![![-2033, 16510, -4128], ![362, 186792, 0]], ![![-1861, 15134, -3784], ![363, 171226, 0]], ![![-338, 2827, -707], ![185, 31992, 0]]]
  g := ![![![1, 0, 0], ![-166, 181, 0], ![-31, 0, 181]], ![![-1, 1, 0], ![14, -16, 4], ![3, 0, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![52, -42, 1]] ![![181, 0, 0], ![-15, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-2715, 181, 0]], ![![9412, -7602, 181], ![-724, 724, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-15, 1, 0]]], ![![![52, -42, 1]], ![![-4, 4, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [44, 164, 189, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 53, 59], [95, 137, 132], [0, 1]]
 g := ![![[128, 104, 75], [19, 85, 109], [107, 111, 184], [61, 107, 54], [112, 186, 27], [31, 2, 1], []], ![[79, 162, 96, 16], [101, 11, 6, 130], [93, 163, 85, 102], [31, 133, 10, 23], [47, 143, 56, 45], [121, 171, 101, 144], [37, 43]], ![[54, 167, 44, 38], [66, 133, 59, 185], [79, 93, 2, 183], [155, 161, 154, 178], [143, 181, 28, 88], [174, 51, 103, 57], [155, 43]]]
 h' := ![![[98, 53, 59], [119, 116, 120], [67, 15, 142], [181, 102, 39], [38, 153, 93], [164, 176, 72], [0, 0, 1], [0, 1]], ![[95, 137, 132], [46, 121, 173], [162, 52, 93], [170, 14, 92], [58, 129, 185], [157, 20, 2], [145, 136, 137], [98, 53, 59]], ![[0, 1], [126, 145, 89], [25, 124, 147], [175, 75, 60], [179, 100, 104], [115, 186, 117], [104, 55, 53], [95, 137, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 65], []]
 b := ![[], [21, 149, 164], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [44, 164, 189, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80220, 7258, 2483]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![420, 38, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![83, -34, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![83, -34, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![83, 159, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![83, -34, 1], ![72, 117, -134], ![-4655, 35, 16]]]
  hmulB := by decide  
  f := ![![![-82, 34, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -159, 193]], ![![0, -1, 1], ![58, 111, -134], ![-31, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [100, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 192], [0, 1]]
 g := ![![[62, 83], [25], [42], [137], [96], [187], [169, 1]], ![[0, 110], [25], [42], [137], [96], [187], [145, 192]]]
 h' := ![![[169, 192], [152, 135], [170, 5], [160, 87], [93, 152], [129, 17], [84, 90], [0, 1]], ![[0, 1], [0, 58], [50, 188], [2, 106], [112, 41], [107, 176], [47, 103], [169, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [149, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [100, 24, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5153, 3428, 376]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135, -292, 376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-59, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-59, 1, 0]] 
 ![![193, 0, 0], ![134, 1, 0], ![177, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-59, 1, 0], ![2, -60, 4], ![140, 0, -57]]]
  hmulB := by decide  
  f := ![![![48440, -1667219, 111156], ![-23353, -5363277, 0]], ![![33631, -1157496, 77172], ![-16211, -3723549, 0]], ![![44427, -1529004, 101941], ![-21408, -4918653, 0]]]
  g := ![![![1, 0, 0], ![-134, 193, 0], ![-177, 0, 193]], ![![-1, 1, 0], ![38, -60, 4], ![53, 0, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![83, -34, 1]] ![![193, 0, 0], ![-59, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-11387, 193, 0]], ![![16019, -6562, 193], ![-4825, 2123, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-59, 1, 0]]], ![![![83, -34, 1]], ![![-25, 11, -1]]]]
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


lemma PB205I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB205I3 : PrimesBelowBoundCertificateInterval O 137 193 205 where
  m := 11
  g := ![2, 2, 2, 3, 2, 3, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB205I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![6967871]
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I157N0, I157N1, I157N2, I163N1, I167N0, I167N1, I167N2, I173N1, I179N0, I179N1, I181N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N0, I157N1, I157N2], [I163N1], [I167N0, I167N1, I167N2], [I173N1], [I179N0, I179N0, I179N1], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
