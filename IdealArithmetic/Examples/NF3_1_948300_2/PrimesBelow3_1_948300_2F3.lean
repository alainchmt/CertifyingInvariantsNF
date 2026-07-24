
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8595628209211860762, -1865786051308766708, -477408023931921477]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-8595628209211860762, -1865786051308766708, -477408023931921477]] 
 ![![139, 0, 0], ![0, 139, 0], ![85, 63, 1]] where
  M :=![![![-8595628209211860762, -1865786051308766708, -477408023931921477], ![-92183594663279764261, -20009574739159057010, -5119950129994378647], ![-301677544805221877650, -65482794438158701303, -16755410660473445071]]]
  hmulB := by decide  
  f := ![![![-1197397271, -508648117, 189544746]], ![![37848963079, 2084849532, -1715489097]], ![![15513273755, 641155455, -637933951]]]
  g := ![![![230101106654686797, 202956255082030837, -477408023931921477], ![2467713427239154106, 2176599161514293509, -5119950129994378647], ![8075772383705186715, 7123079691882506030, -16755410660473445071]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [11, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 138], [0, 1]]
 g := ![![[3, 38], [131, 89], [34], [1, 78], [129], [116], [1]], ![[0, 101], [113, 50], [34], [68, 61], [129], [116], [1]]]
 h' := ![![[106, 138], [88, 49], [25, 28], [128, 112], [13, 83], [96, 95], [128, 106], [0, 1]], ![[0, 1], [0, 90], [74, 111], [46, 27], [54, 56], [19, 44], [105, 33], [106, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [98, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [11, 33, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1163, 705, 84]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -33, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1197397271, -508648117, 189544746]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1197397271, -508648117, 189544746]] 
 ![![139, 0, 0], ![90, 1, 0], ![96, 0, 1]] where
  M :=![![![-1197397271, -508648117, 189544746], ![37848963079, 2084849532, -1715489097], ![-126360853997, 1010177674, 3291690512]]]
  hmulB := by decide  
  f := ![![![-8595628209211860762, -1865786051308766708, -477408023931921477]], ![![-6228705996347821819, -1352016686021209070, -345947282617750443]], ![![-8106891027982449718, -1759699678876261189, -450263172359265517]]]
  g := ![![![189817537, -508648117, 189544746], ![107190349, 2084849532, -1715489097], ![-3836540531, 1010177674, 3291690512]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-8595628209211860762, -1865786051308766708, -477408023931921477]] ![![-1197397271, -508648117, 189544746]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [144, 148, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 147, 97], [119, 1, 52], [0, 1]]
 g := ![![[40, 112, 125], [134, 61], [24, 25, 116], [74, 24], [1, 116, 25], [21, 1], []], ![[56, 142, 83, 147], [43, 25], [68, 121, 44, 139], [137, 4], [55, 73, 64, 98], [130, 1], [74, 22]], ![[130, 48, 46, 139], [12, 103], [110, 27, 6, 75], [52, 86], [89, 84, 47, 135], [4, 4], [119, 22]]]
 h' := ![![[51, 147, 97], [21, 57, 42], [120, 22, 106], [97, 34, 50], [5, 133, 60], [105, 26, 144], [0, 0, 1], [0, 1]], ![[119, 1, 52], [17, 89, 58], [139, 71, 5], [40, 124, 70], [139, 24, 147], [135, 48, 133], [140, 129, 1], [51, 147, 97]], ![[0, 1], [11, 3, 49], [139, 56, 38], [72, 140, 29], [40, 141, 91], [45, 75, 21], [5, 20, 147], [119, 1, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 117], []]
 b := ![[], [19, 135, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [144, 148, 128, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3417017, 1687872, 280120]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22933, 11328, 1880]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-6, -29, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-6, -29, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![145, 122, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-6, -29, 1], ![226, -15, -88], ![-5851, -521, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-145, -122, 151]], ![![-1, -1, 1], ![86, 71, -88], ![-81, -39, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [82, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 150], [0, 1]]
 g := ![![[57, 68], [84, 16], [47, 123], [99], [127, 84], [49], [1]], ![[80, 83], [45, 135], [2, 28], [99], [111, 67], [49], [1]]]
 h' := ![![[7, 150], [58, 81], [72, 4], [61, 127], [5, 34], [139, 101], [69, 7], [0, 1]], ![[0, 1], [21, 70], [100, 147], [44, 24], [92, 117], [91, 50], [118, 144], [7, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [20, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [82, 144, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1066121, 431123, 88199]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77634, -68405, 88199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-63, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-63, 1, 0]] 
 ![![151, 0, 0], ![88, 1, 0], ![107, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-63, 1, 0], ![-1, -62, 3], ![197, 20, -64]]]
  hmulB := by decide  
  f := ![![![-7025, -439519, 21267], ![151, -1070439, 0]], ![![-4067, -256123, 12393], ![152, -623781, 0]], ![![-4993, -311447, 15070], ![71, -758523, 0]]]
  g := ![![![1, 0, 0], ![-88, 151, 0], ![-107, 0, 151]], ![![-1, 1, 0], ![34, -62, 3], ![35, 20, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-6, -29, 1]] ![![151, 0, 0], ![-63, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-9513, 151, 0]], ![![-906, -4379, 151], ![604, 1812, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-63, 1, 0]]], ![![![-6, -29, 1]], ![![4, 12, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-3, 15, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-3, 15, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![154, 15, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-3, 15, 1], ![182, 32, 44], ![2817, 359, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -15, 157]], ![![-1, 0, 1], ![-42, -4, 44], ![15, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [92, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 156], [0, 1]]
 g := ![![[13, 12], [132], [137, 42], [113, 47], [29, 130], [146], [1]], ![[105, 145], [132], [145, 115], [107, 110], [136, 27], [146], [1]]]
 h' := ![![[60, 156], [154, 144], [113, 17], [123, 102], [1, 138], [56, 75], [65, 60], [0, 1]], ![[0, 1], [2, 13], [34, 140], [120, 55], [117, 19], [3, 82], [54, 97], [60, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [144, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [92, 97, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5289, 3994, 507]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-531, -23, 507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-44, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-44, 1, 0]] 
 ![![157, 0, 0], ![113, 1, 0], ![154, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-44, 1, 0], ![-1, -43, 3], ![197, 20, -45]]]
  hmulB := by decide  
  f := ![![![-3915, -170281, 11880], ![157, -621720, 0]], ![![-2805, -122551, 8550], ![158, -447450, 0]], ![![-3850, -167027, 11653], ![119, -609840, 0]]]
  g := ![![![1, 0, 0], ![-113, 157, 0], ![-154, 0, 157]], ![![-1, 1, 0], ![28, -43, 3], ![31, 20, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-3, 15, 1]] ![![157, 0, 0], ![-44, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6908, 157, 0]], ![![-471, 2355, 157], ![314, -628, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-44, 1, 0]]], ![![![-3, 15, 1]], ![![2, -4, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [4, 140, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 20, 17], [24, 142, 146], [0, 1]]
 g := ![![[36, 73, 143], [116, 61, 58], [25, 97], [65, 104], [120, 35], [79, 43, 1], []], ![[119, 153, 64, 17], [89, 98, 23, 23], [82, 55], [80, 4], [90, 4], [8, 151, 53, 162], [67, 126]], ![[91, 1, 70, 26], [106, 18, 27, 97], [161, 87], [116, 39], [63, 126], [151, 30, 47, 46], [101, 126]]]
 h' := ![![[19, 20, 17], [25, 32, 119], [85, 22, 104], [48, 146, 74], [109, 149, 105], [10, 15, 144], [0, 0, 1], [0, 1]], ![[24, 142, 146], [127, 138, 1], [69, 41, 146], [87, 119, 113], [154, 140, 2], [158, 61, 2], [93, 4, 142], [19, 20, 17]], ![[0, 1], [71, 156, 43], [82, 100, 76], [143, 61, 139], [66, 37, 56], [36, 87, 17], [9, 159, 20], [24, 142, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 75], []]
 b := ![[], [65, 142, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [4, 140, 120, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-314916, 3260, 4890]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1932, 20, 30]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [133, 13, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 12, 30], [72, 154, 137], [0, 1]]
 g := ![![[37, 106, 85], [76, 67, 122], [131, 109, 132], [160, 157], [56, 8], [23, 161, 1], []], ![[19, 94, 20, 155], [0, 79, 44, 153], [62, 51, 105, 51], [111, 7], [151, 130], [23, 77, 72, 60], [163, 65]], ![[61, 32, 3, 8], [100, 85], [29, 72, 122, 137], [62, 84], [133, 44], [164, 163, 73, 22], [56, 65]]]
 h' := ![![[89, 12, 30], [79, 140, 69], [112, 107, 17], [129, 65, 93], [37, 90, 149], [114, 165, 141], [0, 0, 1], [0, 1]], ![[72, 154, 137], [107, 33, 130], [30, 65, 150], [129, 143, 73], [14, 72, 95], [97, 23, 111], [103, 56, 154], [89, 12, 30]], ![[0, 1], [68, 161, 135], [56, 162], [1, 126, 1], [8, 5, 90], [50, 146, 82], [74, 111, 12], [72, 154, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 6], []]
 b := ![[], [135, 100, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [133, 13, 6, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9076116, 2111047, 500165]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54348, 12641, 2995]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241714, 52467, 13425]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![241714, 52467, 13425]] 
 ![![173, 0, 0], ![0, 173, 0], ![165, 67, 1]] where
  M :=![![![241714, 52467, 13425], ![2592258, 562681, 143976], ![8483349, 1841415, 471172]]]
  hmulB := by decide  
  f := ![![![-196, 87, -21]], ![![-4224, -529, 282]], ![![-1707, -119, 85]]]
  g := ![![![-11407, -4896, 13425], ![-122334, -52507, 143976], ![-400347, -171833, 471172]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [133, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 172], [0, 1]]
 g := ![![[98, 160], [116], [116, 139], [45, 35], [163], [96, 21], [1]], ![[0, 13], [116], [46, 34], [56, 138], [163], [68, 152], [1]]]
 h' := ![![[114, 172], [65, 92], [142, 156], [70, 73], [64, 30], [34, 63], [40, 114], [0, 1]], ![[0, 1], [0, 81], [107, 17], [88, 100], [24, 143], [123, 110], [61, 59], [114, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [144, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [133, 59, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3592, 846, 103]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119, -35, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![196, -87, 21]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![196, -87, 21]] 
 ![![173, 0, 0], ![146, 1, 0], ![54, 0, 1]] where
  M :=![![![196, -87, 21], ![4224, 529, -282], ![-20037, -501, 724]]]
  hmulB := by decide  
  f := ![![![-241714, -52467, -13425]], ![![-218974, -47531, -12162]], ![![-124485, -27021, -6914]]]
  g := ![![![68, -87, 21], ![-334, 529, -282], ![81, -501, 724]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![241714, 52467, 13425]] ![![196, -87, 21]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![33, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![33, 1, 0]] 
 ![![179, 0, 0], ![33, 1, 0], ![103, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![33, 1, 0], ![-1, 34, 3], ![197, 20, 32]]]
  hmulB := by decide  
  f := ![![![-3528, 118863, 10488], ![179, -625784, 0]], ![![-677, 21895, 1932], ![180, -115276, 0]], ![![-2031, 68396, 6035], ![108, -360088, 0]]]
  g := ![![![1, 0, 0], ![-33, 179, 0], ![-103, 0, 179]], ![![0, 1, 0], ![-8, 34, 3], ![-21, 20, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![71, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![71, 1, 0]] 
 ![![179, 0, 0], ![71, 1, 0], ![26, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![71, 1, 0], ![-1, 72, 3], ![197, 20, 70]]]
  hmulB := by decide  
  f := ![![![-4942, 350783, 14616], ![179, -872088, 0]], ![![-2003, 139103, 5796], ![180, -345828, 0]], ![![-769, 50951, 2123], ![155, -126672, 0]]]
  g := ![![![1, 0, 0], ![-71, 179, 0], ![-26, 0, 179]], ![![0, 1, 0], ![-29, 72, 3], ![-17, 20, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![75, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![75, 1, 0]] 
 ![![179, 0, 0], ![75, 1, 0], ![9, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![75, 1, 0], ![-1, 76, 3], ![197, 20, 74]]]
  hmulB := by decide  
  f := ![![![-2812, 208087, 8214], ![179, -490102, 0]], ![![-1222, 87171, 3441], ![180, -205313, 0]], ![![-177, 10462, 413], ![94, -24642, 0]]]
  g := ![![![1, 0, 0], ![-75, 179, 0], ![-9, 0, 179]], ![![0, 1, 0], ![-32, 76, 3], ![-11, 20, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![33, 1, 0]] ![![179, 0, 0], ![71, 1, 0]]
  ![![179, 0, 0], ![5, 35, 1]] where
 M := ![![![32041, 0, 0], ![12709, 179, 0]], ![![5907, 179, 0], ![2342, 105, 3]]]
 hmul := by decide  
 g := ![![![![174, -35, -1], ![179, 0, 0]], ![![66, -34, -1], ![179, 0, 0]]], ![![![28, -34, -1], ![179, 0, 0]], ![![13, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![5, 35, 1]] ![![179, 0, 0], ![75, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![13425, 179, 0]], ![![895, 6265, 179], ![537, 2685, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![75, 1, 0]]], ![![![5, 35, 1]], ![![3, 15, 1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![15, -19, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![15, -19, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![15, 162, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![15, -19, 1], ![216, 16, -58], ![-3881, -321, 55]]]
  hmulB := by decide  
  f := ![![![-14, 19, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -162, 181]], ![![0, -1, 1], ![6, 52, -58], ![-26, -51, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [90, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 180], [0, 1]]
 g := ![![[172, 108], [3], [117, 25], [64], [58, 136], [108, 156], [1]], ![[48, 73], [3], [95, 156], [64], [170, 45], [130, 25], [1]]]
 h' := ![![[86, 180], [30, 17], [149, 148], [149, 176], [29, 8], [54, 90], [91, 86], [0, 1]], ![[0, 1], [44, 164], [26, 33], [81, 5], [174, 173], [11, 91], [66, 95], [86, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [12, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [90, 95, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2019, 3126, 1293]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -1140, 1293]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![58, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![58, 1, 0]] 
 ![![181, 0, 0], ![58, 1, 0], ![126, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![58, 1, 0], ![-1, 59, 3], ![197, 20, 57]]]
  hmulB := by decide  
  f := ![![![-2014, 115462, 5871], ![181, -354217, 0]], ![![-685, 36992, 1881], ![182, -113487, 0]], ![![-1394, 80377, 4087], ![101, -246582, 0]]]
  g := ![![![1, 0, 0], ![-58, 181, 0], ![-126, 0, 181]], ![![0, 1, 0], ![-21, 59, 3], ![-45, 20, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![15, -19, 1]] ![![181, 0, 0], ![58, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![10498, 181, 0]], ![![2715, -3439, 181], ![1086, -1086, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![58, 1, 0]]], ![![![15, -19, 1]], ![![6, -6, 0]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [81, 175, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 148, 127], [166, 42, 64], [0, 1]]
 g := ![![[172, 64, 3], [157, 177, 80], [165, 189, 98], [189, 111, 92], [185, 46, 103], [21, 177, 1], []], ![[90, 61, 17, 66], [118, 157, 82, 127], [110, 152, 164, 87], [41, 34, 189, 113], [26, 156, 19, 174], [63, 124, 51, 176], [112, 85]], ![[70, 41, 29, 177], [99, 110, 69, 128], [150, 121, 179, 12], [46, 7, 56, 25], [20, 4, 140, 96], [165, 185, 70, 107], [175, 85]]]
 h' := ![![[11, 148, 127], [80, 42, 24], [5, 14, 135], [162, 74, 17], [104, 131, 130], [18, 133, 165], [0, 0, 1], [0, 1]], ![[166, 42, 64], [20, 137, 39], [40, 85, 190], [81, 160, 180], [150, 37, 132], [41, 23, 137], [26, 73, 42], [11, 148, 127]], ![[0, 1], [58, 12, 128], [185, 92, 57], [27, 148, 185], [169, 23, 120], [36, 35, 80], [11, 118, 148], [166, 42, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 112], []]
 b := ![[], [87, 179, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [81, 175, 14, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2522919, -477500, -105050]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13209, -2500, -550]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![21, -75, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![21, -75, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![21, 118, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![21, -75, 1], ![272, -34, -226], ![-14913, -1441, 117]]]
  hmulB := by decide  
  f := ![![![-20, 75, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -118, 193]], ![![0, -1, 1], ![26, 138, -226], ![-90, -79, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [66, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 192], [0, 1]]
 g := ![![[100, 85], [107], [21], [144], [138], [150], [155, 1]], ![[151, 108], [107], [21], [144], [138], [150], [117, 192]]]
 h' := ![![[155, 192], [97, 49], [37, 53], [74, 54], [11, 181], [137, 36], [192, 27], [0, 1]], ![[0, 1], [165, 144], [146, 140], [145, 139], [81, 12], [120, 157], [131, 166], [155, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [86, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [66, 38, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27786, 1688, 1820]
  a := ![-2, -6, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-342, -1104, 1820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![33, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![33, 1, 0]] 
 ![![193, 0, 0], ![33, 1, 0], ![76, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![33, 1, 0], ![-1, 34, 3], ![197, 20, 32]]]
  hmulB := by decide  
  f := ![![![-19922, 676259, 59670], ![193, -3838770, 0]], ![![-3433, 115599, 10200], ![194, -656200, 0]], ![![-7841, 266299, 23497], ![53, -1511640, 0]]]
  g := ![![![1, 0, 0], ![-33, 193, 0], ![-76, 0, 193]], ![![0, 1, 0], ![-7, 34, 3], ![-15, 20, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![21, -75, 1]] ![![193, 0, 0], ![33, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![6369, 193, 0]], ![![4053, -14475, 193], ![965, -2509, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![33, 1, 0]]], ![![![21, -75, 1]], ![![5, -13, -1]]]]
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


lemma PB276I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB276I3 : PrimesBelowBoundCertificateInterval O 137 193 276 where
  m := 11
  g := ![2, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB276I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
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
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
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
      exact NI179N1
      exact NI179N2
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
  β := ![I139N1, I151N1, I157N1, I173N1, I179N0, I179N1, I179N2, I181N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N1], [], [], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
