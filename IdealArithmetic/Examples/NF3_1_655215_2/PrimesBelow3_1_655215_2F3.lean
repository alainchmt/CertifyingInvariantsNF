
import IdealArithmetic.Examples.NF3_1_655215_2.RI3_1_655215_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [55, 23, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 100, 72], [136, 38, 67], [0, 1]]
 g := ![![[120, 60, 120], [36, 74, 34], [46, 91], [95, 110, 89], [135, 5], [69, 1], []], ![[127, 122, 67, 98], [31, 50, 12, 94], [39, 52], [118, 137, 121, 135], [76, 113], [37, 54], [132, 41]], ![[79, 8, 106, 99], [106, 46, 66, 55], [22, 25], [8, 96, 123, 28], [96, 112], [77, 131], [137, 41]]]
 h' := ![![[72, 100, 72], [105, 126, 113], [24, 109, 112], [57, 20, 77], [38, 135, 111], [97, 26, 12], [0, 0, 1], [0, 1]], ![[136, 38, 67], [47, 112, 22], [123, 6, 11], [105, 53, 57], [54, 30, 38], [131, 13, 104], [9, 74, 38], [72, 100, 72]], ![[0, 1], [108, 40, 4], [98, 24, 16], [125, 66, 5], [54, 113, 129], [57, 100, 23], [119, 65, 100], [136, 38, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 93], []]
 b := ![[], [87, 11, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [55, 23, 70, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36835, 53376, -56990]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![265, 384, -410]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-13, -39, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-13, -39, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![136, 110, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-13, -39, 1], ![120, -87, -78], ![-4740, 1425, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -110, 149]], ![![-1, -1, 1], ![72, 57, -78], ![12, 45, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [91, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 148], [0, 1]]
 g := ![![[100, 20], [5], [140, 144], [35], [61, 112], [121], [1]], ![[29, 129], [5], [46, 5], [35], [21, 37], [121], [1]]]
 h' := ![![[138, 148], [104, 13], [74, 81], [47, 12], [111, 83], [101, 75], [58, 138], [0, 1]], ![[0, 1], [110, 136], [77, 68], [64, 137], [92, 66], [21, 74], [30, 11], [138, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [119, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [91, 11, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81, 690, -522]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![477, 390, -522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-71, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-71, 1, 0]] 
 ![![149, 0, 0], ![78, 1, 0], ![48, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-71, 1, 0], ![0, -70, 2], ![120, -35, -71]]]
  hmulB := by decide  
  f := ![![![4616, -65, 0], ![9685, 0, 0]], ![![2486, -35, 0], ![5216, 0, 0]], ![![1508, 14, -1], ![3164, 75, 0]]]
  g := ![![![1, 0, 0], ![-78, 149, 0], ![-48, 0, 149]], ![![-1, 1, 0], ![36, -70, 2], ![42, -35, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-13, -39, 1]] ![![149, 0, 0], ![-71, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10579, 149, 0]], ![![-1937, -5811, 149], ![1043, 2682, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-71, 1, 0]]], ![![![-13, -39, 1]], ![![7, 18, -1]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [99, 83, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 39, 66], [96, 111, 85], [0, 1]]
 g := ![![[141, 138, 100], [64, 75, 1], [3, 70, 21], [140, 145], [5, 23, 9], [29, 1], []], ![[48, 109, 43, 24], [111, 31, 85, 87], [132, 78, 102, 83], [133, 81], [88, 66, 140, 126], [146, 90], [102, 128]], ![[71, 123, 105, 18], [33, 75, 110, 145], [36, 32, 135, 72], [140, 139], [86, 60, 66, 103], [91, 11], [83, 128]]]
 h' := ![![[84, 39, 66], [6, 123, 141], [5, 23, 1], [135, 44, 126], [109, 30, 121], [149, 61, 3], [0, 0, 1], [0, 1]], ![[96, 111, 85], [139, 110, 62], [103, 52, 119], [2, 40, 129], [118, 95, 9], [73, 146, 131], [129, 61, 111], [84, 39, 66]], ![[0, 1], [12, 69, 99], [41, 76, 31], [71, 67, 47], [48, 26, 21], [93, 95, 17], [93, 90, 39], [96, 111, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 49], []]
 b := ![[], [57, 51, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [99, 83, 122, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![227255, 0, 4530]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1505, 0, 30]
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

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-9, -59, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-9, -59, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![148, 98, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-9, -59, 1], ![120, -103, -118], ![-7140, 2125, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-148, -98, 157]], ![![-1, -1, 1], ![112, 73, -118], ![-4, 41, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [38, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 156], [0, 1]]
 g := ![![[135, 42], [36], [122, 19], [62, 76], [134, 126], [89], [1]], ![[79, 115], [36], [149, 138], [13, 81], [123, 31], [89], [1]]]
 h' := ![![[51, 156], [26, 55], [74, 6], [156, 31], [89, 95], [103, 35], [119, 51], [0, 1]], ![[0, 1], [5, 102], [66, 151], [10, 126], [67, 62], [4, 122], [51, 106], [51, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [59, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [38, 106, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1045, 588, -1407]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1333, 882, -1407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-39, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-39, 1, 0]] 
 ![![157, 0, 0], ![118, 1, 0], ![44, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-39, 1, 0], ![0, -38, 2], ![120, -35, -39]]]
  hmulB := by decide  
  f := ![![![6046, -155, 0], ![24335, 0, 0]], ![![4564, -117, 0], ![18370, 0, 0]], ![![1682, -24, -1], ![6770, 79, 0]]]
  g := ![![![1, 0, 0], ![-118, 157, 0], ![-44, 0, 157]], ![![-1, 1, 0], ![28, -38, 2], ![38, -35, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-9, -59, 1]] ![![157, 0, 0], ![-39, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6123, 157, 0]], ![![-1413, -9263, 157], ![471, 2198, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-39, 1, 0]]], ![![![-9, -59, 1]], ![![3, 14, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-8, 74, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-8, 74, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![155, 74, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-8, 74, 1], ![120, 31, 148], ![8820, -2530, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -74, 163]], ![![-1, 0, 1], ![-140, -67, 148], ![95, 4, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [54, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 162], [0, 1]]
 g := ![![[147, 160], [84, 71], [25], [161], [41], [50, 119], [1]], ![[0, 3], [140, 92], [25], [161], [41], [13, 44], [1]]]
 h' := ![![[49, 162], [28, 46], [47, 87], [147, 5], [56, 145], [71, 81], [109, 49], [0, 1]], ![[0, 1], [0, 117], [72, 76], [66, 158], [152, 18], [128, 82], [65, 114], [49, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [102, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [54, 114, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![954, -104, -649]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![623, 294, -649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![15, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![15, 1, 0]] 
 ![![163, 0, 0], ![15, 1, 0], ![43, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![15, 1, 0], ![0, 16, 2], ![120, -35, 15]]]
  hmulB := by decide  
  f := ![![![1216, 81, 0], ![-13203, 0, 0]], ![![90, 6, 0], ![-977, 0, 0]], ![![316, 13, -1], ![-3431, 82, 0]]]
  g := ![![![1, 0, 0], ![-15, 163, 0], ![-43, 0, 163]], ![![0, 1, 0], ![-2, 16, 2], ![0, -35, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-8, 74, 1]] ![![163, 0, 0], ![15, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![2445, 163, 0]], ![![-1304, 12062, 163], ![0, 1141, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![15, 1, 0]]], ![![![-8, 74, 1]], ![![0, 7, 1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [129, 38, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 45, 147], [72, 121, 20], [0, 1]]
 g := ![![[149, 133, 126], [64, 28, 154], [33, 102, 36], [111, 114], [22, 130], [92, 56, 1], []], ![[137, 157, 122, 65], [78, 126, 34, 152], [103, 37, 36, 58], [144, 124], [141, 115], [107, 20, 159, 98], [59, 66]], ![[129, 71, 121, 79], [3, 1, 80, 165], [123, 30, 12, 125], [56, 147], [42, 12], [41, 166, 158, 86], [19, 66]]]
 h' := ![![[151, 45, 147], [94, 12, 136], [85, 38, 133], [64, 91, 6], [122, 132, 92], [156, 135, 56], [0, 0, 1], [0, 1]], ![[72, 121, 20], [119, 27, 17], [49, 43, 136], [69, 57, 75], [38, 136, 142], [109, 117, 68], [160, 162, 121], [151, 45, 147]], ![[0, 1], [69, 128, 14], [79, 86, 65], [135, 19, 86], [41, 66, 100], [99, 82, 43], [61, 5, 45], [72, 121, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 147], []]
 b := ![[], [91, 71, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [129, 38, 111, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14609661, -5177000, 10553398]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87483, -31000, 63194]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![81, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![81, 1, 0]] 
 ![![173, 0, 0], ![81, 1, 0], ![139, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![81, 1, 0], ![0, 82, 2], ![120, -35, 81]]]
  hmulB := by decide  
  f := ![![![3322, 41, 0], ![-7093, 0, 0]], ![![1620, 20, 0], ![-3459, 0, 0]], ![![2774, -7, -1], ![-5923, 87, 0]]]
  g := ![![![1, 0, 0], ![-81, 173, 0], ![-139, 0, 173]], ![![0, 1, 0], ![-40, 82, 2], ![-48, -35, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-73, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-73, 1, 0]] 
 ![![173, 0, 0], ![100, 1, 0], ![140, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-73, 1, 0], ![0, -72, 2], ![120, -35, -73]]]
  hmulB := by decide  
  f := ![![![9929, -136, 0], ![23528, 0, 0]], ![![5768, -79, 0], ![13668, 0, 0]], ![![8046, -74, -1], ![19066, 87, 0]]]
  g := ![![![1, 0, 0], ![-100, 173, 0], ![-140, 0, 173]], ![![-1, 1, 0], ![40, -72, 2], ![80, -35, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-9, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-9, 1, 0]] 
 ![![173, 0, 0], ![164, 1, 0], ![137, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-9, 1, 0], ![0, -8, 2], ![120, -35, -9]]]
  hmulB := by decide  
  f := ![![![730, -81, 0], ![14013, 0, 0]], ![![694, -77, 0], ![13322, 0, 0]], ![![586, -61, -1], ![11249, 87, 0]]]
  g := ![![![1, 0, 0], ![-164, 173, 0], ![-137, 0, 173]], ![![-1, 1, 0], ![6, -8, 2], ![41, -35, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![81, 1, 0]] ![![173, 0, 0], ![-73, 1, 0]]
  ![![173, 0, 0], ![71, -82, 1]] where
 M := ![![![29929, 0, 0], ![-12629, 173, 0]], ![![14013, 173, 0], ![-5913, 9, 2]]]
 hmul := by decide  
 g := ![![![![102, 82, -1], ![173, 0, 0]], ![![-73, 1, 0], ![0, 0, 0]]], ![![![10, 83, -1], ![173, 0, 0]], ![![-35, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![71, -82, 1]] ![![173, 0, 0], ![-9, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-1557, 173, 0]], ![![12283, -14186, 173], ![-519, 692, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-9, 1, 0]]], ![![![71, -82, 1]], ![![-3, 4, -1]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![22, 19, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![22, 19, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![22, 19, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![22, 19, 1], ![120, 6, 38], ![2220, -605, -13]]]
  hmulB := by decide  
  f := ![![![-21, -19, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -19, 179]], ![![0, 0, 1], ![-4, -4, 38], ![14, -2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [31, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 178], [0, 1]]
 g := ![![[114, 52], [70, 39], [67], [60], [143, 95], [151, 147], [1]], ![[0, 127], [74, 140], [67], [60], [38, 84], [111, 32], [1]]]
 h' := ![![[46, 178], [157, 125], [158, 24], [83, 70], [42, 66], [152, 128], [148, 46], [0, 1]], ![[0, 1], [0, 54], [9, 155], [81, 109], [35, 113], [133, 51], [116, 133], [46, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [2, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [31, 133, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![319, 186, 104]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -10, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-38, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-38, 1, 0]] 
 ![![179, 0, 0], ![141, 1, 0], ![13, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-38, 1, 0], ![0, -37, 2], ![120, -35, -38]]]
  hmulB := by decide  
  f := ![![![3155, -83, 0], ![14857, 0, 0]], ![![2509, -66, 0], ![11815, 0, 0]], ![![289, 11, -1], ![1361, 90, 0]]]
  g := ![![![1, 0, 0], ![-141, 179, 0], ![-13, 0, 179]], ![![-1, 1, 0], ![29, -37, 2], ![31, -35, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![22, 19, 1]] ![![179, 0, 0], ![-38, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-6802, 179, 0]], ![![3938, 3401, 179], ![-716, -716, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-38, 1, 0]]], ![![![22, 19, 1]], ![![-4, -4, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [104, 42, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 106, 72], [123, 74, 109], [0, 1]]
 g := ![![[8, 133, 39], [2, 82], [129, 64, 70], [132, 70], [176, 151, 38], [2, 15, 1], []], ![[114, 136, 134, 146], [13, 56], [49, 0, 157, 23], [153, 166], [59, 160, 128, 74], [123, 0, 86, 54], [171, 116]], ![[67, 54, 4, 57], [31, 59], [122, 78, 57, 151], [111, 67], [178, 134, 62, 151], [111, 133, 84, 78], [134, 116]]]
 h' := ![![[73, 106, 72], [95, 161, 138], [159, 68, 156], [14, 105, 147], [158, 77, 34], [154, 166, 20], [0, 0, 1], [0, 1]], ![[123, 74, 109], [69, 167, 84], [110, 98, 150], [7, 121, 157], [57, 166, 96], [101, 116, 38], [34, 31, 74], [73, 106, 72]], ![[0, 1], [93, 34, 140], [56, 15, 56], [60, 136, 58], [54, 119, 51], [87, 80, 123], [107, 150, 106], [123, 74, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 13], []]
 b := ![[], [116, 119, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [104, 42, 166, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![572684, -163443, 21177]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3164, -903, 117]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-45, -65, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-45, -65, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![146, 126, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-45, -65, 1], ![120, -145, -130], ![-7860, 2335, -80]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -126, 191]], ![![-1, -1, 1], ![100, 85, -130], ![20, 65, -80]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [76, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 190], [0, 1]]
 g := ![![[105, 48], [93, 144], [84, 49], [125, 135], [135, 3], [90, 45], [1]], ![[20, 143], [29, 47], [41, 142], [65, 56], [70, 188], [70, 146], [1]]]
 h' := ![![[42, 190], [190, 96], [110, 12], [50, 7], [54, 53], [36, 24], [115, 42], [0, 1]], ![[0, 1], [20, 95], [41, 179], [153, 184], [179, 138], [89, 167], [160, 149], [42, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [5, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [76, 149, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9738, -2360, -2050]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1618, 1340, -2050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-61, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-61, 1, 0]] 
 ![![191, 0, 0], ![130, 1, 0], ![80, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-61, 1, 0], ![0, -60, 2], ![120, -35, -61]]]
  hmulB := by decide  
  f := ![![![9334, -153, 0], ![29223, 0, 0]], ![![6406, -105, 0], ![20056, 0, 0]], ![![3914, -34, -1], ![12254, 96, 0]]]
  g := ![![![1, 0, 0], ![-130, 191, 0], ![-80, 0, 191]], ![![-1, 1, 0], ![40, -60, 2], ![50, -35, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-45, -65, 1]] ![![191, 0, 0], ![-61, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-11651, 191, 0]], ![![-8595, -12415, 191], ![2865, 3820, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-61, 1, 0]]], ![![![-45, -65, 1]], ![![15, 20, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-41, -25, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-41, -25, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![152, 168, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-41, -25, 1], ![120, -101, -50], ![-3060, 935, -76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-152, -168, 193]], ![![-1, -1, 1], ![40, 43, -50], ![44, 71, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [58, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 192], [0, 1]]
 g := ![![[66, 126], [92], [144], [97], [169], [1], [32, 1]], ![[45, 67], [92], [144], [97], [169], [1], [64, 192]]]
 h' := ![![[32, 192], [62, 133], [90, 142], [170, 181], [44, 26], [14, 180], [74, 1], [0, 1]], ![[0, 1], [72, 60], [2, 51], [172, 12], [104, 167], [177, 13], [106, 192], [32, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [156, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [58, 161, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2260, 60, 152]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108, -132, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![50, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![50, 1, 0]] 
 ![![193, 0, 0], ![50, 1, 0], ![76, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![50, 1, 0], ![0, 51, 2], ![120, -35, 50]]]
  hmulB := by decide  
  f := ![![![7101, 142, 0], ![-27406, 0, 0]], ![![1850, 37, 0], ![-7140, 0, 0]], ![![2732, 29, -1], ![-10544, 97, 0]]]
  g := ![![![1, 0, 0], ![-50, 193, 0], ![-76, 0, 193]], ![![0, 1, 0], ![-14, 51, 2], ![-10, -35, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-41, -25, 1]] ![![193, 0, 0], ![50, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![9650, 193, 0]], ![![-7913, -4825, 193], ![-1930, -1351, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![50, 1, 0]]], ![![![-41, -25, 1]], ![![-10, -7, 0]]]]
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


lemma PB230I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB230I3 : PrimesBelowBoundCertificateInterval O 137 193 230 where
  m := 11
  g := ![1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB230I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
      exact NI173N1
      exact NI173N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N1, I157N1, I163N1, I173N0, I173N1, I173N2, I179N1, I191N1, I193N1]
  Il := ![[], [I149N1], [], [I157N1], [I163N1], [], [I173N0, I173N1, I173N2], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
