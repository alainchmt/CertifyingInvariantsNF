
import IdealArithmetic.Examples.NF3_3_662216_1.RI3_3_662216_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [48, 131, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 78, 89], [119, 60, 50], [0, 1]]
 g := ![![[16, 26, 9], [9, 31, 96], [120, 9], [114, 75, 125], [128, 131], [46, 1], []], ![[71, 43, 3, 44], [93, 35, 71, 100], [122, 121], [121, 55, 63, 112], [10, 54], [136, 125], [31, 137]], ![[31, 99, 70, 115], [118, 73, 135, 84], [72, 64], [52, 130, 133, 26], [100, 1], [16, 107], [70, 137]]]
 h' := ![![[66, 78, 89], [124, 28, 3], [38, 105, 42], [88, 90, 3], [89, 111, 79], [16, 42, 39], [0, 0, 1], [0, 1]], ![[119, 60, 50], [12, 49, 31], [100, 123, 50], [37, 20, 128], [50, 67, 24], [104, 124, 101], [88, 76, 60], [66, 78, 89]], ![[0, 1], [136, 62, 105], [108, 50, 47], [111, 29, 8], [51, 100, 36], [79, 112, 138], [98, 63, 78], [119, 60, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 88], []]
 b := ![[], [12, 6, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [48, 131, 93, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-205859, -81315, -10564]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1481, -585, -76]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245150, -103629, -18210]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-245150, -103629, -18210]] 
 ![![149, 0, 0], ![0, 149, 0], ![34, 142, 1]] where
  M :=![![![-245150, -103629, -18210], ![-3035439, -1283120, -225468], ![-18669159, -7891743, -1386749]]]
  hmulB := by decide  
  f := ![![![200444, 8241, -3972]], ![![-631251, -25960, 12510]], ![![-549857, -22613, 10897]]]
  g := ![![![2510, 16659, -18210], ![31077, 206264, -225468], ![191143, 1268635, -1386749]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [29, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 148], [0, 1]]
 g := ![![[83, 36], [145], [84, 124], [20], [59, 148], [82], [1]], ![[0, 113], [145], [63, 25], [20], [82, 1], [82], [1]]]
 h' := ![![[126, 148], [138, 6], [97, 61], [134, 71], [77, 136], [102, 44], [120, 126], [0, 1]], ![[0, 1], [0, 143], [35, 88], [140, 78], [78, 13], [133, 105], [53, 23], [126, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [119, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [29, 23, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-412, 1531, 1548]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-356, -1465, 1548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![200444, 8241, -3972]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![200444, 8241, -3972]] 
 ![![149, 0, 0], ![13, 1, 0], ![65, 0, 1]] where
  M :=![![![200444, 8241, -3972], ![-631251, -25960, 12510], ![893853, 36789, -17719]]]
  hmulB := by decide  
  f := ![![![-245150, -103629, -18210]], ![![-41761, -17653, -3102]], ![![-232241, -98172, -17251]]]
  g := ![![![2359, 8241, -3972], ![-7429, -25960, 12510], ![10519, 36789, -17719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-245150, -103629, -18210]] ![![200444, 8241, -3972]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [78, 43, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 74, 43], [63, 76, 108], [0, 1]]
 g := ![![[32, 21, 47], [28, 63, 9], [63, 115, 145], [82, 148], [32, 90, 116], [134, 1], []], ![[53, 54, 99, 31], [121, 114, 120, 9], [8, 28, 80, 2], [20, 18], [21, 78, 111, 127], [8, 38], [148, 37]], ![[53, 134, 45, 15], [115, 80, 139, 134], [114, 132, 100, 33], [46, 137], [3, 138, 11, 126], [74, 40], [83, 37]]]
 h' := ![![[71, 74, 43], [81, 2, 54], [69, 115, 148], [4, 108, 121], [71, 92, 65], [118, 49, 95], [0, 0, 1], [0, 1]], ![[63, 76, 108], [136, 130, 113], [110, 55, 36], [120, 150, 99], [64, 92, 138], [80, 71, 116], [141, 50, 76], [71, 74, 43]], ![[0, 1], [82, 19, 135], [31, 132, 118], [116, 44, 82], [82, 118, 99], [35, 31, 91], [62, 101, 74], [63, 76, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 53], []]
 b := ![[], [64, 65, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [78, 43, 17, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6791111297, -3611751333, -1038044064]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44974247, -23918883, -6874464]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [115, 107, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 51, 9], [34, 105, 148], [0, 1]]
 g := ![![[64, 156, 64], [103, 42], [0, 99, 153], [132, 6, 48], [76, 46, 147], [53, 1], []], ![[81, 151, 143, 9], [143, 126], [84, 61, 105, 25], [62, 16, 71, 117], [37, 108, 119, 48], [135, 35], [30, 81]], ![[55, 73, 53, 56], [74, 86], [2, 46, 47, 121], [2, 145, 128, 13], [127, 119, 18, 75], [35, 89], [48, 81]]]
 h' := ![![[19, 51, 9], [87, 6, 149], [0, 122, 55], [49, 136, 101], [52, 79, 131], [28, 23, 33], [0, 0, 1], [0, 1]], ![[34, 105, 148], [107, 65, 156], [99, 127, 122], [91, 68, 54], [70, 145, 22], [107, 28, 61], [51, 89, 105], [19, 51, 9]], ![[0, 1], [35, 86, 9], [99, 65, 137], [55, 110, 2], [22, 90, 4], [139, 106, 63], [32, 68, 51], [34, 105, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 130], []]
 b := ![[], [118, 24, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [115, 107, 104, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2167071, -1093662, -274122]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13803, -6966, -1746]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![538391, 22352, -10704]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![538391, 22352, -10704]] 
 ![![163, 0, 0], ![0, 163, 0], ![157, 100, 1]] where
  M :=![![![538391, 22352, -10704], ![-1700992, -71737, 34000], ![2431936, 107328, -49385]]]
  hmulB := by decide  
  f := ![![![652885, 275984, 48496]], ![![8083840, 3417157, 600464]], ![![5893291, 2491180, 437751]]]
  g := ![![![13613, 6704, -10704], ![-43184, -21299, 34000], ![62487, 30956, -49385]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [148, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 162], [0, 1]]
 g := ![![[29, 14], [144, 88], [55], [24], [150], [4, 145], [1]], ![[88, 149], [119, 75], [55], [24], [150], [161, 18], [1]]]
 h' := ![![[109, 162], [41, 103], [56, 67], [32, 50], [145, 26], [60, 65], [15, 109], [0, 1]], ![[0, 1], [21, 60], [24, 96], [103, 113], [45, 137], [136, 98], [160, 54], [109, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [22, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [148, 54, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1176, 612, 130]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -76, 130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-652885, -275984, -48496]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-652885, -275984, -48496]] 
 ![![163, 0, 0], ![125, 1, 0], ![12, 0, 1]] where
  M :=![![![-652885, -275984, -48496], ![-8083840, -3417157, -600464], ![-49719488, -21017152, -3693141]]]
  hmulB := by decide  
  f := ![![![-538391, -22352, 10704]], ![![-402441, -16701, 8000]], ![![-54556, -2304, 1091]]]
  g := ![![![211209, -275984, -48496], ![2615131, -3417157, -600464], ![16084308, -21017152, -3693141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![538391, 22352, -10704]] ![![-652885, -275984, -48496]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [73, 27, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 135, 91], [3, 31, 76], [0, 1]]
 g := ![![[146, 18, 14], [26, 36, 84], [61, 149, 3], [13, 42], [35, 29], [60, 33, 1], []], ![[77, 32, 67, 103], [143, 116, 34, 120], [145, 153, 133, 79], [106, 7], [43, 8], [64, 145, 156, 110], [82, 98]], ![[102, 154, 148, 54], [21, 37, 116, 29], [75, 83, 11, 33], [55, 121], [12, 97], [105, 91, 5, 2], [97, 98]]]
 h' := ![![[30, 135, 91], [106, 140, 101], [56, 85, 90], [77, 40, 105], [58, 37, 83], [129, 146, 14], [0, 0, 1], [0, 1]], ![[3, 31, 76], [137, 50, 6], [108, 60, 4], [144, 15, 48], [37, 118, 95], [105, 121, 26], [91, 68, 31], [30, 135, 91]], ![[0, 1], [12, 144, 60], [101, 22, 73], [119, 112, 14], [31, 12, 156], [89, 67, 127], [109, 99, 135], [3, 31, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 4], []]
 b := ![[], [139, 57, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [73, 27, 134, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11080283, 4613208, 812622]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66349, 27624, 4866]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120130, -50779, -8922]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-120130, -50779, -8922]] 
 ![![173, 0, 0], ![0, 173, 0], ![130, 111, 1]] where
  M :=![![![-120130, -50779, -8922], ![-1487221, -628684, -110480], ![-9147917, -3866901, -679463]]]
  hmulB := by decide  
  f := ![![![275756, 11335, -5464]], ![![-868369, -35692, 17206]], ![![-342840, -14091, 6793]]]
  g := ![![![6010, 5431, -8922], ![74423, 67252, -110480], ![457701, 413604, -679463]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [150, 118, 1] where
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
 g := ![![[40, 15], [56], [87, 157], [97, 138], [140], [57, 84], [1]], ![[0, 158], [56], [72, 16], [75, 35], [140], [6, 89], [1]]]
 h' := ![![[55, 172], [166, 19], [98, 70], [155, 26], [72, 151], [100, 60], [23, 55], [0, 1]], ![[0, 1], [0, 154], [142, 103], [28, 147], [73, 22], [113, 113], [107, 118], [55, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [76, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [150, 118, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1990, 297, 171]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, -108, 171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-275756, -11335, 5464]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-275756, -11335, 5464]] 
 ![![173, 0, 0], ![123, 1, 0], ![48, 0, 1]] where
  M :=![![![-275756, -11335, 5464], ![868369, 35692, -17206], ![-1229359, -50519, 24357]]]
  hmulB := by decide  
  f := ![![![120130, 50779, 8922]], ![![94007, 39737, 6982]], ![![86209, 36441, 6403]]]
  g := ![![![4949, -11335, 5464], ![-15583, 35692, -17206], ![22054, -50519, 24357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-120130, -50779, -8922]] ![![-275756, -11335, 5464]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [63, 89, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 98, 116], [0, 80, 63], [0, 1]]
 g := ![![[58, 74, 1], [148, 71, 117], [70, 16], [57, 161], [139, 147, 106], [17, 105, 1], []], ![[158, 38, 69, 83], [177, 25, 46, 13], [138, 60], [170, 56], [78, 47, 154, 27], [84, 29, 156, 87], [36, 31]], ![[0, 163, 121, 102], [58, 35, 126, 176], [37, 67], [165, 155], [77, 33, 117, 72], [159, 37, 98, 32], [89, 31]]]
 h' := ![![[105, 98, 116], [163, 74, 1], [101, 13, 81], [6, 112, 4], [14, 36, 124], [3, 106, 74], [0, 0, 1], [0, 1]], ![[0, 80, 63], [43, 121, 72], [153, 43, 112], [75, 173, 66], [89, 143, 134], [73, 4, 137], [165, 29, 80], [105, 98, 116]], ![[0, 1], [105, 163, 106], [57, 123, 165], [132, 73, 109], [161, 0, 100], [7, 69, 147], [121, 150, 98], [0, 80, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 156], []]
 b := ![[], [150, 55, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [63, 89, 74, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2212619, 1135576, 311818]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12361, 6344, 1742]
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



lemma PB181I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 180 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 180 (by omega)

def PB181I3 : PrimesBelowBoundCertificateInterval O 137 180 181 where
  m := 8
  g := ![1, 2, 1, 1, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB181I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
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
  β := ![I149N1, I163N1, I173N1]
  Il := ![[], [I149N1], [], [], [I163N1], [], [I173N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
