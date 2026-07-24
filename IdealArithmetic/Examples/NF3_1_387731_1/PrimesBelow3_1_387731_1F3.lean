
import IdealArithmetic.Examples.NF3_1_387731_1.RI3_1_387731_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [15, 4, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 15, 83], [118, 123, 56], [0, 1]]
 g := ![![[18, 22, 112], [0, 38, 36], [54, 51], [38, 91, 96], [86, 120], [126, 1], []], ![[17, 49, 11, 55], [24, 56, 5, 107], [25, 100], [77, 15, 102, 7], [1, 57], [49, 117], [86, 78]], ![[32, 110, 134, 60], [124, 17, 60, 94], [69, 67], [56, 18, 63, 84], [126, 71], [128, 86], [113, 78]]]
 h' := ![![[8, 15, 83], [0, 14, 23], [81, 19, 6], [125, 4, 107], [39, 54, 42], [56, 37, 26], [0, 0, 1], [0, 1]], ![[118, 123, 56], [131, 98, 99], [105, 8, 91], [52, 101, 10], [131, 122, 57], [29, 96, 14], [25, 116, 123], [8, 15, 83]], ![[0, 1], [54, 27, 17], [81, 112, 42], [137, 34, 22], [30, 102, 40], [35, 6, 99], [136, 23, 15], [118, 123, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 64], []]
 b := ![[], [31, 17, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [15, 4, 13, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23491, -234215, -297877]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169, -1685, -2143]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [13, 36, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 138, 52], [84, 10, 97], [0, 1]]
 g := ![![[148, 61, 80], [78, 133], [45, 133, 95], [104, 142], [27, 38, 47], [97, 1], []], ![[10, 134, 74, 34], [67, 20], [47, 88, 12, 10], [108, 88], [85, 45, 130, 3], [64, 100], [96, 22]], ![[17, 95, 102, 34], [53, 110], [95, 43, 121, 98], [90, 129], [114, 119, 13, 8], [5, 121], [51, 22]]]
 h' := ![![[13, 138, 52], [1, 128, 123], [11, 124, 27], [116, 58, 63], [96, 17, 80], [80, 71, 135], [0, 0, 1], [0, 1]], ![[84, 10, 97], [68, 63, 138], [55, 140, 13], [92, 90, 70], [119, 9, 45], [17, 34, 125], [113, 144, 10], [13, 138, 52]], ![[0, 1], [91, 107, 37], [66, 34, 109], [83, 1, 16], [106, 123, 24], [131, 44, 38], [135, 5, 138], [84, 10, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 89], []]
 b := ![[], [74, 132, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [13, 36, 52, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4768, 62431, 128438]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, 419, 862]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [70, 119, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 12, 128], [91, 138, 23], [0, 1]]
 g := ![![[14, 3, 139], [114, 60, 78], [83, 141, 11], [44, 44], [108, 140, 59], [17, 1], []], ![[55, 106, 57, 20], [16, 121, 44, 94], [32, 41, 57, 72], [71, 84], [96, 1, 51, 121], [76, 18], [136, 76]], ![[122, 48, 89, 57], [85, 106, 102, 83], [38, 121, 127, 119], [85, 76], [41, 97, 20, 134], [52, 144], [90, 76]]]
 h' := ![![[77, 12, 128], [23, 102, 21], [79, 124, 57], [40, 42, 39], [141, 20, 73], [18, 21, 19], [0, 0, 1], [0, 1]], ![[91, 138, 23], [114, 74, 99], [32, 6, 31], [31, 94, 37], [13, 3, 101], [148, 60, 25], [33, 125, 138], [77, 12, 128]], ![[0, 1], [19, 126, 31], [7, 21, 63], [34, 15, 75], [104, 128, 128], [6, 70, 107], [18, 26, 12], [91, 138, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 61], []]
 b := ![[], [62, 135, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [70, 119, 134, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![279199, 0, 5587]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1849, 0, 37]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![74, -70, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![74, -70, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![74, 87, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![74, -70, 1], ![4, -25, -280], ![-281, 2031, 45]]]
  hmulB := by decide  
  f := ![![![-73, 70, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -87, 157]], ![![0, -1, 1], ![132, 155, -280], ![-23, -12, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [101, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 156], [0, 1]]
 g := ![![[43, 14], [64], [86, 75], [15, 35], [139, 121], [140], [1]], ![[0, 143], [64], [136, 82], [143, 122], [115, 36], [140], [1]]]
 h' := ![![[53, 156], [62, 64], [106, 8], [55, 46], [91, 52], [143, 11], [56, 53], [0, 1]], ![[0, 1], [0, 93], [59, 149], [138, 111], [21, 105], [98, 146], [39, 104], [53, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [67, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [101, 104, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![269, -1171, -3287]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1551, 1814, -3287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-34, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-34, 1, 0]] 
 ![![157, 0, 0], ![123, 1, 0], ![112, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-34, 1, 0], ![0, -33, 4], ![4, -29, -34]]]
  hmulB := by decide  
  f := ![![![4047, -119, 0], ![18683, 0, 0]], ![![3197, -94, 0], ![14759, 0, 0]], ![![2884, -60, -3], ![13314, 118, 0]]]
  g := ![![![1, 0, 0], ![-123, 157, 0], ![-112, 0, 157]], ![![-1, 1, 0], ![23, -33, 4], ![47, -29, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![74, -70, 1]] ![![157, 0, 0], ![-34, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5338, 157, 0]], ![![11618, -10990, 157], ![-2512, 2355, -314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-34, 1, 0]]], ![![![74, -70, 1]], ![![-16, 15, -2]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [24, 72, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 58], [93, 104], [0, 1]]
 g := ![![[21, 90, 53], [81, 17, 39], [42, 22], [13, 121], [19, 55], [144, 78, 1], []], ![[1, 42, 133], [125, 119, 144], [38, 135], [154, 9], [9, 93], [14, 13, 104], []], ![[119, 31, 140], [96, 27, 143], [132, 6], [19, 33], [81, 15], [73, 72, 58], []]]
 h' := ![![[148, 58], [12, 51, 85], [89, 11, 107], [49, 48, 115], [144, 95, 152], [130, 148, 50], [0, 0, 1], [0, 1]], ![[93, 104], [116, 128, 38], [38, 115, 44], [102, 77, 61], [156, 37, 160], [32, 150, 147], [62, 53, 104], [148, 58]], ![[0, 1], [63, 147, 40], [63, 37, 12], [121, 38, 150], [67, 31, 14], [50, 28, 129], [10, 110, 58], [93, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122], []]
 b := ![[], [43, 97, 158], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [24, 72, 85, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28036, -288999, -399513]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![172, -1773, -2451]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![11, 76, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![11, 76, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![11, 76, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![11, 76, 1], ![4, 58, 304], ![303, -2203, -18]]]
  hmulB := by decide  
  f := ![![![-10, -76, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -76, 167]], ![![0, 0, 1], ![-20, -138, 304], ![3, -5, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [42, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 166], [0, 1]]
 g := ![![[91, 4], [152, 133], [92, 144], [144], [132], [86, 27], [1]], ![[0, 163], [7, 34], [156, 23], [144], [132], [98, 140], [1]]]
 h' := ![![[19, 166], [129, 2], [144, 48], [29, 12], [137, 12], [62, 93], [125, 19], [0, 1]], ![[0, 1], [0, 165], [54, 119], [90, 155], [31, 155], [159, 74], [152, 148], [19, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [20, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [42, 148, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6230, -63639, -97159]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6437, 43835, -97159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![30, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![30, 1, 0]] 
 ![![167, 0, 0], ![30, 1, 0], ![18, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![30, 1, 0], ![0, 31, 4], ![4, -29, 30]]]
  hmulB := by decide  
  f := ![![![871, 29, 0], ![-4843, 0, 0]], ![![150, 5, 0], ![-834, 0, 0]], ![![54, -6, -1], ![-300, 42, 0]]]
  g := ![![![1, 0, 0], ![-30, 167, 0], ![-18, 0, 167]], ![![0, 1, 0], ![-6, 31, 4], ![2, -29, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![11, 76, 1]] ![![167, 0, 0], ![30, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![5010, 167, 0]], ![![1837, 12692, 167], ![334, 2338, 334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![30, 1, 0]]], ![![![11, 76, 1]], ![![2, 14, 2]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [16, 58, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 34, 137], [6, 138, 36], [0, 1]]
 g := ![![[51, 50, 122], [27, 85], [106, 72, 67], [143, 153, 160], [110, 40], [26, 55, 1], []], ![[67, 109, 58, 130], [48, 157], [69, 93, 82, 88], [125, 43, 141, 33], [144, 43], [38, 171, 74, 15], [151, 85]], ![[1, 86, 58, 135], [141, 38], [141, 95, 76, 113], [157, 89, 104, 172], [80, 36], [116, 53, 88, 96], [79, 85]]]
 h' := ![![[49, 34, 137], [32, 99, 45], [34, 103, 137], [134, 141, 97], [26, 157, 81], [103, 34, 127], [0, 0, 1], [0, 1]], ![[6, 138, 36], [56, 54, 51], [85, 62, 147], [52, 146, 6], [103, 103, 163], [37, 9, 40], [158, 134, 138], [49, 34, 137]], ![[0, 1], [34, 20, 77], [53, 8, 62], [23, 59, 70], [110, 86, 102], [51, 130, 6], [156, 39, 34], [6, 138, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 126], []]
 b := ![[], [19, 74, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [16, 58, 118, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6747, 52765, 16262]
  a := ![-1, 2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, 305, 94]
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



lemma PB177I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 176 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 176 (by omega)

def PB177I3 : PrimesBelowBoundCertificateInterval O 137 176 177 where
  m := 7
  g := ![1, 1, 1, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB177I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![5177717]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
  β := ![I157N1, I167N1]
  Il := ![[], [], [], [I157N1], [], [I167N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
