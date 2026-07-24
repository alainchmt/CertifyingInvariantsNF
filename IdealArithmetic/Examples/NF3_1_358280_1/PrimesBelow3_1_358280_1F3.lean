
import IdealArithmetic.Examples.NF3_1_358280_1.RI3_1_358280_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![31, -28, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![31, -28, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![31, 111, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![31, -28, 1], ![-142, 61, -27], ![3834, -952, 34]]]
  hmulB := by decide  
  f := ![![![-30, 28, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -111, 139]], ![![0, -1, 1], ![5, 22, -27], ![20, -34, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [53, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 138], [0, 1]]
 g := ![![[43, 118], [0, 25], [38], [], [], [106], [1]], ![[86, 21], [15, 114], [38], [], [], [106], [1]]]
 h' := ![![[84, 138], [0, 102], [71, 134], [0, 49], [7], [110], [86, 84], [0, 1]], ![[0, 1], [89, 37], [68, 5], [85, 90], [7], [110], [53, 55], [84, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [91, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [53, 55, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-373, -107, -21]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 16, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![27, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![27, 1, 0]] 
 ![![139, 0, 0], ![27, 1, 0], ![105, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![27, 1, 0], ![0, 27, 1], ![-142, 30, 28]]]
  hmulB := by decide  
  f := ![![![1972, 73, 0], ![-10147, 0, 0]], ![![378, 14, 0], ![-1945, 0, 0]], ![![1518, 56, 0], ![-7811, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 139, 0], ![-105, 0, 139]], ![![0, 1, 0], ![-6, 27, 1], ![-28, 30, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![31, -28, 1]] ![![139, 0, 0], ![27, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3753, 139, 0]], ![![4309, -3892, 139], ![695, -695, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![27, 1, 0]]], ![![![31, -28, 1]], ![![5, -5, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![37, -29, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![37, -29, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![37, 120, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![37, -29, 1], ![-142, 67, -28], ![3976, -982, 39]]]
  hmulB := by decide  
  f := ![![![-36, 29, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -120, 149]], ![![0, -1, 1], ![6, 23, -28], ![17, -38, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [64, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 148], [0, 1]]
 g := ![![[107, 7], [54], [68, 63], [132], [48, 148], [36], [1]], ![[0, 142], [54], [148, 86], [132], [42, 1], [36], [1]]]
 h' := ![![[6, 148], [38, 93], [118, 59], [16, 130], [57, 70], [4, 44], [85, 6], [0, 1]], ![[0, 1], [0, 56], [25, 90], [51, 19], [30, 79], [119, 105], [121, 143], [6, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [23, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [64, 143, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![348, -1650, 694]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-170, -570, 694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![28, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![28, 1, 0]] 
 ![![149, 0, 0], ![28, 1, 0], ![110, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![28, 1, 0], ![0, 28, 1], ![-142, 30, 29]]]
  hmulB := by decide  
  f := ![![![393, 14, 0], ![-2086, 0, 0]], ![![28, 1, 0], ![-148, 0, 0]], ![![286, 10, 0], ![-1518, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 149, 0], ![-110, 0, 149]], ![![0, 1, 0], ![-6, 28, 1], ![-28, 30, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![37, -29, 1]] ![![149, 0, 0], ![28, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![4172, 149, 0]], ![![5513, -4321, 149], ![894, -745, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![28, 1, 0]]], ![![![37, -29, 1]], ![![6, -5, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [30, 39, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 19, 44], [136, 131, 107], [0, 1]]
 g := ![![[23, 120, 80], [42, 76, 97], [12, 77, 78], [49, 47], [110, 60, 62], [50, 1], []], ![[123, 38, 33, 20], [132, 84, 150, 137], [53, 105, 146, 38], [145, 43], [101, 57, 45, 37], [30, 98], [20, 124]], ![[27, 103, 13, 35], [68, 122, 129, 120], [83, 57, 79, 87], [113, 99], [121, 73, 145, 115], [60, 59], [108, 124]]]
 h' := ![![[65, 19, 44], [99, 50, 82], [93, 149, 61], [71, 87, 57], [22, 50, 54], [10, 134, 45], [0, 0, 1], [0, 1]], ![[136, 131, 107], [109, 137, 107], [24, 103, 51], [45, 99, 121], [4, 50, 63], [7, 135, 13], [1, 84, 131], [65, 19, 44]], ![[0, 1], [61, 115, 113], [126, 50, 39], [108, 116, 124], [146, 51, 34], [37, 33, 93], [5, 67, 19], [136, 131, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 105], []]
 b := ![[], [109, 116, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [30, 39, 101, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111740, 24613, -3171]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![740, 163, -21]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46099, -1308, 838]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-46099, -1308, 838]] 
 ![![157, 0, 0], ![0, 157, 0], ![10, 79, 1]] where
  M :=![![![-46099, -1308, 838], ![-118996, -20959, -470], ![66740, -133096, -21429]]]
  hmulB := by decide  
  f := ![![![-2462263, 888940, -115786]], ![![16441612, -5935843, 773154]], ![![7417050, -2677745, 348781]]]
  g := ![![![-347, -430, 838], ![-728, 103, -470], ![1790, 9935, -21429]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [82, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 156], [0, 1]]
 g := ![![[106, 90], [82], [63, 67], [9, 154], [148, 25], [109], [1]], ![[0, 67], [82], [12, 90], [23, 3], [136, 132], [109], [1]]]
 h' := ![![[100, 156], [95, 54], [15, 32], [47, 58], [110, 132], [141, 152], [75, 100], [0, 1]], ![[0, 1], [0, 103], [75, 125], [38, 99], [122, 25], [112, 5], [27, 57], [100, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152]]
 b := ![[], [125, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [82, 57, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-286, -1129, 97]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -56, 97]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2462263, 888940, -115786]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-2462263, 888940, -115786]] 
 ![![157, 0, 0], ![77, 1, 0], ![37, 0, 1]] where
  M :=![![![-2462263, 888940, -115786], ![16441612, -5935843, 773154], ![-109787868, 39636232, -5162689]]]
  hmulB := by decide  
  f := ![![![-46099, -1308, 838]], ![![-23367, -775, 408]], ![![-10439, -1156, 61]]]
  g := ![![![-424373, 888940, -115786], ![2833725, -5935843, 773154], ![-18922027, 39636232, -5162689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-46099, -1308, 838]] ![![-2462263, 888940, -115786]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-33, 28, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-33, 28, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![130, 28, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-33, 28, 1], ![-142, -3, 29], ![-4118, 728, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-130, -28, 163]], ![![-1, 0, 1], ![-24, -5, 29], ![-46, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [24, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 162], [0, 1]]
 g := ![![[75, 34], [41, 91], [15], [35], [95], [156, 49], [1]], ![[0, 129], [56, 72], [15], [35], [95], [139, 114], [1]]]
 h' := ![![[156, 162], [157, 69], [62, 108], [52, 129], [27, 19], [5, 101], [139, 156], [0, 1]], ![[0, 1], [0, 94], [121, 55], [127, 34], [57, 144], [113, 62], [25, 7], [156, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [125, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [24, 7, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-402, -59, 27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -5, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-29, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-29, 1, 0]] 
 ![![163, 0, 0], ![134, 1, 0], ![137, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-29, 1, 0], ![0, -29, 1], ![-142, 30, -28]]]
  hmulB := by decide  
  f := ![![![1654, -57, 0], ![9291, 0, 0]], ![![1364, -47, 0], ![7662, 0, 0]], ![![1398, -48, 0], ![7853, 1, 0]]]
  g := ![![![1, 0, 0], ![-134, 163, 0], ![-137, 0, 163]], ![![-1, 1, 0], ![23, -29, 1], ![-2, 30, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-33, 28, 1]] ![![163, 0, 0], ![-29, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4727, 163, 0]], ![![-5379, 4564, 163], ![815, -815, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-29, 1, 0]]], ![![![-33, 28, 1]], ![![5, -5, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![61, 35, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![61, 35, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![61, 35, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![61, 35, 1], ![-142, 91, 36], ![-5112, 938, 127]]]
  hmulB := by decide  
  f := ![![![-60, -35, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -35, 167]], ![![0, 0, 1], ![-14, -7, 36], ![-77, -21, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [145, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 166], [0, 1]]
 g := ![![[20, 108], [131, 32], [45, 81], [108], [162], [127, 47], [1]], ![[112, 59], [16, 135], [114, 86], [108], [162], [99, 120], [1]]]
 h' := ![![[106, 166], [43, 38], [155, 115], [110, 9], [78, 129], [122, 117], [22, 106], [0, 1]], ![[0, 1], [63, 129], [154, 52], [62, 158], [58, 38], [166, 50], [69, 61], [106, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [28, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [145, 61, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5331, 2225, 493]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212, -90, 493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-36, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-36, 1, 0]] 
 ![![167, 0, 0], ![131, 1, 0], ![40, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-36, 1, 0], ![0, -36, 1], ![-142, 30, -35]]]
  hmulB := by decide  
  f := ![![![4753, -132, 0], ![22044, 0, 0]], ![![3709, -103, 0], ![17202, 0, 0]], ![![1160, -32, 0], ![5380, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 167, 0], ![-40, 0, 167]], ![![-1, 1, 0], ![28, -36, 1], ![-16, 30, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![61, 35, 1]] ![![167, 0, 0], ![-36, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-6012, 167, 0]], ![![10187, 5845, 167], ![-2338, -1169, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-36, 1, 0]]], ![![![61, 35, 1]], ![![-14, -7, 0]]]]
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


lemma PB170I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 169 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 169 (by omega)

def PB170I3 : PrimesBelowBoundCertificateInterval O 137 169 170 where
  m := 6
  g := ![2, 2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB170I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
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
  β := ![I139N1, I149N1, I157N1, I163N1, I167N1]
  Il := ![[I139N1], [I149N1], [], [I157N1], [I163N1], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
