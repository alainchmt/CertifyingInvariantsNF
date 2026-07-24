
import IdealArithmetic.Examples.NF3_1_192584_1.RI3_1_192584_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [20, 75, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 18, 38], [38, 64, 45], [0, 1]]
 g := ![![[47, 45, 64], [61, 17, 31], [7, 70], [44, 49], [46, 11, 1], []], ![[56, 62, 21, 41], [2, 56, 37, 23], [37, 31], [13, 70], [49, 2, 31, 23], [71, 33]], ![[58, 67, 26, 55], [28, 15, 54, 56], [53, 70], [31, 31], [29, 4, 29, 55], [64, 33]]]
 h' := ![![[56, 18, 38], [25, 47, 8], [27, 72, 60], [82, 39, 53], [76, 65, 76], [0, 0, 1], [0, 1]], ![[38, 64, 45], [34, 53, 57], [32, 38, 19], [5, 3, 60], [4, 69, 30], [56, 15, 64], [56, 18, 38]], ![[0, 1], [52, 66, 18], [70, 56, 4], [47, 41, 53], [70, 32, 60], [81, 68, 18], [38, 64, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 48], []]
 b := ![[], [31, 7, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [20, 75, 72, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44073, 2075, 4150]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-531, 25, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![195395, 28100, 454]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![195395, 28100, 454]] 
 ![![89, 0, 0], ![0, 89, 0], ![44, 27, 1]] where
  M :=![![![195395, 28100, 454], ![-16846, 203113, 56654], ![-2800514, 459086, 231213]]]
  hmulB := by decide  
  f := ![![![-235430425, 70659104, -16851282]], ![![1738936022, -521902219, 124466926]], ![![340314440, -102137663, 24358511]]]
  g := ![![![1971, 178, 454], ![-28198, -14905, 56654], ![-145774, -64985, 231213]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [23, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 88], [0, 1]]
 g := ![![[3, 68], [18], [84], [62, 34], [49, 44], [1]], ![[28, 21], [18], [84], [30, 55], [39, 45], [1]]]
 h' := ![![[20, 88], [41, 54], [30, 75], [87, 23], [30, 52], [66, 20], [0, 1]], ![[0, 1], [53, 35], [17, 14], [13, 66], [2, 37], [21, 69], [20, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [7, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [23, 69, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1124, -1511, 778]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-372, -253, 778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235430425, 70659104, -16851282]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-235430425, 70659104, -16851282]] 
 ![![89, 0, 0], ![34, 1, 0], ![1, 0, 1]] where
  M :=![![![-235430425, 70659104, -16851282], ![1738936022, -521902219, 124466926], ![-6304348734, 1892107330, -451243115]]]
  hmulB := by decide  
  f := ![![![195395, 28100, 454]], ![![74456, 13017, 810]], ![![-29271, 5474, 2603]]]
  g := ![![![-29449311, 70659104, -16851282], ![217518478, -521902219, 124466926], ![-788592751, 1892107330, -451243115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![195395, 28100, 454]] ![![-235430425, 70659104, -16851282]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, 9, -2]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-38, 9, -2]] 
 ![![97, 0, 0], ![0, 97, 0], ![19, 44, 1]] where
  M :=![![![-38, 9, -2], ![207, -72, 16], ![-809, 235, -63]]]
  hmulB := by decide  
  f := ![![![-8, -1, 0]], ![![-1, -8, -2]], ![![-1, -4, -1]]]
  g := ![![![0, 1, -2], ![-1, -8, 16], ![4, 31, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [37, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 96], [0, 1]]
 g := ![![[89, 88], [6], [64], [70], [47], [5, 1]], ![[44, 9], [6], [64], [70], [47], [10, 96]]]
 h' := ![![[5, 96], [26, 66], [32, 43], [13, 8], [88, 19], [9, 85], [0, 1]], ![[0, 1], [65, 31], [53, 54], [53, 89], [86, 78], [46, 12], [5, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [11, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [37, 92, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167245, -180878, 76430]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16695, -36534, 76430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![97, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![8, 1, 0], ![1, 8, 2], ![-99, 17, 9]]]
  hmulB := by decide  
  f := ![![![38, -9, 2]], ![![1, 0, 0]], ![![15, -4, 1]]]
  g := ![![![0, 1, 0], ![-1, 8, 2], ![-4, 17, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-38, 9, -2]] ![![8, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [79, 44, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 26, 20], [14, 74, 81], [0, 1]]
 g := ![![[97, 9, 22], [9, 33], [4, 11, 80], [77, 9], [36, 22], [1]], ![[5, 14, 68, 79], [61, 16], [18, 3, 30, 64], [75, 6], [68, 49], [70, 6, 53, 21]], ![[24, 28, 29, 95], [7, 19], [58, 52, 67, 87], [40, 47], [63, 45], [82, 46, 60, 80]]]
 h' := ![![[13, 26, 20], [64, 95, 74], [88, 44, 29], [33, 82, 22], [64, 95, 98], [22, 57, 27], [0, 1]], ![[14, 74, 81], [42, 81, 3], [35, 59, 97], [92, 76, 36], [82, 5, 62], [0, 33, 7], [13, 26, 20]], ![[0, 1], [90, 26, 24], [21, 99, 76], [29, 44, 43], [82, 1, 42], [3, 11, 67], [14, 74, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 77], []]
 b := ![[], [54, 74, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [79, 44, 74, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-550551, 112615, -1717]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5451, 1115, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [24, 90, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42, 1], [97, 60, 102], [0, 1]]
 g := ![![[80, 102, 25], [89, 83, 26], [92, 0, 66], [49, 76], [6, 34], [1]], ![[4, 24, 14, 30], [79, 51, 78, 63], [68, 55, 48, 41], [63, 58], [64, 52], [30, 86, 54, 1]], ![[45, 94, 91, 90], [63, 65, 3, 89], [49, 35, 45, 96], [65, 46], [73, 28], [48, 71, 46, 102]]]
 h' := ![![[37, 42, 1], [27, 57, 98], [58, 101, 52], [48, 56, 13], [20, 80, 30], [79, 13, 31], [0, 1]], ![[97, 60, 102], [27, 99, 66], [61, 94, 28], [2, 79, 12], [81, 32, 26], [81, 46, 19], [37, 42, 1]], ![[0, 1], [52, 50, 42], [23, 11, 23], [35, 71, 78], [16, 94, 47], [74, 44, 53], [97, 60, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 83], []]
 b := ![[], [6, 67, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [24, 90, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44084, 2060, 4120]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-428, 20, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33301869, 11675240, 1976766]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![33301869, 11675240, 1976766]] 
 ![![107, 0, 0], ![13, 1, 0], ![23, 0, 1]] where
  M :=![![![33301869, 11675240, 1976766], ![-184024594, 66906891, 25327246], ![-1236896166, 117431674, 78582131]]]
  hmulB := by decide  
  f := ![![![-2283465177774917, 685330298650156, -163442408294534]], ![![-119802977488457, 35956147324019, -8575075876852]], ![![-1062301494533763, 318825707346562, -76035805709403]]]
  g := ![![![-1532167, 11675240, 1976766], ![-15292905, 66906891, 25327246], ![-42718663, 117431674, 78582131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![200546743757980, -60189558015025, 14354430754828]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![200546743757980, -60189558015025, 14354430754828]] 
 ![![107, 0, 0], ![97, 1, 0], ![4, 0, 1]] where
  M :=![![![200546743757980, -60189558015025, 14354430754828], ![-1481278202742997, 444572066590056, -106024685275222], ![5370234582539527, -1611754147203373, 384382508575031]]]
  hmulB := by decide  
  f := ![![![-317232070, 20205931, 17420182]], ![![-303513111, 18120433, 16332614]], ![![-37229373, -2709373, 642969]]]
  g := ![![![55902020076599, -60189558015025, 14354430754828], ![-412903457204463, 444572066590056, -106024685275222], ![1496942587167912, -1611754147203373, 384382508575031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![107, 0, 0], ![103, 1, 0], ![46, 0, 1]] where
  M :=![![![-4, 1, 0], ![1, -4, 2], ![-99, 17, -3]]]
  hmulB := by decide  
  f := ![![![22, -3, -2]], ![![23, -3, -2]], ![![13, -1, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 2], ![-16, 17, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![33301869, 11675240, 1976766]] ![![200546743757980, -60189558015025, 14354430754828]]
  ![![22, -3, -2]] where
 M := ![![![22, -3, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![22, -3, -2]] ![![-4, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62813, -74588, -18228]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-62813, -74588, -18228]] 
 ![![109, 0, 0], ![0, 109, 0], ![84, 10, 1]] where
  M :=![![![-62813, -74588, -18228], ![1729984, -372689, -167404], ![8131560, -520648, -447277]]]
  hmulB := by decide  
  f := ![![![-729694129, 219001148, -52228940]], ![![5389666208, -1617586109, 385773356]], ![![-247131852, 74171022, -17688829]]]
  g := ![![![13471, 988, -18228], ![144880, 11939, -167404], ![419292, 36258, -447277]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [21, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 108], [0, 1]]
 g := ![![[86, 26], [93], [26, 94], [41, 89], [64], [47, 1]], ![[0, 83], [93], [84, 15], [82, 20], [64], [94, 108]]]
 h' := ![![[47, 108], [10, 74], [108, 23], [11, 58], [0, 78], [103, 8], [0, 1]], ![[0, 1], [0, 35], [99, 86], [12, 51], [69, 31], [43, 101], [47, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [15, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [21, 62, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11145, 2823, 1187]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1017, -83, 1187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![729694129, -219001148, 52228940]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![729694129, -219001148, 52228940]] 
 ![![109, 0, 0], ![88, 1, 0], ![107, 0, 1]] where
  M :=![![![729694129, -219001148, 52228940], ![-5389666208, 1617586109, -385773356], ![19539727112, -5864406056, 1398584961]]]
  hmulB := by decide  
  f := ![![![62813, 74588, 18228]], ![![34840, 63637, 16252]], ![![-12941, 77996, 21997]]]
  g := ![![![132232097, -219001148, 52228940], ![-976692612, 1617586109, -385773356], ![3540907057, -5864406056, 1398584961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-62813, -74588, -18228]] ![![729694129, -219001148, 52228940]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [34, 8, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 48, 107], [75, 64, 6], [0, 1]]
 g := ![![[105, 85, 81], [46, 51], [51, 88], [52, 69], [46, 45, 64], [1]], ![[10, 25, 83, 75], [43, 77], [97, 97], [44, 15], [104, 70, 107, 76], [106, 104, 66, 10]], ![[41, 95, 69, 58], [32, 14], [82, 112], [101, 51], [71, 73, 61, 54], [72, 60, 52, 103]]]
 h' := ![![[46, 48, 107], [7, 88, 9], [21, 36, 86], [25, 19, 75], [18, 49, 71], [79, 105, 8], [0, 1]], ![[75, 64, 6], [35, 13, 48], [64, 10, 90], [56, 97, 53], [14, 6, 69], [55, 79, 108], [46, 48, 107]], ![[0, 1], [98, 12, 56], [100, 67, 50], [17, 110, 98], [93, 58, 86], [84, 42, 110], [75, 64, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 111], []]
 b := ![[], [89, 40, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [34, 8, 105, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87914, -2712, 2712]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-778, -24, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀



lemma PB125I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 124 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 124 (by omega)

def PB125I2 : PrimesBelowBoundCertificateInterval O 79 124 125 where
  m := 8
  g := ![1, 2, 2, 1, 1, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB125I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I89N1, I97N1, I107N0, I107N1, I107N2, I109N1]
  Il := ![[], [I89N1], [I97N1], [], [], [I107N0, I107N1, I107N2], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
