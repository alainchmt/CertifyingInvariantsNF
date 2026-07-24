
import IdealArithmetic.Examples.NF3_1_311467_2.RI3_1_311467_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6137, -147, -126]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![6137, -147, -126]] 
 ![![83, 0, 0], ![0, 83, 0], ![31, 15, 1]] where
  M :=![![![6137, -147, -126], ![21168, 719, -273], ![45864, 9429, 446]]]
  hmulB := by decide  
  f := ![![![-34877, 13524, -1575]], ![![264600, -102602, 11949]], ![![10607, -4113, 479]]]
  g := ![![![121, 21, -126], ![357, 58, -273], ![386, 33, 446]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [29, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 82], [0, 1]]
 g := ![![[28, 63], [16, 36], [9], [78], [57, 75], [1]], ![[0, 20], [0, 47], [9], [78], [79, 8], [1]]]
 h' := ![![[18, 82], [34, 35], [25, 77], [28, 80], [7, 24], [54, 18], [0, 1]], ![[0, 1], [0, 48], [0, 6], [57, 3], [24, 59], [46, 65], [18, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [36, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [29, 65, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-475, -104, -18]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 2, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34877, 13524, -1575]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-34877, 13524, -1575]] 
 ![![83, 0, 0], ![67, 1, 0], ![76, 0, 1]] where
  M :=![![![-34877, 13524, -1575], ![264600, -102602, 11949], ![-2007432, 778407, -90653]]]
  hmulB := by decide  
  f := ![![![6137, -147, -126]], ![![5209, -110, -105]], ![![6172, -21, -110]]]
  g := ![![![-9895, 13524, -1575], ![75070, -102602, 11949], ![-569531, 778407, -90653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![6137, -147, -126]] ![![-34877, 13524, -1575]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-20, 43, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-20, 43, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![69, 43, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-20, 43, 1], ![-168, 23, 44], ![-7392, 1724, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -43, 89]], ![![-1, 0, 1], ![-36, -21, 44], ![-135, -13, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [84, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 88], [0, 1]]
 g := ![![[11, 71], [79], [8], [51, 32], [50, 88], [1]], ![[0, 18], [79], [8], [31, 57], [84, 1], [1]]]
 h' := ![![[55, 88], [75, 31], [6, 41], [77, 50], [72, 11], [5, 55], [0, 1]], ![[0, 1], [0, 58], [36, 48], [68, 39], [54, 78], [4, 34], [55, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [31, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [84, 34, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![555, -1705, 484]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-369, -253, 484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-44, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-44, 1, 0]] 
 ![![89, 0, 0], ![45, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-44, 1, 0], ![0, -44, 1], ![-168, 43, -43]]]
  hmulB := by decide  
  f := ![![![3917, -89, 0], ![7921, 0, 0]], ![![2025, -46, 0], ![4095, 0, 0]], ![![990, -22, 0], ![2002, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 89, 0], ![-22, 0, 89]], ![![-1, 1, 0], ![22, -44, 1], ![-13, 43, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-20, 43, 1]] ![![89, 0, 0], ![-44, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3916, 89, 0]], ![![-1780, 3827, 89], ![712, -1869, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-44, 1, 0]]], ![![![-20, 43, 1]], ![![8, -21, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![20, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![20, 1, 0]] 
 ![![97, 0, 0], ![20, 1, 0], ![85, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![20, 1, 0], ![0, 20, 1], ![-168, 43, 21]]]
  hmulB := by decide  
  f := ![![![561, 28, 0], ![-2716, 0, 0]], ![![100, 5, 0], ![-484, 0, 0]], ![![485, 24, 0], ![-2348, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 97, 0], ![-85, 0, 97]], ![![0, 1, 0], ![-5, 20, 1], ![-29, 43, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![38, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![38, 1, 0]] 
 ![![97, 0, 0], ![38, 1, 0], ![11, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![38, 1, 0], ![0, 38, 1], ![-168, 43, 39]]]
  hmulB := by decide  
  f := ![![![723, 19, 0], ![-1843, 0, 0]], ![![266, 7, 0], ![-678, 0, 0]], ![![53, 1, 0], ![-135, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 97, 0], ![-11, 0, 97]], ![![0, 1, 0], ![-15, 38, 1], ![-23, 43, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![20, 1, 0]] ![![97, 0, 0], ![38, 1, 0]]
  ![![97, 0, 0], ![-16, -39, 1]] where
 M := ![![![9409, 0, 0], ![3686, 97, 0]], ![![1940, 97, 0], ![760, 58, 1]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![38, 1, 0], ![0, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-16, -39, 1]] ![![97, 0, 0], ![38, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3686, 97, 0]], ![![-1552, -3783, 97], ![-776, -1455, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![38, 1, 0]]], ![![![-16, -39, 1]], ![![-8, -15, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [28, 30, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 5, 76], [97, 95, 25], [0, 1]]
 g := ![![[17, 6, 36], [50, 71], [71, 54, 52], [93, 52], [86, 19], [1]], ![[48, 13, 13, 37], [31, 80], [71, 75, 97, 24], [88, 92], [5, 36], [13, 8, 25, 30]], ![[74, 13, 56, 80], [9, 4], [84, 15, 98, 58], [27, 1], [30, 58], [41, 9, 19, 71]]]
 h' := ![![[29, 5, 76], [28, 24, 95], [32, 17, 77], [86, 82, 70], [93, 83, 70], [73, 71, 25], [0, 1]], ![[97, 95, 25], [47, 56, 42], [39, 31, 22], [94, 12, 55], [29, 17, 30], [88, 83, 95], [29, 5, 76]], ![[0, 1], [47, 21, 65], [20, 53, 2], [66, 7, 77], [69, 1, 1], [0, 48, 82], [97, 95, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 9], []]
 b := ![[], [68, 55, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [28, 30, 76, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7676, 43531, -9595]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, 431, -95]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6436657, 483960, 175621]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-6436657, 483960, 175621]] 
 ![![103, 0, 0], ![0, 103, 0], ![89, 11, 1]] where
  M :=![![![-6436657, 483960, 175621], ![-29504328, 1115046, 659581], ![-110809608, -1142345, 1774627]]]
  hmulB := by decide  
  f := ![![![26526794129, -10286099555, 1197915798]], ![![-201249854064, 78037173443, -9088183757]], ![![16251952951, -6301900079, 733917227]]]
  g := ![![![-214242, -14057, 175621], ![-856379, -59615, 659581], ![-2609237, -200614, 1774627]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [7, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 102], [0, 1]]
 g := ![![[21, 59], [28, 19], [10, 91], [2], [63], [59, 1]], ![[0, 44], [16, 84], [23, 12], [2], [63], [15, 102]]]
 h' := ![![[59, 102], [10, 33], [33, 88], [49, 83], [75, 65], [102, 75], [0, 1]], ![[0, 1], [0, 70], [75, 15], [2, 20], [99, 38], [98, 28], [59, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [3, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [7, 44, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-452, -1337, 253]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-223, -40, 253]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26526794129, -10286099555, 1197915798]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![26526794129, -10286099555, 1197915798]] 
 ![![103, 0, 0], ![91, 1, 0], ![62, 0, 1]] where
  M :=![![![26526794129, -10286099555, 1197915798], ![-201249854064, 78037173443, -9088183757], ![1526814871176, -592041755615, 68948989686]]]
  hmulB := by decide  
  f := ![![![-6436657, 483960, 175621]], ![![-5973205, 438402, 161564]], ![![-4950314, 280225, 122943]]]
  g := ![![![8624185186, -10286099555, 1197915798], ![-65428788781, 78037173443, -9088183757], ![496386187103, -592041755615, 68948989686]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-6436657, 483960, 175621]] ![![26526794129, -10286099555, 1197915798]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [16, 35, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 48, 73], [86, 58, 34], [0, 1]]
 g := ![![[51, 85, 1], [35, 67, 57], [95, 53], [64, 41, 39], [72, 40], [1]], ![[41, 65, 106, 60], [18, 16, 55, 97], [65, 10], [77, 83, 10, 80], [9, 99], [55, 54, 56, 72]], ![[61, 83, 69, 61], [33, 7, 71, 87], [10, 90], [82, 32, 64, 85], [83, 30], [8, 103, 7, 35]]]
 h' := ![![[40, 48, 73], [82, 33, 1], [61, 73, 59], [46, 95, 38], [67, 100, 50], [91, 72, 19], [0, 1]], ![[86, 58, 34], [85, 1, 6], [71, 94, 84], [24, 46, 44], [63, 15, 35], [97, 22, 45], [40, 48, 73]], ![[0, 1], [34, 73, 100], [96, 47, 71], [91, 73, 25], [43, 99, 22], [27, 13, 43], [86, 58, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 39], []]
 b := ![[], [60, 68, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [16, 35, 88, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35096, 2568, 2568]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-328, 24, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341, 213, 34]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-341, 213, 34]] 
 ![![109, 0, 0], ![0, 109, 0], ![6, 80, 1]] where
  M :=![![![-341, 213, 34], ![-5712, 1121, 247], ![-41496, 4909, 1368]]]
  hmulB := by decide  
  f := ![![![-2945, 1142, -133]], ![![22344, -8664, 1009]], ![![14682, -5693, 663]]]
  g := ![![![-5, -23, 34], ![-66, -171, 247], ![-456, -959, 1368]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [22, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 108], [0, 1]]
 g := ![![[66, 5], [4], [44, 25], [31, 46], [16], [74, 1]], ![[0, 104], [4], [41, 84], [56, 63], [16], [39, 108]]]
 h' := ![![[74, 108], [81, 21], [13, 2], [81, 5], [24, 41], [7, 4], [0, 1]], ![[0, 1], [0, 88], [52, 107], [15, 104], [6, 68], [85, 105], [74, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [41, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [22, 35, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6494, 2212, 480]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -332, 480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2945, 1142, -133]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-2945, 1142, -133]] 
 ![![109, 0, 0], ![28, 1, 0], ![88, 0, 1]] where
  M :=![![![-2945, 1142, -133], ![22344, -8664, 1009], ![-169512, 65731, -7655]]]
  hmulB := by decide  
  f := ![![![-341, 213, 34]], ![![-140, 65, 11]], ![![-656, 217, 40]]]
  g := ![![![-213, 1142, -133], ![1616, -8664, 1009], ![-12260, 65731, -7655]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-341, 213, 34]] ![![-2945, 1142, -133]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-17, -31, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-17, -31, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![96, 82, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-17, -31, 1], ![-168, 26, -30], ![5040, -1458, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -82, 113]], ![![-1, -1, 1], ![24, 22, -30], ![48, -10, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [21, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 112], [0, 1]]
 g := ![![[], [], [], [25], [0, 102], [0, 1]], ![[], [], [], [25], [0, 11], [0, 112]]]
 h' := ![![[0, 112], [98], [18], [40], [0, 5], [0, 92], [0, 1]], ![[0, 1], [98], [18], [40], [0, 108], [0, 21], [0, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [0, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [21, 0, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![862, -389, 49]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -39, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![30, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![30, 1, 0]] 
 ![![113, 0, 0], ![30, 1, 0], ![4, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![30, 1, 0], ![0, 30, 1], ![-168, 43, 31]]]
  hmulB := by decide  
  f := ![![![1111, 37, 0], ![-4181, 0, 0]], ![![270, 9, 0], ![-1016, 0, 0]], ![![8, 0, 0], ![-30, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 113, 0], ![-4, 0, 113]], ![![0, 1, 0], ![-8, 30, 1], ![-14, 43, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-17, -31, 1]] ![![113, 0, 0], ![30, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![3390, 113, 0]], ![![-1921, -3503, 113], ![-678, -904, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![30, 1, 0]]], ![![![-17, -31, 1]], ![![-6, -8, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [70, 94, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 103, 36], [21, 23, 91], [0, 1]]
 g := ![![[74, 4, 8], [18, 67, 117], [23, 113, 52], [25, 5, 42], [31, 95, 18], [1]], ![[112, 64, 16, 103], [61, 66, 59, 8], [60, 45, 68, 88], [25, 81, 8, 31], [17, 43, 112, 26], [25, 96, 3, 47]], ![[100, 83, 8, 51], [7, 124, 26, 23], [57, 114, 73, 48], [32, 85, 88, 114], [43, 98, 17, 53], [49, 27, 46, 80]]]
 h' := ![![[27, 103, 36], [10, 125, 95], [41, 110, 25], [28, 88, 68], [116, 35, 13], [57, 33, 48], [0, 1]], ![[21, 23, 91], [105, 88, 81], [49, 91, 90], [103, 89, 33], [44, 1, 35], [26, 37, 6], [27, 103, 36]], ![[0, 1], [52, 41, 78], [47, 53, 12], [110, 77, 26], [39, 91, 79], [116, 57, 73], [21, 23, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 117], []]
 b := ![[], [120, 53, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [70, 94, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87122, -92837, 26924]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-686, -731, 212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997925, -386958, 45065]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![997925, -386958, 45065]] 
 ![![131, 0, 0], ![0, 131, 0], ![98, 16, 1]] where
  M :=![![![997925, -386958, 45065], ![-7570920, 2935720, -341893], ![57438024, -22272319, 2593827]]]
  hmulB := by decide  
  f := ![![![-1217, 401, 74]], ![![-12432, 1965, 475]], ![![-3038, 601, 132]]]
  g := ![![![-26095, -8458, 45065], ![197974, 64168, -341893], ![-1501962, -486821, 2593827]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [99, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 130], [0, 1]]
 g := ![![[58, 45], [72, 113], [74], [49], [16], [91], [1]], ![[0, 86], [69, 18], [74], [49], [16], [91], [1]]]
 h' := ![![[22, 130], [77, 62], [87, 84], [48, 104], [24, 7], [6, 4], [32, 22], [0, 1]], ![[0, 1], [0, 69], [101, 47], [109, 27], [47, 124], [94, 127], [123, 109], [22, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [33, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [99, 109, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6369, -3350, 462]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-297, -82, 462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1217, -401, -74]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1217, -401, -74]] 
 ![![131, 0, 0], ![114, 1, 0], ![104, 0, 1]] where
  M :=![![![1217, -401, -74], ![12432, -1965, -475], ![79800, -7993, -2440]]]
  hmulB := by decide  
  f := ![![![-997925, 386958, -45065]], ![![-810630, 314332, -36607]], ![![-1230704, 477221, -55577]]]
  g := ![![![417, -401, -74], ![2182, -1965, -475], ![9502, -7993, -2440]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![997925, -386958, 45065]] ![![1217, -401, -74]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![8, -22, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![8, -22, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![8, 115, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![8, -22, 1], ![-168, 51, -21], ![3528, -1071, 30]]]
  hmulB := by decide  
  f := ![![![-7, 22, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -115, 137]], ![![0, -1, 1], ![0, 18, -21], ![24, -33, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [109, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 136], [0, 1]]
 g := ![![[56, 44], [44], [112], [124, 112], [136], [22], [1]], ![[0, 93], [44], [112], [106, 25], [136], [22], [1]]]
 h' := ![![[61, 136], [3, 110], [2, 110], [47, 48], [50, 48], [30, 100], [28, 61], [0, 1]], ![[0, 1], [0, 27], [136, 27], [98, 89], [101, 89], [102, 37], [50, 76], [61, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [71, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [109, 76, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1434, -313, 145]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -124, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![21, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![21, 1, 0]] 
 ![![137, 0, 0], ![21, 1, 0], ![107, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![21, 1, 0], ![0, 21, 1], ![-168, 43, 22]]]
  hmulB := by decide  
  f := ![![![1891, 90, 0], ![-12330, 0, 0]], ![![273, 13, 0], ![-1780, 0, 0]], ![![1453, 69, 0], ![-9474, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 137, 0], ![-107, 0, 137]], ![![0, 1, 0], ![-4, 21, 1], ![-25, 43, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![8, -22, 1]] ![![137, 0, 0], ![21, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![2877, 137, 0]], ![![1096, -3014, 137], ![0, -411, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![21, 1, 0]]], ![![![8, -22, 1]], ![![0, -3, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB158I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB158I2 : PrimesBelowBoundCertificateInterval O 79 137 158 where
  m := 11
  g := ![2, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB158I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I103N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N1], [], [I103N1], [], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
