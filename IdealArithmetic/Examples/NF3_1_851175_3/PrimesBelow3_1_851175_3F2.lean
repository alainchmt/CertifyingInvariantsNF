
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![32, 34, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![32, 34, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![32, 34, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![32, 34, 1], ![78, 31, 101], ![3745, -1141, -36]]]
  hmulB := by decide  
  f := ![![![-31, -34, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -34, 83]], ![![0, 0, 1], ![-38, -41, 101], ![59, 1, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [41, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 82], [0, 1]]
 g := ![![[25, 81], [24, 28], [33], [77], [67, 11], [1]], ![[0, 2], [42, 55], [33], [77], [80, 72], [1]]]
 h' := ![![[54, 82], [12, 9], [44, 51], [61, 45], [75, 34], [42, 54], [0, 1]], ![[0, 1], [0, 74], [59, 32], [1, 38], [2, 49], [53, 29], [54, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [68, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [41, 29, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![844, -37, -399]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![164, 163, -399]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-18, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-18, 1, 0]] 
 ![![83, 0, 0], ![65, 1, 0], ![36, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-18, 1, 0], ![-1, -17, 3], ![112, -35, -19]]]
  hmulB := by decide  
  f := ![![![-303, -5475, 966], ![83, -26726, 0]], ![![-233, -4285, 756], ![84, -20916, 0]], ![![-126, -2375, 419], ![61, -11592, 0]]]
  g := ![![![1, 0, 0], ![-65, 83, 0], ![-36, 0, 83]], ![![-1, 1, 0], ![12, -17, 3], ![37, -35, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![32, 34, 1]] ![![83, 0, 0], ![-18, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1494, 83, 0]], ![![2656, 2822, 83], ![-498, -581, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-18, 1, 0]]], ![![![32, 34, 1]], ![![-6, -7, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-41, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-41, 1, 0]] 
 ![![89, 0, 0], ![48, 1, 0], ![76, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-41, 1, 0], ![-1, -40, 3], ![112, -35, -42]]]
  hmulB := by decide  
  f := ![![![430, 17160, -1287], ![0, 38181, 0]], ![![232, 9240, -693], ![1, 20559, 0]], ![![387, 14653, -1099], ![43, 32604, 0]]]
  g := ![![![1, 0, 0], ![-48, 89, 0], ![-76, 0, 89]], ![![-1, 1, 0], ![19, -40, 3], ![56, -35, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-30, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-30, 1, 0]] 
 ![![89, 0, 0], ![59, 1, 0], ![36, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-30, 1, 0], ![-1, -29, 3], ![112, -35, -31]]]
  hmulB := by decide  
  f := ![![![-2119, -62351, 6450], ![89, -191350, 0]], ![![-1394, -41326, 4275], ![90, -126825, 0]], ![![-846, -25221, 2609], ![69, -77400, 0]]]
  g := ![![![1, 0, 0], ![-59, 89, 0], ![-36, 0, 89]], ![![-1, 1, 0], ![18, -29, 3], ![37, -35, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-18, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-18, 1, 0]] 
 ![![89, 0, 0], ![71, 1, 0], ![46, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-18, 1, 0], ![-1, -17, 3], ![112, -35, -19]]]
  hmulB := by decide  
  f := ![![![-317, -5713, 1008], ![89, -29904, 0]], ![![-249, -4557, 804], ![90, -23852, 0]], ![![-160, -2953, 521], ![65, -15456, 0]]]
  g := ![![![1, 0, 0], ![-71, 89, 0], ![-46, 0, 89]], ![![-1, 1, 0], ![12, -17, 3], ![39, -35, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-41, 1, 0]] ![![89, 0, 0], ![-30, 1, 0]]
  ![![89, 0, 0], ![24, 36, 1]] where
 M := ![![![7921, 0, 0], ![-2670, 89, 0]], ![![-3649, 89, 0], ![1229, -70, 3]]]
 hmul := by decide  
 g := ![![![![65, -36, -1], ![89, 0, 0]], ![![-30, 1, 0], ![0, 0, 0]]], ![![![-41, 1, 0], ![0, 0, 0]], ![![13, -2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![24, 36, 1]] ![![89, 0, 0], ![-18, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1602, 89, 0]], ![![2136, 3204, 89], ![-356, -623, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-18, 1, 0]]], ![![![24, 36, 1]], ![![-4, -7, 1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![371217, 13002, 9883]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![371217, 13002, 9883]] 
 ![![97, 0, 0], ![16, 1, 0], ![6, 0, 1]] where
  M :=![![![371217, 13002, 9883], ![1093894, 38314, 29123], ![833595, 29197, 22193]]]
  hmulB := by decide  
  f := ![![![-1629, 565, -16]], ![![-293, 88, 15]], ![![562, -177, -18]]]
  g := ![![![1071, 13002, 9883], ![3156, 38314, 29123], ![2405, 29197, 22193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9165, 321, 244]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![9165, 321, 244]] 
 ![![97, 0, 0], ![65, 1, 0], ![57, 0, 1]] where
  M :=![![![9165, 321, 244], ![27007, 946, 719], ![20580, 721, 548]]]
  hmulB := by decide  
  f := ![![![9, 16, -25]], ![![-23, 20, -16]], ![![40, -9, -6]]]
  g := ![![![-264, 321, 244], ![-778, 946, 719], ![-593, 721, 548]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![371217, 13002, 9883]] ![![371217, 13002, 9883]]
  ![![160263290262, 5613276013, 4266728276]] where
 M := ![![![160263290262, 5613276013, 4266728276]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI97N1 : IdealMulLeCertificate' Table 
  ![![160263290262, 5613276013, 4266728276]] ![![9165, 321, 244]]
  ![![97, 0, 0]] where
 M := ![![![1708220068454401, 59830986369396, 45478355372523]]]
 hmul := by decide  
 g := ![![![![17610516169633, 616814292468, 468849024459]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![30, 6, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![30, 6, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![30, 6, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![30, 6, 1], ![106, 1, 17], ![609, -161, -10]]]
  hmulB := by decide  
  f := ![![![-29, -6, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -6, 101]], ![![0, 0, 1], ![-4, -1, 17], ![9, -1, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [28, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 100], [0, 1]]
 g := ![![[82, 65], [20], [53, 30], [5], [36], [27, 1]], ![[19, 36], [20], [55, 71], [5], [36], [54, 100]]]
 h' := ![![[27, 100], [98, 60], [31, 90], [99, 63], [80, 45], [52, 95], [0, 1]], ![[0, 1], [1, 41], [37, 11], [83, 38], [83, 56], [92, 6], [27, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [30, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [28, 74, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4217, 3136, -1632]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![443, 128, -1632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-17, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-17, 1, 0]] 
 ![![101, 0, 0], ![84, 1, 0], ![10, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-17, 1, 0], ![-1, -16, 3], ![112, -35, -18]]]
  hmulB := by decide  
  f := ![![![-7392, -118561, 22230], ![101, -748410, 0]], ![![-6144, -98593, 18486], ![102, -622362, 0]], ![![-727, -11739, 2201], ![39, -74100, 0]]]
  g := ![![![1, 0, 0], ![-84, 101, 0], ![-10, 0, 101]], ![![-1, 1, 0], ![13, -16, 3], ![32, -35, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![30, 6, 1]] ![![101, 0, 0], ![-17, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1717, 101, 0]], ![![3030, 606, 101], ![-404, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-17, 1, 0]]], ![![![30, 6, 1]], ![![-4, -1, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![43, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![43, 1, 0]] 
 ![![103, 0, 0], ![43, 1, 0], ![90, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![43, 1, 0], ![-1, 44, 3], ![112, -35, 42]]]
  hmulB := by decide  
  f := ![![![-594, 24287, 1656], ![103, -56856, 0]], ![![-273, 10119, 690], ![104, -23690, 0]], ![![-504, 21222, 1447], ![54, -49680, 0]]]
  g := ![![![1, 0, 0], ![-43, 103, 0], ![-90, 0, 103]], ![![0, 1, 0], ![-21, 44, 3], ![-21, -35, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, -28, -2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![87, -28, -2]] 
 ![![103, 0, 0], ![69, 1, 0], ![72, 0, 1]] where
  M :=![![![87, -28, -2], ![-196, 129, -82], ![-3010, 882, 183]]]
  hmulB := by decide  
  f := ![![![-95931, -3360, -2554]], ![![-67009, -2347, -1784]], ![![-69150, -2422, -1841]]]
  g := ![![![21, -28, -2], ![-31, 129, -82], ![-748, 882, 183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-9, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-9, 1, 0]] 
 ![![103, 0, 0], ![94, 1, 0], ![10, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-9, 1, 0], ![-1, -8, 3], ![112, -35, -10]]]
  hmulB := by decide  
  f := ![![![-7430, -59521, 22320], ![103, -766320, 0]], ![![-6779, -54313, 20367], ![104, -699267, 0]], ![![-719, -5779, 2167], ![37, -74400, 0]]]
  g := ![![![1, 0, 0], ![-94, 103, 0], ![-10, 0, 103]], ![![-1, 1, 0], ![7, -8, 3], ![34, -35, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![43, 1, 0]] ![![87, -28, -2]]
  ![![103, 0, 0], ![-7, -31, 1]] where
 M := ![![![8961, -2884, -206]], ![![3545, -1075, -168]]]
 hmul := by decide  
 g := ![![![![94, 3, -3], ![103, 0, 0]]], ![![![37, 1, -2], ![38, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-7, -31, 1]] ![![103, 0, 0], ![-9, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-927, 103, 0]], ![![-721, -3193, 103], ![206, 206, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-9, 1, 0]]], ![![![-7, -31, 1]], ![![2, 2, -1]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [99, 81, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 96, 95], [106, 10, 12], [0, 1]]
 g := ![![[30, 12, 12], [35, 14, 86], [65, 90], [90, 64, 23], [19, 90], [1]], ![[7, 32, 64, 15], [80, 42, 24, 91], [18, 16], [41, 39, 105, 63], [62, 99], [87, 68, 91, 91]], ![[96, 80, 32, 76], [26, 15, 23, 33], [24, 92], [34, 34, 80, 30], [26, 85], [22, 32, 12, 16]]]
 h' := ![![[26, 96, 95], [66, 103, 36], [77, 44, 73], [78, 74, 25], [2, 25, 39], [8, 26, 25], [0, 1]], ![[106, 10, 12], [41, 56, 87], [11, 4, 95], [9, 86, 4], [51, 59, 90], [82, 79, 45], [26, 96, 95]], ![[0, 1], [74, 55, 91], [53, 59, 46], [90, 54, 78], [17, 23, 85], [68, 2, 37], [106, 10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 23], []]
 b := ![[], [96, 33, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [99, 81, 82, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1062312906, -67869244, -397049822]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9928158, -634292, -3710746]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![64, 54, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![64, 54, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![64, 54, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![64, 54, 1], ![58, 83, 161], ![5985, -1841, -24]]]
  hmulB := by decide  
  f := ![![![-63, -54, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -54, 109]], ![![0, 0, 1], ![-94, -79, 161], ![69, -5, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [105, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 108], [0, 1]]
 g := ![![[50, 27], [73], [22, 97], [100, 84], [1], [91, 1]], ![[0, 82], [73], [20, 12], [5, 25], [1], [73, 108]]]
 h' := ![![[91, 108], [79, 71], [88, 89], [73, 36], [65, 56], [37, 1], [0, 1]], ![[0, 1], [0, 38], [12, 20], [79, 73], [38, 53], [19, 108], [91, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [7, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [105, 18, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2073, 2553, -2381]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1379, 1203, -2381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-52, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-52, 1, 0]] 
 ![![109, 0, 0], ![57, 1, 0], ![24, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-52, 1, 0], ![-1, -51, 3], ![112, -35, -53]]]
  hmulB := by decide  
  f := ![![![3433, 175032, -10296], ![0, 374088, 0]], ![![1795, 91494, -5382], ![1, 195546, 0]], ![![764, 38539, -2267], ![17, 82368, 0]]]
  g := ![![![1, 0, 0], ![-57, 109, 0], ![-24, 0, 109]], ![![-1, 1, 0], ![26, -51, 3], ![31, -35, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![64, 54, 1]] ![![109, 0, 0], ![-52, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-5668, 109, 0]], ![![6976, 5886, 109], ![-3270, -2725, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-52, 1, 0]]], ![![![64, 54, 1]], ![![-30, -25, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![56, 3, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![56, 3, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![56, 3, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![56, 3, 1], ![109, 24, 8], ![273, -56, 19]]]
  hmulB := by decide  
  f := ![![![-55, -3, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -3, 113]], ![![0, 0, 1], ![-3, 0, 8], ![-7, -1, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [32, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 112], [0, 1]]
 g := ![![[83, 53], [32], [25], [50], [9, 97], [56, 1]], ![[0, 60], [32], [25], [50], [17, 16], [112, 112]]]
 h' := ![![[56, 112], [95, 77], [21, 91], [97, 108], [51, 29], [16, 53], [0, 1]], ![[0, 1], [0, 36], [32, 22], [43, 5], [93, 84], [46, 60], [56, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [46, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [32, 57, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![863, -93, -483]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![247, 12, -483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-8, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-8, 1, 0]] 
 ![![113, 0, 0], ![105, 1, 0], ![94, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-8, 1, 0], ![-1, -7, 3], ![112, -35, -9]]]
  hmulB := by decide  
  f := ![![![-1349, -9507, 4074], ![113, -153454, 0]], ![![-1252, -8828, 3783], ![114, -142493, 0]], ![![-1126, -7908, 3389], ![40, -127652, 0]]]
  g := ![![![1, 0, 0], ![-105, 113, 0], ![-94, 0, 113]], ![![-1, 1, 0], ![4, -7, 3], ![41, -35, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![56, 3, 1]] ![![113, 0, 0], ![-8, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-904, 113, 0]], ![![6328, 339, 113], ![-339, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-8, 1, 0]]], ![![![56, 3, 1]], ![![-3, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3341, -117, -89]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-3341, -117, -89]] 
 ![![127, 0, 0], ![0, 127, 0], ![9, 27, 1]] where
  M :=![![![-3341, -117, -89], ![-9851, -343, -262], ![-7497, -266, -198]]]
  hmulB := by decide  
  f := ![![![14, -4, -1]], ![![-108, 45, -11]], ![![-25, 10, -2]]]
  g := ![![![-20, 18, -89], ![-59, 53, -262], ![-45, 40, -198]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [104, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 126], [0, 1]]
 g := ![![[73, 11], [96, 70], [118, 1], [13, 73], [106, 120], [28, 1]], ![[0, 116], [24, 57], [19, 126], [25, 54], [37, 7], [56, 126]]]
 h' := ![![[28, 126], [49, 30], [47, 18], [45, 1], [25, 94], [9, 45], [0, 1]], ![[0, 1], [0, 97], [43, 109], [73, 126], [117, 33], [126, 82], [28, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [76, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [104, 99, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17373, -2618, 999]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, -233, 999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 4, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-14, 4, 1]] 
 ![![127, 0, 0], ![47, 1, 0], ![52, 0, 1]] where
  M :=![![![-14, 4, 1], ![108, -45, 11], ![385, -91, -52]]]
  hmulB := by decide  
  f := ![![![3341, 117, 89]], ![![1314, 46, 35]], ![![1427, 50, 38]]]
  g := ![![![-2, 4, 1], ![13, -45, 11], ![58, -91, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-3341, -117, -89]] ![![-14, 4, 1]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [50, 56, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 6, 84], [67, 124, 47], [0, 1]]
 g := ![![[1, 61, 49], [3, 57, 100], [76, 65], [24, 121], [101, 55], [17, 1], []], ![[93, 41, 2, 65], [93, 93, 64, 107], [42, 109], [106, 74], [116, 36], [76, 49], [47, 113]], ![[9, 52, 100, 116], [1, 69, 10, 2], [13, 74], [1, 125], [45, 5], [38, 36], [84, 113]]]
 h' := ![![[81, 6, 84], [112, 130, 124], [2, 3, 10], [38, 4, 117], [94, 116, 11], [67, 46, 102], [0, 0, 1], [0, 1]], ![[67, 124, 47], [29, 74, 96], [42, 16, 51], [96, 53, 41], [5, 65, 104], [98, 46, 6], [19, 26, 124], [81, 6, 84]], ![[0, 1], [118, 58, 42], [80, 112, 70], [59, 74, 104], [41, 81, 16], [8, 39, 23], [27, 105, 6], [67, 124, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 38], []]
 b := ![[], [15, 34, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [50, 56, 114, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-894861, 396275, -120389]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6831, 3025, -919]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1255, 512, -113]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-1255, 512, -113]] 
 ![![137, 0, 0], ![0, 137, 0], ![79, 67, 1]] where
  M :=![![![-1255, 512, -113], ![-13168, 3212, 1649], ![64463, -23457, 2075]]]
  hmulB := by decide  
  f := ![![![330989, 11593, 8812]], ![![975351, 34162, 25967]], ![![673284, 23582, 17925]]]
  g := ![![![56, 59, -113], ![-1047, -783, 1649], ![-726, -1186, 2075]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [94, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 136], [0, 1]]
 g := ![![[24, 34], [69], [112], [124, 61], [34], [123], [1]], ![[40, 103], [69], [112], [56, 76], [34], [123], [1]]]
 h' := ![![[73, 136], [115, 87], [5, 53], [126, 89], [14, 46], [14, 50], [43, 73], [0, 1]], ![[0, 1], [27, 50], [38, 84], [47, 48], [84, 91], [102, 87], [29, 64], [73, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [10, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [94, 64, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1725, 693, -873]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![516, 432, -873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![330989, 11593, 8812]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![330989, 11593, 8812]] 
 ![![137, 0, 0], ![74, 1, 0], ![22, 0, 1]] where
  M :=![![![330989, 11593, 8812], ![975351, 34162, 25967], ![743260, 26033, 19788]]]
  hmulB := by decide  
  f := ![![![-1255, 512, -113]], ![![-774, 300, -49]], ![![269, -89, -3]]]
  g := ![![![-5261, 11593, 8812], ![-15503, 34162, 25967], ![-11814, 26033, 19788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-1255, 512, -113]] ![![330989, 11593, 8812]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB262I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB262I2 : PrimesBelowBoundCertificateInterval O 79 137 262 where
  m := 11
  g := ![2, 3, 3, 2, 3, 1, 2, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB262I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I101N1, I103N0, I103N1, I103N2, I109N1, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N0, I97N1], [I101N1], [I103N0, I103N1, I103N2], [], [I109N1], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
