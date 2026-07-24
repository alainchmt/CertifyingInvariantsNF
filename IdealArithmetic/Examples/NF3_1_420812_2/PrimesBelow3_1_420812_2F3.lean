
import IdealArithmetic.Examples.NF3_1_420812_2.RI3_1_420812_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-64, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-64, 1, 0]] 
 ![![139, 0, 0], ![75, 1, 0], ![107, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-64, 1, 0], ![1, -64, 2], ![0, -38, -63]]]
  hmulB := by decide  
  f := ![![![6841, -671175, 20976], ![-7923, -1457832, 0]], ![![3739, -362082, 11316], ![-4169, -786462, 0]], ![![5273, -516660, 16147], ![-6084, -1122216, 0]]]
  g := ![![![1, 0, 0], ![-75, 139, 0], ![-107, 0, 139]], ![![-1, 1, 0], ![33, -64, 2], ![69, -38, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-54, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-54, 1, 0]] 
 ![![139, 0, 0], ![85, 1, 0], ![2, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-54, 1, 0], ![1, -54, 2], ![0, -38, -53]]]
  hmulB := by decide  
  f := ![![![-737, 54427, -2016], ![695, 140112, 0]], ![![-453, 33261, -1232], ![418, 85624, 0]], ![![-4, 783, -29], ![27, 2016, 0]]]
  g := ![![![1, 0, 0], ![-85, 139, 0], ![-2, 0, 139]], ![![-1, 1, 0], ![33, -54, 2], ![24, -38, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-22, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-22, 1, 0]] 
 ![![139, 0, 0], ![117, 1, 0], ![106, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-22, 1, 0], ![1, -22, 2], ![0, -38, -21]]]
  hmulB := by decide  
  f := ![![![5257, -121428, 11040], ![-1668, -767280, 0]], ![![4427, -102202, 9292], ![-1389, -645794, 0]], ![![4014, -92600, 8419], ![-1240, -585120, 0]]]
  g := ![![![1, 0, 0], ![-117, 139, 0], ![-106, 0, 139]], ![![-1, 1, 0], ![17, -22, 2], ![48, -38, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-64, 1, 0]] ![![139, 0, 0], ![-54, 1, 0]]
  ![![139, 0, 0], ![-9, -59, 1]] where
 M := ![![![19321, 0, 0], ![-7506, 139, 0]], ![![-8896, 139, 0], ![3457, -118, 2]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![-45, 60, -1], ![139, 0, 0]]], ![![![-55, 60, -1], ![139, 0, 0]], ![![25, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-9, -59, 1]] ![![139, 0, 0], ![-22, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3058, 139, 0]], ![![-1251, -8201, 139], ![139, 1251, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-22, 1, 0]]], ![![![-9, -59, 1]], ![![1, 9, -1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-71, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-71, 1, 0]] 
 ![![149, 0, 0], ![78, 1, 0], ![13, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-71, 1, 0], ![1, -71, 2], ![0, -38, -70]]]
  hmulB := by decide  
  f := ![![![11802, -1326751, 37376], ![-14453, -2784512, 0]], ![![6233, -694472, 19564], ![-7449, -1457518, 0]], ![![1044, -115757, 3261], ![-1231, -242944, 0]]]
  g := ![![![1, 0, 0], ![-78, 149, 0], ![-13, 0, 149]], ![![-1, 1, 0], ![37, -71, 2], ![26, -38, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-55, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-55, 1, 0]] 
 ![![149, 0, 0], ![94, 1, 0], ![127, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-55, 1, 0], ![1, -55, 2], ![0, -38, -54]]]
  hmulB := by decide  
  f := ![![![-5529, 403942, -14690], ![4917, 1094405, 0]], ![![-3477, 254794, -9266], ![3130, 690317, 0]], ![![-4737, 344300, -12521], ![4125, 932815, 0]]]
  g := ![![![1, 0, 0], ![-94, 149, 0], ![-127, 0, 149]], ![![-1, 1, 0], ![33, -55, 2], ![70, -38, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-24, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-24, 1, 0]] 
 ![![149, 0, 0], ![125, 1, 0], ![85, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-24, 1, 0], ![1, -24, 2], ![0, -38, -23]]]
  hmulB := by decide  
  f := ![![![-2459, 62490, -5208], ![894, 387996, 0]], ![![-2063, 52411, -4368], ![746, 325416, 0]], ![![-1387, 35648, -2971], ![608, 221340, 0]]]
  g := ![![![1, 0, 0], ![-125, 149, 0], ![-85, 0, 149]], ![![-1, 1, 0], ![19, -24, 2], ![45, -38, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-71, 1, 0]] ![![149, 0, 0], ![-55, 1, 0]]
  ![![149, 0, 0], ![16, -63, 1]] where
 M := ![![![22201, 0, 0], ![-8195, 149, 0]], ![![-10579, 149, 0], ![3906, -126, 2]]]
 hmul := by decide  
 g := ![![![![133, 63, -1], ![149, 0, 0]], ![![-55, 1, 0], ![0, 0, 0]]], ![![![-71, 1, 0], ![0, 0, 0]], ![![10, 63, -1], ![151, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![16, -63, 1]] ![![149, 0, 0], ![-24, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3576, 149, 0]], ![![2384, -9387, 149], ![-447, 1490, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-24, 1, 0]]], ![![![16, -63, 1]], ![![-3, 10, -1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [75, 42, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 41, 99], [49, 109, 52], [0, 1]]
 g := ![![[47, 96, 18], [4, 84, 1], [122, 43, 127], [61, 85], [115, 11, 32], [148, 1], []], ![[110, 47, 49, 40], [150, 82, 127, 32], [91, 81, 105, 31], [52, 118], [66, 50, 38, 81], [9, 103], [6, 137]], ![[66, 122, 60, 23], [97, 21, 114, 41], [56, 26, 20, 14], [133, 36], [63, 9, 90, 111], [121, 20], [53, 137]]]
 h' := ![![[99, 41, 99], [2, 122, 138], [61, 32, 150], [128, 74, 60], [133, 123, 113], [74, 51, 118], [0, 0, 1], [0, 1]], ![[49, 109, 52], [143, 79, 91], [69, 97, 39], [150, 132, 125], [44, 96, 32], [50, 48, 93], [140, 7, 109], [99, 41, 99]], ![[0, 1], [17, 101, 73], [32, 22, 113], [65, 96, 117], [136, 83, 6], [4, 52, 91], [87, 144, 41], [49, 109, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 114], []]
 b := ![[], [87, 71, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [75, 42, 3, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5285, -28388, -9966]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -188, -66]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [40, 129, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 156, 75], [87, 0, 82], [0, 1]]
 g := ![![[94, 146, 17], [29, 115], [96, 52, 81], [135, 146, 44], [79, 125, 140], [95, 1], []], ![[69, 85, 70, 36], [90, 108], [117, 29, 75, 75], [17, 11, 60, 81], [74, 17, 137, 108], [], [111, 130]], ![[155, 56, 44, 3], [17, 51], [119, 140, 72, 67], [142, 34, 136, 113], [60, 31, 83, 105], [118, 1], [104, 130]]]
 h' := ![![[8, 156, 75], [99, 80, 86], [85, 56, 127], [95, 67, 148], [137, 120, 63], [125, 108, 104], [0, 0, 1], [0, 1]], ![[87, 0, 82], [104, 124, 34], [90, 70, 118], [137, 65, 1], [2, 55, 51], [86, 146, 93], [20, 90], [8, 156, 75]], ![[0, 1], [49, 110, 37], [27, 31, 69], [49, 25, 8], [49, 139, 43], [131, 60, 117], [112, 67, 156], [87, 0, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 46], []]
 b := ![[], [19, 156, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [40, 129, 62, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59346, -16328, 119163]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![378, -104, 759]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![12, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![12, 1, 0]] 
 ![![163, 0, 0], ![12, 1, 0], ![10, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![12, 1, 0], ![1, 12, 2], ![0, -38, 13]]]
  hmulB := by decide  
  f := ![![![-8811, -106888, -17816], ![-1304, 1452004, 0]], ![![-655, -7860, -1310], ![1, 106765, 0]], ![![-546, -6558, -1093], ![-6, 89080, 0]]]
  g := ![![![1, 0, 0], ![-12, 163, 0], ![-10, 0, 163]], ![![0, 1, 0], ![-1, 12, 2], ![2, -38, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![41, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![41, 1, 0]] 
 ![![163, 0, 0], ![41, 1, 0], ![138, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![41, 1, 0], ![1, 41, 2], ![0, -38, 42]]]
  hmulB := by decide  
  f := ![![![483, 23122, 1128], ![326, -91932, 0]], ![![100, 5780, 282], ![164, -22983, 0]], ![![381, 19575, 955], ![387, -77832, 0]]]
  g := ![![![1, 0, 0], ![-41, 163, 0], ![-138, 0, 163]], ![![0, 1, 0], ![-12, 41, 2], ![-26, -38, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-54, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-54, 1, 0]] 
 ![![163, 0, 0], ![109, 1, 0], ![91, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-54, 1, 0], ![1, -54, 2], ![0, -38, -53]]]
  hmulB := by decide  
  f := ![![![-320, 23164, -858], ![326, 69927, 0]], ![![-177, 15442, -572], ![327, 46618, 0]], ![![-176, 12932, -479], ![190, 39039, 0]]]
  g := ![![![1, 0, 0], ![-109, 163, 0], ![-91, 0, 163]], ![![-1, 1, 0], ![35, -54, 2], ![55, -38, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![12, 1, 0]] ![![163, 0, 0], ![41, 1, 0]]
  ![![163, 0, 0], ![2, -55, 1]] where
 M := ![![![26569, 0, 0], ![6683, 163, 0]], ![![1956, 163, 0], ![493, 53, 2]]]
 hmul := by decide  
 g := ![![![![161, 55, -1], ![163, 0, 0]], ![![39, 56, -1], ![163, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![2, -55, 1]] ![![163, 0, 0], ![-54, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-8802, 163, 0]], ![![326, -8965, 163], ![-163, 2934, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-54, 1, 0]]], ![![![2, -55, 1]], ![![-1, 18, -1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![13, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![13, 1, 0]] 
 ![![167, 0, 0], ![13, 1, 0], ![83, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![13, 1, 0], ![1, 13, 2], ![0, -38, 14]]]
  hmulB := by decide  
  f := ![![![-13703, -180168, -27720], ![-2004, 2314620, 0]], ![![-1065, -14013, -2156], ![-166, 180026, 0]], ![![-6816, -89545, -13777], ![-925, 1150380, 0]]]
  g := ![![![1, 0, 0], ![-13, 167, 0], ![-83, 0, 167]], ![![0, 1, 0], ![-2, 13, 2], ![-4, -38, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![24, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![24, 1, 0]] 
 ![![167, 0, 0], ![24, 1, 0], ![130, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![24, 1, 0], ![1, 24, 2], ![0, -38, 25]]]
  hmulB := by decide  
  f := ![![![390, 9911, 826], ![167, -68971, 0]], ![![35, 1415, 118], ![168, -9853, 0]], ![![300, 7715, 643], ![155, -53690, 0]]]
  g := ![![![1, 0, 0], ![-24, 167, 0], ![-130, 0, 167]], ![![0, 1, 0], ![-5, 24, 2], ![-14, -38, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-38, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-38, 1, 0]] 
 ![![167, 0, 0], ![129, 1, 0], ![30, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-38, 1, 0], ![1, -38, 2], ![0, -38, -37]]]
  hmulB := by decide  
  f := ![![![9560, -402203, 21170], ![-4509, -1767695, 0]], ![![7379, -310667, 16352], ![-3506, -1365392, 0]], ![![1716, -72252, 3803], ![-816, -317550, 0]]]
  g := ![![![1, 0, 0], ![-129, 167, 0], ![-30, 0, 167]], ![![-1, 1, 0], ![29, -38, 2], ![36, -38, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![13, 1, 0]] ![![167, 0, 0], ![24, 1, 0]]
  ![![167, 0, 0], ![73, -65, 1]] where
 M := ![![![27889, 0, 0], ![4008, 167, 0]], ![![2171, 167, 0], ![313, 37, 2]]]
 hmul := by decide  
 g := ![![![![94, 65, -1], ![167, 0, 0]], ![![-49, 66, -1], ![167, 0, 0]]], ![![![-60, 66, -1], ![167, 0, 0]], ![![1, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![73, -65, 1]] ![![167, 0, 0], ![-38, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-6346, 167, 0]], ![![12191, -10855, 167], ![-2839, 2505, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-38, 1, 0]]], ![![![73, -65, 1]], ![![-17, 15, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-53, -49, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-53, -49, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![120, 124, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-53, -49, 1], ![-49, -91, -97], ![-19, 1843, -140]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -124, 173]], ![![-1, -1, 1], ![67, 69, -97], ![97, 111, -140]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [10, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 172], [0, 1]]
 g := ![![[45, 52], [121], [157, 43], [163, 163], [85], [159, 90], [1]], ![[0, 121], [121], [10, 130], [165, 10], [85], [141, 83], [1]]]
 h' := ![![[69, 172], [170, 158], [160, 162], [100, 133], [66, 110], [140, 137], [163, 69], [0, 1]], ![[0, 1], [0, 15], [93, 11], [108, 40], [44, 63], [78, 36], [80, 104], [69, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [164, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [10, 104, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85288, -77774, -163942]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![113224, 117058, -163942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-76, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-76, 1, 0]] 
 ![![173, 0, 0], ![97, 1, 0], ![140, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-76, 1, 0], ![1, -76, 2], ![0, -38, -75]]]
  hmulB := by decide  
  f := ![![![-4715, 531666, -13992], ![5190, 1210308, 0]], ![![-2629, 298055, -7844], ![2942, 678506, 0]], ![![-3820, 430250, -11323], ![4190, 979440, 0]]]
  g := ![![![1, 0, 0], ![-97, 173, 0], ![-140, 0, 173]], ![![-1, 1, 0], ![41, -76, 2], ![82, -38, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-53, -49, 1]] ![![173, 0, 0], ![-76, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-13148, 173, 0]], ![![-9169, -8477, 173], ![3979, 3633, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-76, 1, 0]]], ![![![-53, -49, 1]], ![![23, 21, -1]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [49, 160, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 95, 127], [13, 83, 52], [0, 1]]
 g := ![![[157, 122, 171], [126, 147, 93], [134, 59], [29, 153], [172, 72, 89], [129, 17, 1], []], ![[113, 26, 48, 8], [21, 26, 20, 164], [66, 65], [119, 4], [78, 117, 18, 159], [30, 111, 168, 130], [109, 19]], ![[93, 99, 73, 82], [88, 93, 102, 17], [94, 153], [111, 168], [101, 76, 132, 145], [94, 140, 118, 141], [5, 19]]]
 h' := ![![[4, 95, 127], [91, 99, 23], [84, 16, 123], [57, 33, 136], [164, 12, 42], [123, 7, 140], [0, 0, 1], [0, 1]], ![[13, 83, 52], [90, 121, 162], [134, 14, 69], [44, 16, 85], [133, 32, 177], [7, 134, 158], [45, 110, 83], [4, 95, 127]], ![[0, 1], [167, 138, 173], [73, 149, 166], [174, 130, 137], [171, 135, 139], [135, 38, 60], [103, 69, 95], [13, 83, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 36], []]
 b := ![[], [62, 174, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [49, 160, 162, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164680, -88426, -327391]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-920, -494, -1829]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![40, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![40, 1, 0]] 
 ![![181, 0, 0], ![40, 1, 0], ![15, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![40, 1, 0], ![1, 40, 2], ![0, -38, 41]]]
  hmulB := by decide  
  f := ![![![-9531, -419656, -20984], ![-4344, 1899052, 0]], ![![-2118, -92715, -4636], ![-904, 419558, 0]], ![![-825, -34779, -1739], ![-201, 157380, 0]]]
  g := ![![![1, 0, 0], ![-40, 181, 0], ![-15, 0, 181]], ![![0, 1, 0], ![-9, 40, 2], ![5, -38, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![53, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![53, 1, 0]] 
 ![![181, 0, 0], ![53, 1, 0], ![44, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![53, 1, 0], ![1, 53, 2], ![0, -38, 54]]]
  hmulB := by decide  
  f := ![![![5694, 360697, 13612], ![3801, -1231886, 0]], ![![1674, 105570, 3984], ![1087, -360552, 0]], ![![1371, 87683, 3309], ![969, -299464, 0]]]
  g := ![![![1, 0, 0], ![-53, 181, 0], ![-44, 0, 181]], ![![0, 1, 0], ![-16, 53, 2], ![-2, -38, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![87, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![87, 1, 0]] 
 ![![181, 0, 0], ![87, 1, 0], ![17, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![87, 1, 0], ![1, 87, 2], ![0, -38, 88]]]
  hmulB := by decide  
  f := ![![![-10121, -1402806, -32250], ![-12489, 2918625, 0]], ![![-4879, -674217, -15500], ![-5972, 1402750, 0]], ![![-1015, -131756, -3029], ![-1039, 274125, 0]]]
  g := ![![![1, 0, 0], ![-87, 181, 0], ![-17, 0, 181]], ![![0, 1, 0], ![-42, 87, 2], ![10, -38, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![40, 1, 0]] ![![181, 0, 0], ![53, 1, 0]]
  ![![181, 0, 0], ![65, -44, 1]] where
 M := ![![![32761, 0, 0], ![9593, 181, 0]], ![![7240, 181, 0], ![2121, 93, 2]]]
 hmul := by decide  
 g := ![![![![116, 44, -1], ![181, 0, 0]], ![![-12, 45, -1], ![181, 0, 0]]], ![![![-25, 45, -1], ![181, 0, 0]], ![![-54, 45, -1], ![183, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![65, -44, 1]] ![![181, 0, 0], ![87, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![15747, 181, 0]], ![![11765, -7964, 181], ![5611, -3801, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![87, 1, 0]]], ![![![65, -44, 1]], ![![31, -21, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)


lemma PB184I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 183 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 183 (by omega)

def PB184I3 : PrimesBelowBoundCertificateInterval O 137 183 184 where
  m := 9
  g := ![3, 3, 1, 1, 3, 3, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB184I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![181, 181, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
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
      exact NI163N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I139N0, I139N1, I139N2, I149N0, I149N1, I149N2, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N1, I181N0, I181N1, I181N2]
  Il := ![[I139N0, I139N1, I139N2], [I149N0, I149N1, I149N2], [], [], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N1], [], [I181N0, I181N1, I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
