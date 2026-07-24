
import IdealArithmetic.Examples.NF3_1_410267_1.RI3_1_410267_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![5, -38, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![5, -38, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![5, 45, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![5, -38, 1], ![41, -46, -191], ![-4498, 520, 30]]]
  hmulB := by decide  
  f := ![![![-4, 38, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -45, 83]], ![![0, -1, 1], ![12, 103, -191], ![-56, -10, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [48, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 82], [0, 1]]
 g := ![![[61, 64], [73, 37], [51], [41], [1, 31], [1]], ![[0, 19], [52, 46], [51], [41], [35, 52], [1]]]
 h' := ![![[60, 82], [65, 75], [58, 28], [4, 36], [35, 46], [35, 60], [0, 1]], ![[0, 1], [0, 8], [78, 55], [6, 47], [56, 37], [66, 23], [60, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [12, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [48, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1054, 356, -420]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 232, -420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![25, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![25, 1, 0]] 
 ![![83, 0, 0], ![25, 1, 0], ![53, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![25, 1, 0], ![2, 26, 5], ![117, -13, 24]]]
  hmulB := by decide  
  f := ![![![231, 3638, 700], ![166, -11620, 0]], ![![59, 1091, 210], ![84, -3486, 0]], ![![146, 2323, 447], ![111, -7420, 0]]]
  g := ![![![1, 0, 0], ![-25, 83, 0], ![-53, 0, 83]], ![![0, 1, 0], ![-11, 26, 5], ![-10, -13, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![5, -38, 1]] ![![83, 0, 0], ![25, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2075, 83, 0]], ![![415, -3154, 83], ![166, -996, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![25, 1, 0]]], ![![![5, -38, 1]], ![![2, -12, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-30, 41, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-30, 41, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![59, 41, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-30, 41, 1], ![199, -2, 204], ![4745, -507, -84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -41, 89]], ![![-1, 0, 1], ![-133, -94, 204], ![109, 33, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [88, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 88], [0, 1]]
 g := ![![[52, 88], [9], [55], [55, 80], [3, 34], [1]], ![[0, 1], [9], [55], [32, 9], [80, 55], [1]]]
 h' := ![![[52, 88], [77, 55], [54, 86], [55, 12], [3, 13], [1, 52], [0, 1]], ![[0, 1], [0, 34], [76, 3], [56, 77], [56, 76], [35, 37], [52, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [81, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [88, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8490, 4394, -1586]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![956, 780, -1586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-26, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-26, 1, 0]] 
 ![![89, 0, 0], ![63, 1, 0], ![84, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-26, 1, 0], ![2, -25, 5], ![117, -13, -27]]]
  hmulB := by decide  
  f := ![![![3563, -50357, 10075], ![-1602, -179335, 0]], ![![2541, -35638, 7130], ![-1067, -126914, 0]], ![![3364, -47528, 9509], ![-1508, -169260, 0]]]
  g := ![![![1, 0, 0], ![-63, 89, 0], ![-84, 0, 89]], ![![-1, 1, 0], ![13, -25, 5], ![36, -13, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-30, 41, 1]] ![![89, 0, 0], ![-26, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2314, 89, 0]], ![![-2670, 3649, 89], ![979, -1068, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-26, 1, 0]]], ![![![-30, 41, 1]], ![![11, -12, 2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [91, 44, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 49, 67], [53, 47, 30], [0, 1]]
 g := ![![[1, 46, 86], [8, 18], [69, 64], [4, 79], [76, 86], [1]], ![[9, 47, 17, 41], [15, 22], [67, 81], [57, 96], [12, 70], [51, 67, 23, 63]], ![[61, 32, 26, 90], [14, 81], [81, 1], [18, 65], [26, 70], [80, 16, 90, 34]]]
 h' := ![![[6, 49, 67], [60, 87, 38], [20, 1, 55], [73, 68, 89], [7, 39, 46], [6, 53, 59], [0, 1]], ![[53, 47, 30], [93, 15, 49], [10, 32, 33], [53, 40, 9], [83, 82, 22], [37, 55, 19], [6, 49, 67]], ![[0, 1], [40, 92, 10], [76, 64, 9], [47, 86, 96], [6, 73, 29], [74, 86, 19], [53, 47, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 41], []]
 b := ![[], [15, 17, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [91, 44, 38, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3851082651, 890402964, -560000303]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39701883, 9179412, -5773199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [22, 67, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 25, 18], [59, 75, 83], [0, 1]]
 g := ![![[89, 98, 21], [97, 43], [25, 58, 30], [4, 23], [68, 97], [1]], ![[69, 35, 57, 28], [26, 76], [62, 58, 62, 63], [99, 9], [47, 81], [75, 100, 45, 75]], ![[28, 73, 81, 55], [21, 6], [33, 31, 63, 75], [13, 21], [63, 20], [13, 75, 94, 26]]]
 h' := ![![[62, 25, 18], [93, 37, 83], [56, 65, 12], [17, 54, 38], [99, 96, 86], [79, 34, 20], [0, 1]], ![[59, 75, 83], [1, 61, 23], [88, 80, 50], [64, 43, 85], [90, 64, 98], [35, 93, 92], [62, 25, 18]], ![[0, 1], [76, 3, 96], [72, 57, 39], [48, 4, 79], [58, 42, 18], [63, 75, 90], [59, 75, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 91], []]
 b := ![[], [57, 23, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [22, 67, 81, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7796190, 1676600, -407636]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77190, 16600, -4036]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![24, 30, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![24, 30, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![24, 30, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![24, 30, 1], ![177, 41, 149], ![3458, -364, -19]]]
  hmulB := by decide  
  f := ![![![-23, -30, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -30, 103]], ![![0, 0, 1], ![-33, -43, 149], ![38, 2, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [65, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 102], [0, 1]]
 g := ![![[71, 34], [72, 66], [88, 29], [25], [58], [20, 1]], ![[30, 69], [53, 37], [50, 74], [25], [58], [40, 102]]]
 h' := ![![[20, 102], [58, 72], [48, 90], [3, 21], [17, 98], [39, 26], [0, 1]], ![[0, 1], [56, 31], [97, 13], [11, 82], [20, 5], [44, 77], [20, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [59, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [65, 83, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![951, 236, -720]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177, 212, -720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![19, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![2, -45, 5], ![117, -13, -47]]]
  hmulB := by decide  
  f := ![![![1421, -42290, 4700], ![-1030, -96820, 0]], ![![811, -23395, 2600], ![-514, -53560, 0]], ![![305, -7802, 867], ![-94, -17860, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-19, 0, 103]], ![![-1, 1, 0], ![24, -45, 5], ![17, -13, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![24, 30, 1]] ![![103, 0, 0], ![-46, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4738, 103, 0]], ![![2472, 3090, 103], ![-927, -1339, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-46, 1, 0]]], ![![![24, 30, 1]], ![![-9, -13, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-12, 38, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-12, 38, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![95, 38, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-12, 38, 1], ![193, 13, 189], ![4394, -468, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -38, 107]], ![![-1, 0, 1], ![-166, -67, 189], ![97, 18, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [81, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 106], [0, 1]]
 g := ![![[88, 37], [14, 105], [87], [36, 25], [25], [41, 1]], ![[0, 70], [39, 2], [87], [98, 82], [25], [82, 106]]]
 h' := ![![[41, 106], [43, 12], [102, 76], [80, 27], [24, 102], [103, 102], [0, 1]], ![[0, 1], [0, 95], [8, 31], [10, 80], [33, 5], [5, 5], [41, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [46, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [81, 66, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33020, -595, 1778]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1270, -637, 1778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![25, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![25, 1, 0]] 
 ![![107, 0, 0], ![25, 1, 0], ![63, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![25, 1, 0], ![2, 26, 5], ![117, -13, 24]]]
  hmulB := by decide  
  f := ![![![-4699, -66284, -12750], ![-1712, 272850, 0]], ![![-1115, -15467, -2975], ![-320, 63665, 0]], ![![-2766, -39027, -7507], ![-1011, 160650, 0]]]
  g := ![![![1, 0, 0], ![-25, 107, 0], ![-63, 0, 107]], ![![0, 1, 0], ![-9, 26, 5], ![-10, -13, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-12, 38, 1]] ![![107, 0, 0], ![25, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2675, 107, 0]], ![![-1284, 4066, 107], ![-107, 963, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![25, 1, 0]]], ![![![-12, 38, 1]], ![![-1, 9, 2]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [54, 5, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 49, 58], [78, 59, 51], [0, 1]]
 g := ![![[81, 94, 38], [42, 34], [4, 75, 38], [56, 78, 15], [13, 63], [1]], ![[68, 44, 33, 23], [17, 80], [21, 103, 61, 54], [90, 24, 3, 2], [83, 4], [58, 104, 103, 2]], ![[41, 13, 26, 92], [81, 36], [22, 33, 6, 103], [65, 55, 8, 86], [59, 29], [90, 1, 51, 107]]]
 h' := ![![[95, 49, 58], [25, 70, 16], [2, 93, 19], [28, 43, 93], [34, 16, 61], [55, 104, 64], [0, 1]], ![[78, 59, 51], [79, 89, 99], [105, 65, 84], [27, 107, 24], [87, 16, 58], [10, 16, 107], [95, 49, 58]], ![[0, 1], [67, 59, 103], [100, 60, 6], [80, 68, 101], [96, 77, 99], [11, 98, 47], [78, 59, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 107], []]
 b := ![[], [38, 100, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [54, 5, 45, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1637834, 302584, -29430]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15026, 2776, -270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![17, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![17, 1, 0]] 
 ![![113, 0, 0], ![17, 1, 0], ![7, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![17, 1, 0], ![2, 18, 5], ![117, -13, 16]]]
  hmulB := by decide  
  f := ![![![-1405, -12958, -3600], ![-226, 81360, 0]], ![![-216, -1944, -540], ![1, 12204, 0]], ![![-92, -803, -223], ![19, 5040, 0]]]
  g := ![![![1, 0, 0], ![-17, 113, 0], ![-7, 0, 113]], ![![0, 1, 0], ![-3, 18, 5], ![2, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, 1, 0]] 
 ![![113, 0, 0], ![26, 1, 0], ![86, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, 1, 0], ![2, 27, 5], ![117, -13, 25]]]
  hmulB := by decide  
  f := ![![![5907, 86381, 16000], ![2147, -361600, 0]], ![![1342, 19867, 3680], ![566, -83168, 0]], ![![4488, 65741, 12177], ![1667, -275200, 0]]]
  g := ![![![1, 0, 0], ![-26, 113, 0], ![-86, 0, 113]], ![![0, 1, 0], ![-10, 27, 5], ![-15, -13, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-43, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-43, 1, 0]] 
 ![![113, 0, 0], ![70, 1, 0], ![46, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-43, 1, 0], ![2, -42, 5], ![117, -13, -44]]]
  hmulB := by decide  
  f := ![![![-2505, 65254, -7770], ![1582, 175602, 0]], ![![-1536, 40395, -4810], ![1018, 108706, 0]], ![![-995, 26563, -3163], ![709, 71484, 0]]]
  g := ![![![1, 0, 0], ![-70, 113, 0], ![-46, 0, 113]], ![![-1, 1, 0], ![24, -42, 5], ![27, -13, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![17, 1, 0]] ![![113, 0, 0], ![26, 1, 0]]
  ![![113, 0, 0], ![21, 54, 1]] where
 M := ![![![12769, 0, 0], ![2938, 113, 0]], ![![1921, 113, 0], ![444, 44, 5]]]
 hmul := by decide  
 g := ![![![![92, -54, -1], ![113, 0, 0]], ![![5, -53, -1], ![113, 0, 0]]], ![![![-4, -53, -1], ![113, 0, 0]], ![![3, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![21, 54, 1]] ![![113, 0, 0], ![-43, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-4859, 113, 0]], ![![2373, 6102, 113], ![-678, -2260, 226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-43, 1, 0]]], ![![![21, 54, 1]], ![![-6, -20, 2]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [124, 105, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 20, 81], [45, 106, 46], [0, 1]]
 g := ![![[114, 47, 8], [105, 21, 25], [38], [103, 68, 121], [1, 99, 36], [1]], ![[76, 120, 51, 42], [58, 74, 57, 68], [109, 95, 11, 107], [15, 19, 9, 61], [91, 4, 1, 120], [36, 53, 17, 73]], ![[53, 47, 39, 67], [100, 71, 40, 67], [62, 124, 65, 20], [106, 57, 55, 106], [66, 77, 124, 105], [109, 17, 112, 54]]]
 h' := ![![[88, 20, 81], [61, 2, 95], [114, 51, 122], [55, 66], [3, 74, 11], [3, 22, 6], [0, 1]], ![[45, 106, 46], [65, 95, 72], [19, 88, 45], [21, 50, 12], [113, 76, 48], [98, 9, 5], [88, 20, 81]], ![[0, 1], [49, 30, 87], [115, 115, 87], [104, 11, 115], [74, 104, 68], [12, 96, 116], [45, 106, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 58], []]
 b := ![[], [57, 105, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [124, 105, 121, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2620137, -270764, 38735]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20631, -2132, 305]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![41, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![41, 1, 0]] 
 ![![131, 0, 0], ![41, 1, 0], ![49, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![41, 1, 0], ![2, 42, 5], ![117, -13, 40]]]
  hmulB := by decide  
  f := ![![![3244, 79283, 9440], ![1703, -247328, 0]], ![![1016, 24776, 2950], ![525, -77290, 0]], ![![1194, 29655, 3531], ![699, -92512, 0]]]
  g := ![![![1, 0, 0], ![-41, 131, 0], ![-49, 0, 131]], ![![0, 1, 0], ![-15, 42, 5], ![-10, -13, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-40, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-40, 1, 0]] 
 ![![131, 0, 0], ![91, 1, 0], ![29, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-40, 1, 0], ![2, -39, 5], ![117, -13, -41]]]
  hmulB := by decide  
  f := ![![![-4503, 101071, -12960], ![2227, 339552, 0]], ![![-3119, 70188, -9000], ![1573, 235800, 0]], ![![-977, 22374, -2869], ![558, 75168, 0]]]
  g := ![![![1, 0, 0], ![-91, 131, 0], ![-29, 0, 131]], ![![-1, 1, 0], ![26, -39, 5], ![19, -13, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-1, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-1, 1, 0]] 
 ![![131, 0, 0], ![130, 1, 0], ![79, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-1, 1, 0], ![2, 0, 5], ![117, -13, -2]]]
  hmulB := by decide  
  f := ![![![17161, 0, 42900], ![0, -1123980, 0]], ![![17029, 0, 42570], ![1, -1115334, 0]], ![![10349, 0, 25871], ![0, -677820, 0]]]
  g := ![![![1, 0, 0], ![-130, 131, 0], ![-79, 0, 131]], ![![-1, 1, 0], ![-3, 0, 5], ![15, -13, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![41, 1, 0]] ![![131, 0, 0], ![-40, 1, 0]]
  ![![131, 0, 0], ![13, -52, 1]] where
 M := ![![![17161, 0, 0], ![-5240, 131, 0]], ![![5371, 131, 0], ![-1638, 2, 5]]]
 hmul := by decide  
 g := ![![![![118, 52, -1], ![131, 0, 0]], ![![-40, 1, 0], ![0, 0, 0]]], ![![![28, 53, -1], ![131, 0, 0]], ![![-13, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![13, -52, 1]] ![![131, 0, 0], ![-1, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-131, 131, 0]], ![![1703, -6812, 131], ![0, 0, -262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-1, 1, 0]]], ![![![13, -52, 1]], ![![0, 0, -2]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-32, 24, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-32, 24, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![105, 24, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-32, 24, 1], ![165, -21, 119], ![2756, -286, -69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -24, 137]], ![![-1, 0, 1], ![-90, -21, 119], ![73, 10, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [104, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 136], [0, 1]]
 g := ![![[13, 77], [120], [119], [16, 11], [130], [50], [1]], ![[29, 60], [120], [119], [77, 126], [130], [50], [1]]]
 h' := ![![[18, 136], [85, 112], [80, 42], [117, 121], [44, 82], [136, 33], [33, 18], [0, 1]], ![[0, 1], [46, 25], [14, 95], [103, 16], [13, 55], [45, 104], [83, 119], [18, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [110, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [104, 119, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6084, 780, -2365]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1857, 420, -2365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![18, 1, 0]] 
 ![![137, 0, 0], ![18, 1, 0], ![69, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![18, 1, 0], ![2, 19, 5], ![117, -13, 17]]]
  hmulB := by decide  
  f := ![![![14455, 141053, 37125], ![3014, -1017225, 0]], ![![1896, 18522, 4875], ![412, -133575, 0]], ![![7275, 71041, 18698], ![1558, -512325, 0]]]
  g := ![![![1, 0, 0], ![-18, 137, 0], ![-69, 0, 137]], ![![0, 1, 0], ![-5, 19, 5], ![-6, -13, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-32, 24, 1]] ![![137, 0, 0], ![18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![2466, 137, 0]], ![![-4384, 3288, 137], ![-411, 411, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![18, 1, 0]]], ![![![-32, 24, 1]], ![![-3, 3, 1]]]]
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


lemma PB182I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB182I2 : PrimesBelowBoundCertificateInterval O 79 137 182 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB182I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I103N1, I107N1, I113N0, I113N1, I113N2, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N1], [], [], [I103N1], [I107N1], [], [I113N0, I113N1, I113N2], [], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
