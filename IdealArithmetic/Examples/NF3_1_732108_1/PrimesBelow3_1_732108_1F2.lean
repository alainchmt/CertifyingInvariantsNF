
import IdealArithmetic.Examples.NF3_1_732108_1.RI3_1_732108_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6424188, 83031, 196916]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![6424188, 83031, 196916]] 
 ![![83, 0, 0], ![0, 83, 0], ![8, 7, 1]] where
  M :=![![![6424188, 83031, 196916], ![7119830, 92022, 218239], ![1299903, 16801, 39845]]]
  hmulB := by decide  
  f := ![![![-203, 187, -21]], ![![-1151, 864, 956]], ![![-31, 13, 82]]]
  g := ![![![58420, -15607, 196916], ![64746, -17297, 218239], ![11821, -3158, 39845]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [5, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 82], [0, 1]]
 g := ![![[45, 10], [27, 23], [68], [21], [55, 78], [1]], ![[36, 73], [81, 60], [68], [21], [18, 5], [1]]]
 h' := ![![[24, 82], [31, 33], [9, 40], [73, 63], [57, 42], [78, 24], [0, 1]], ![[0, 1], [76, 50], [56, 43], [8, 20], [69, 41], [73, 59], [24, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [9, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [5, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![994, -811, -1100]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![118, 83, -1100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, 187, -21]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-203, 187, -21]] 
 ![![83, 0, 0], ![49, 1, 0], ![31, 0, 1]] where
  M :=![![![-203, 187, -21], ![-1151, 864, 956], ![7108, -6465, 282]]]
  hmulB := by decide  
  f := ![![![6424188, 83031, 196916]], ![![3878374, 50127, 118881]], ![![2415057, 31214, 74027]]]
  g := ![![![-105, 187, -21], ![-881, 864, 956], ![3797, -6465, 282]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![6424188, 83031, 196916]] ![![-203, 187, -21]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![36, -4, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![36, -4, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![36, 85, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![36, -4, 1], ![45, -5, -21], ![-157, 146, 8]]]
  hmulB := by decide  
  f := ![![![-35, 4, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -85, 89]], ![![0, -1, 1], ![9, 20, -21], ![-5, -6, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [85, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 88], [0, 1]]
 g := ![![[12, 22], [17], [79], [13, 16], [82, 79], [1]], ![[0, 67], [17], [79], [69, 73], [47, 10], [1]]]
 h' := ![![[48, 88], [15, 72], [83, 62], [52, 48], [61, 85], [4, 48], [0, 1]], ![[0, 1], [0, 17], [33, 27], [42, 41], [47, 4], [83, 41], [48, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [8, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [85, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, 502, -4264]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1729, 4078, -4264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![21, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![21, 1, 0]] 
 ![![89, 0, 0], ![21, 1, 0], ![81, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![21, 1, 0], ![-2, 23, 5], ![37, -33, 20]]]
  hmulB := by decide  
  f := ![![![-849, 9775, 2125], ![0, -37825, 0]], ![![-200, 2300, 500], ![1, -8900, 0]], ![![-759, 8897, 1934], ![-58, -34425, 0]]]
  g := ![![![1, 0, 0], ![-21, 89, 0], ![-81, 0, 89]], ![![0, 1, 0], ![-10, 23, 5], ![-10, -33, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![36, -4, 1]] ![![89, 0, 0], ![21, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1869, 89, 0]], ![![3204, -356, 89], ![801, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![21, 1, 0]]], ![![![36, -4, 1]], ![![9, -1, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [32, 63, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 5, 24], [8, 91, 73], [0, 1]]
 g := ![![[89, 33, 79], [83, 96], [82, 70], [45, 64], [15, 50], [1]], ![[57, 13, 44, 64], [59, 96], [18, 49], [92, 32], [95, 64], [39, 39, 15, 50]], ![[8, 57, 11, 32], [90, 93], [45, 47], [86, 73], [18, 70], [86, 42, 3, 47]]]
 h' := ![![[62, 5, 24], [84, 13, 46], [11, 34, 75], [4, 57, 19], [59, 32, 8], [65, 34, 70], [0, 1]], ![[8, 91, 73], [63, 46, 36], [60, 61, 75], [65, 22, 90], [14, 85, 41], [12, 23, 8], [62, 5, 24]], ![[0, 1], [41, 38, 15], [37, 2, 44], [64, 18, 85], [87, 77, 48], [88, 40, 19], [8, 91, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 11], []]
 b := ![[], [40, 18, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [32, 63, 27, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11704656223, -9127453717, -7858214440]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![120666559, -94097461, -81012520]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![72, -5, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![72, -5, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![72, 96, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![72, -5, 1], ![47, 29, -26], ![-194, 179, 45]]]
  hmulB := by decide  
  f := ![![![-71, 5, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -96, 101]], ![![0, -1, 1], ![19, 25, -26], ![-34, -41, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [3, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 100], [0, 1]]
 g := ![![[55, 80], [19], [12, 54], [96], [82], [37, 1]], ![[86, 21], [19], [91, 47], [96], [82], [74, 100]]]
 h' := ![![[37, 100], [27, 79], [65, 76], [20, 16], [56, 55], [91, 53], [0, 1]], ![[0, 1], [21, 22], [49, 25], [6, 85], [71, 46], [32, 48], [37, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [72, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [3, 64, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1698, -564, -5523]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3954, 5244, -5523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![26, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![26, 1, 0]] 
 ![![101, 0, 0], ![26, 1, 0], ![56, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![26, 1, 0], ![-2, 28, 5], ![37, -33, 25]]]
  hmulB := by decide  
  f := ![![![-4559, 65665, 11725], ![-505, -236845, 0]], ![![-1180, 16885, 3015], ![-100, -60903, 0]], ![![-2536, 36408, 6501], ![-248, -131320, 0]]]
  g := ![![![1, 0, 0], ![-26, 101, 0], ![-56, 0, 101]], ![![0, 1, 0], ![-10, 28, 5], ![-5, -33, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![72, -5, 1]] ![![101, 0, 0], ![26, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2626, 101, 0]], ![![7272, -505, 101], ![1919, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![26, 1, 0]]], ![![![72, -5, 1]], ![![19, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13407845, 173293, 410981]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![13407845, 173293, 410981]] 
 ![![103, 0, 0], ![31, 1, 0], ![1, 0, 1]] where
  M :=![![![13407845, 173293, 410981], ![14859711, 192058, 455484], ![2713012, 35065, 83160]]]
  hmulB := by decide  
  f := ![![![-3180, 2885, -86]], ![![-1044, 921, 115]], ![![1013, -908, -33]]]
  g := ![![![74027, 173293, 410981], ![82043, 192058, 455484], ![14979, 35065, 83160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -6]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1, 2, -6]] 
 ![![103, 0, 0], ![35, 1, 0], ![29, 0, 1]] where
  M :=![![![-1, 2, -6], ![-226, 201, 16], ![128, -150, 189]]]
  hmulB := by decide  
  f := ![![![40389, 522, 1238]], ![![14159, 183, 434]], ![![11451, 148, 351]]]
  g := ![![![1, 2, -6], ![-75, 201, 16], ![-1, -150, 189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 13, -2]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-14, 13, -2]] 
 ![![103, 0, 0], ![36, 1, 0], ![35, 0, 1]] where
  M :=![![![-14, 13, -2], ![-100, 78, 67], ![499, -457, 37]]]
  hmulB := by decide  
  f := ![![![33505, 433, 1027]], ![![12071, 156, 370]], ![![11451, 148, 351]]]
  g := ![![![-4, 13, -2], ![-51, 78, 67], ![152, -457, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![13407845, 173293, 410981]] ![![-1, 2, -6]]
  ![![33505, 433, 1027]] where
 M := ![![![33505, 433, 1027]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![33505, 433, 1027]] ![![-14, 13, -2]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-6, 18, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-6, 18, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![101, 18, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-6, 18, 1], ![1, -3, 89], ![657, -580, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -18, 107]], ![![-1, 0, 1], ![-84, -15, 89], ![59, 4, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [10, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 106], [0, 1]]
 g := ![![[65, 75], [35, 83], [75], [34, 92], [27], [99, 1]], ![[0, 32], [13, 24], [75], [47, 15], [27], [91, 106]]]
 h' := ![![[99, 106], [78, 90], [39, 46], [88, 90], [31, 78], [80, 54], [0, 1]], ![[0, 1], [0, 17], [99, 61], [10, 17], [49, 29], [76, 53], [99, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [71, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [10, 8, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![897, -658, -845]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![806, 136, -845]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![18, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![18, 1, 0]] 
 ![![107, 0, 0], ![18, 1, 0], ![56, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![18, 1, 0], ![-2, 20, 5], ![37, -33, 17]]]
  hmulB := by decide  
  f := ![![![-1163, 11640, 2910], ![0, -62274, 0]], ![![-194, 1940, 485], ![1, -10379, 0]], ![![-608, 6092, 1523], ![-4, -32592, 0]]]
  g := ![![![1, 0, 0], ![-18, 107, 0], ![-56, 0, 107]], ![![0, 1, 0], ![-6, 20, 5], ![-3, -33, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-6, 18, 1]] ![![107, 0, 0], ![18, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![1926, 107, 0]], ![![-642, 1926, 107], ![-107, 321, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![18, 1, 0]]], ![![![-6, 18, 1]], ![![-1, 3, 1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [34, 88, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 22, 5], [83, 86, 104], [0, 1]]
 g := ![![[59, 11, 100], [32, 108], [27, 10, 93], [7, 54, 36], [26, 104], [1]], ![[73, 102, 90, 46], [56, 48], [35, 106, 66, 36], [102, 2, 40, 102], [17, 78], [19, 5, 94, 16]], ![[66, 103, 42, 106], [19, 12], [40, 81, 71, 25], [69, 75, 90, 1], [86, 100], [100, 83, 49, 93]]]
 h' := ![![[65, 22, 5], [47, 29, 10], [63, 82, 33], [89, 28, 23], [54, 51, 6], [75, 21, 39], [0, 1]], ![[83, 86, 104], [89, 60, 24], [85, 71, 87], [79, 6, 47], [105, 34, 8], [62, 39, 80], [65, 22, 5]], ![[0, 1], [89, 20, 75], [100, 65, 98], [80, 75, 39], [34, 24, 95], [61, 49, 99], [83, 86, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 65], []]
 b := ![[], [15, 39, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [34, 88, 70, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1637834, 1720238, -1046836]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15026, 15782, -9604]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-17, -37, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-17, -37, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![96, 76, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-17, -37, 1], ![111, -124, -186], ![-1378, 1235, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -76, 113]], ![![-1, -1, 1], ![159, 124, -186], ![-2, 19, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [87, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 112], [0, 1]]
 g := ![![[5, 13], [64], [52], [51], [102, 11], [17, 1]], ![[0, 100], [64], [52], [51], [63, 102], [34, 112]]]
 h' := ![![[17, 112], [64, 76], [78, 8], [67, 39], [53, 86], [103, 89], [0, 1]], ![[0, 1], [0, 37], [101, 105], [52, 74], [46, 27], [34, 24], [17, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [61, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [87, 96, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![398, 268, -2875]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2446, 1936, -2875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-40, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-40, 1, 0]] 
 ![![113, 0, 0], ![73, 1, 0], ![12, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-40, 1, 0], ![-2, -38, 5], ![37, -33, -41]]]
  hmulB := by decide  
  f := ![![![-6855, -138635, 18240], ![1243, -412224, 0]], ![![-4431, -89535, 11780], ![792, -266228, 0]], ![![-700, -14723, 1937], ![211, -43776, 0]]]
  g := ![![![1, 0, 0], ![-73, 113, 0], ![-12, 0, 113]], ![![-1, 1, 0], ![24, -38, 5], ![26, -33, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-17, -37, 1]] ![![113, 0, 0], ![-40, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-4520, 113, 0]], ![![-1921, -4181, 113], ![791, 1356, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-40, 1, 0]]], ![![![-17, -37, 1]], ![![7, 12, -2]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [14, 26, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 94, 115], [108, 32, 12], [0, 1]]
 g := ![![[100, 84, 30], [62, 50, 25], [118, 70, 32], [32, 123, 41], [57, 21, 103], [1]], ![[97, 124, 36, 36], [121, 16, 21, 64], [124, 116, 39, 115], [117, 10, 111, 26], [113, 118, 50, 72], [1, 122, 11, 50]], ![[122, 15, 0, 48], [52, 54, 20, 92], [66, 6, 21, 3], [29, 1, 106, 51], [4, 120, 110, 114], [2, 78, 65, 77]]]
 h' := ![![[124, 94, 115], [21, 102, 41], [126, 60, 5], [60, 12, 64], [91, 71, 26], [113, 101, 105], [0, 1]], ![[108, 32, 12], [55, 2, 88], [68, 122, 75], [87, 119, 126], [106, 53, 107], [86, 42, 116], [124, 94, 115]], ![[0, 1], [88, 23, 125], [8, 72, 47], [112, 123, 64], [94, 3, 121], [98, 111, 33], [108, 32, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 119], []]
 b := ![[], [62, 41, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [14, 26, 22, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-939927, 666115, 998855]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7401, 5245, 7865]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-14, 17, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-14, 17, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![117, 17, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-14, 17, 1], ![3, -13, 84], ![620, -547, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-117, -17, 131]], ![![-1, 0, 1], ![-75, -11, 84], ![61, 4, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [96, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 130], [0, 1]]
 g := ![![[81, 101], [86, 108], [36], [41], [60], [113], [1]], ![[50, 30], [119, 23], [36], [41], [60], [113], [1]]]
 h' := ![![[84, 130], [128, 25], [5, 97], [29, 6], [67, 33], [71, 45], [35, 84], [0, 1]], ![[0, 1], [1, 106], [31, 34], [9, 125], [88, 98], [52, 86], [17, 47], [84, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [78, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [96, 47, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9231, -7120, -7855]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7086, 965, -7855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![47, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![47, 1, 0]] 
 ![![131, 0, 0], ![47, 1, 0], ![63, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![47, 1, 0], ![-2, 49, 5], ![37, -33, 46]]]
  hmulB := by decide  
  f := ![![![21180, -550003, -56120], ![3537, 1470344, 0]], ![![7582, -197284, -20130], ![1311, 527406, 0]], ![![10198, -264505, -26989], ![1667, 707112, 0]]]
  g := ![![![1, 0, 0], ![-47, 131, 0], ![-63, 0, 131]], ![![0, 1, 0], ![-20, 49, 5], ![-10, -33, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-14, 17, 1]] ![![131, 0, 0], ![47, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![6157, 131, 0]], ![![-1834, 2227, 131], ![-655, 786, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![47, 1, 0]]], ![![![-14, 17, 1]], ![![-5, 6, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![15, -10, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![15, -10, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![15, 127, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![15, -10, 1], ![57, -38, -51], ![-379, 344, -7]]]
  hmulB := by decide  
  f := ![![![-14, 10, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -127, 137]], ![![0, -1, 1], ![6, 47, -51], ![-2, 9, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [105, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 136], [0, 1]]
 g := ![![[53, 107], [88], [99], [116, 133], [135], [101], [1]], ![[0, 30], [88], [99], [45, 4], [135], [101], [1]]]
 h' := ![![[52, 136], [11, 92], [49, 122], [13, 28], [17, 74], [9, 86], [32, 52], [0, 1]], ![[0, 1], [0, 45], [91, 15], [99, 109], [29, 63], [97, 51], [133, 85], [52, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [78, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [105, 85, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5049, 5558, -6940]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![723, 6474, -6940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![51, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![51, 1, 0]] 
 ![![137, 0, 0], ![51, 1, 0], ![7, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![51, 1, 0], ![-2, 53, 5], ![37, -33, 50]]]
  hmulB := by decide  
  f := ![![![5492, -154979, -14620], ![959, 400588, 0]], ![![2023, -57667, -5440], ![412, 149056, 0]], ![![262, -7919, -747], ![99, 20468, 0]]]
  g := ![![![1, 0, 0], ![-51, 137, 0], ![-7, 0, 137]], ![![0, 1, 0], ![-20, 53, 5], ![10, -33, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![15, -10, 1]] ![![137, 0, 0], ![51, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![6987, 137, 0]], ![![2055, -1370, 137], ![822, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![51, 1, 0]]], ![![![15, -10, 1]], ![![6, -4, 0]]]]
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


lemma PB243I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB243I2 : PrimesBelowBoundCertificateInterval O 79 137 243 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB243I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
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
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
