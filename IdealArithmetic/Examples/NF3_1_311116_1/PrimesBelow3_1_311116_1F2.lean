
import IdealArithmetic.Examples.NF3_1_311116_1.RI3_1_311116_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [61, 37, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 25, 34], [74, 57, 49], [0, 1]]
 g := ![![[72, 69, 16], [64, 51, 27], [37, 75], [14, 16], [50, 81, 1], []], ![[74, 28, 15, 24], [40, 1, 73, 14], [13, 51], [22, 10], [15, 66, 53, 76], [52, 77]], ![[53, 76, 58, 23], [58, 51, 35, 41], [6, 11], [70, 11], [25, 27, 8, 81], [37, 77]]]
 h' := ![![[7, 25, 34], [80, 60, 79], [71, 62, 39], [2, 49, 18], [21, 15, 79], [0, 0, 1], [0, 1]], ![[74, 57, 49], [44, 24, 69], [54, 5, 15], [73, 65, 36], [2, 61, 33], [31, 37, 57], [7, 25, 34]], ![[0, 1], [27, 82, 18], [56, 16, 29], [67, 52, 29], [41, 7, 54], [65, 46, 25], [74, 57, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 47], []]
 b := ![[], [1, 62, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [61, 37, 2, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-891503, 76028, -38014]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10741, 916, -458]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62404478193752135678, -6317070163389197985, -4318309195253705569]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-62404478193752135678, -6317070163389197985, -4318309195253705569]] 
 ![![89, 0, 0], ![0, 89, 0], ![2, 32, 1]] where
  M :=![![![-62404478193752135678, -6317070163389197985, -4318309195253705569], ![-485328603577567795407, -49128763349008298234, -33584111785081482341], ![-436099953516572164947, -44145453729485217901, -30177552858840704279]]]
  hmulB := by decide  
  f := ![![![681310595, 434893114, -581478851]], ![![-61495036566, 5039969929, 3190837535]], ![![-21195121327, 1668442327, 1176170045]]]
  g := ![![![-604133256216232860, 1481672180727296407, -4318309195253705569], ![-4698431236038256525, 11523177682849428502, -33584111785081482341], ![-4221852222459446701, 10354339750038396843, -30177552858840704279]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [22, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 88], [0, 1]]
 g := ![![[62, 85], [22], [11], [85, 39], [27, 40], [1]], ![[0, 4], [22], [11], [22, 50], [24, 49], [1]]]
 h' := ![![[60, 88], [14, 68], [26, 17], [88, 10], [29, 67], [67, 60], [0, 1]], ![[0, 1], [0, 21], [67, 72], [65, 79], [44, 22], [18, 29], [60, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [21, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [22, 29, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![450, 2038, -309]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 134, -309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![681310595, 434893114, -581478851]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![681310595, 434893114, -581478851]] 
 ![![89, 0, 0], ![76, 1, 0], ![36, 0, 1]] where
  M :=![![![681310595, 434893114, -581478851], ![-61495036566, 5039969929, 3190837535], ![80112750819, -13657456853, 3735290587]]]
  hmulB := by decide  
  f := ![![![-62404478193752135678, -6317070163389197985, -4318309195253705569]], ![![-58742347711266630415, -5946360626590869046, -4064894501397338265]], ![![-30142260320130888195, -3051235725971869049, -2085805436943529267]]]
  g := ![![![-128509297, 434893114, -581478851], ![-6285425870, 5039969929, 3190837535], ![11051786635, -13657456853, 3735290587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-62404478193752135678, -6317070163389197985, -4318309195253705569]] ![![681310595, 434893114, -581478851]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![258085, -13794, -21580]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![258085, -13794, -21580]] 
 ![![97, 0, 0], ![0, 97, 0], ![26, 89, 1]] where
  M :=![![![258085, -13794, -21580], ![-2372022, 359977, -61184], ![-259692, -327256, 401359]]]
  hmulB := by decide  
  f := ![![![-1283063687, -129881758, -88786348]], ![![-9978570858, -1010109115, -690504200]], ![![-9591947116, -970972031, -663750337]]]
  g := ![![![8445, 19658, -21580], ![-8054, 59849, -61184], ![-110258, -371631, 401359]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [21, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 96], [0, 1]]
 g := ![![[34, 79], [16], [35], [72], [48], [62, 1]], ![[82, 18], [16], [35], [72], [48], [27, 96]]]
 h' := ![![[62, 96], [61, 46], [94, 93], [76, 61], [91, 84], [56, 40], [0, 1]], ![[0, 1], [3, 51], [40, 4], [75, 36], [61, 13], [14, 57], [62, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [69, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [21, 35, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![587174, 600099, -186526]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56050, 177329, -186526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1283063687, -129881758, -88786348]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-1283063687, -129881758, -88786348]] 
 ![![97, 0, 0], ![49, 1, 0], ![69, 0, 1]] where
  M :=![![![-1283063687, -129881758, -88786348], ![-9978570858, -1010109115, -690504200], ![-8966408028, -907650064, -620463841]]]
  hmulB := by decide  
  f := ![![![258085, -13794, -21580]], ![![105919, -3257, -11532]], ![![180909, -13186, -11213]]]
  g := ![![![115540211, -129881758, -88786348], ![898572841, -1010109115, -690504200], ![807427321, -907650064, -620463841]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![258085, -13794, -21580]] ![![-1283063687, -129881758, -88786348]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [62, 25, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 57], [33, 94, 44], [0, 1]]
 g := ![![[0, 79, 47], [86, 92], [23, 23, 4], [2, 97], [48, 79], [1]], ![[63, 99, 81, 2], [43, 79], [43, 33, 72, 42], [86, 5], [4, 85], [80, 1, 64, 60]], ![[55, 91, 52, 57], [10, 9], [87, 79, 21, 28], [6, 19], [30, 49], [45, 99, 87, 41]]]
 h' := ![![[0, 6, 57], [64, 56, 59], [89, 66, 71], [42, 99, 2], [60, 32, 81], [39, 76, 33], [0, 1]], ![[33, 94, 44], [45, 70, 52], [61, 4, 33], [91, 68, 74], [75, 99, 45], [90, 59, 61], [0, 6, 57]], ![[0, 1], [6, 76, 91], [11, 31, 98], [86, 35, 25], [16, 71, 76], [19, 67, 7], [33, 94, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 6], []]
 b := ![[], [49, 25, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [62, 25, 68, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3939808, 538330, -176245]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39008, 5330, -1745]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112097, -14756, 381]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![112097, -14756, 381]] 
 ![![103, 0, 0], ![0, 103, 0], ![82, 64, 1]] where
  M :=![![![112097, -14756, 381], ![-3120, 80299, -88917], ![-1615365, 95775, 124567]]]
  hmulB := by decide  
  f := ![![![-179792536, -18200009, -12441411]], ![![-1398272415, -141544088, -96758643]], ![![-1024163719, -103673875, -70870805]]]
  g := ![![![785, -380, 381], ![70758, 56029, -88917], ![-114853, -76471, 124567]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [74, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 102], [0, 1]]
 g := ![![[21, 82], [33, 46], [93, 30], [7], [49], [94, 1]], ![[4, 21], [31, 57], [29, 73], [7], [49], [85, 102]]]
 h' := ![![[94, 102], [30, 59], [19, 47], [80, 66], [17, 25], [48, 7], [0, 1]], ![[0, 1], [14, 44], [8, 56], [1, 37], [101, 78], [88, 96], [94, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [1, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [74, 9, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1617, 943, -386]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![323, 249, -386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179792536, 18200009, 12441411]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![179792536, 18200009, 12441411]] 
 ![![103, 0, 0], ![29, 1, 0], ![91, 0, 1]] where
  M :=![![![179792536, 18200009, 12441411], ![1398272415, 141544088, 96758643], ![1256440545, 127186755, 86944061]]]
  hmulB := by decide  
  f := ![![![-112097, 14756, -381]], ![![-31531, 3375, 756]], ![![-83354, 12107, -1546]]]
  g := ![![![-14370642, 18200009, 12441411], ![-111762550, 141544088, 96758643], ![-100426067, 127186755, 86944061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![112097, -14756, 381]] ![![179792536, 18200009, 12441411]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [17, 56, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 77, 26], [86, 29, 81], [0, 1]]
 g := ![![[39, 25, 33], [89, 86, 48], [72, 52], [19, 105, 44], [59, 52], [1]], ![[14, 101, 31, 22], [33, 88, 80, 46], [85, 90], [87, 0, 8, 72], [33, 1], [21, 14, 44, 28]], ![[95, 41, 28, 36], [61, 4, 36, 53], [60, 75], [66, 80, 9, 101], [37, 76], [84, 94, 68, 79]]]
 h' := ![![[86, 77, 26], [92, 4, 56], [64, 82, 35], [105, 88, 42], [35, 70, 30], [90, 51, 65], [0, 1]], ![[86, 29, 81], [75, 37, 16], [29, 59, 44], [46, 19, 82], [11, 105, 15], [12, 91, 1], [86, 77, 26]], ![[0, 1], [5, 66, 35], [12, 73, 28], [47, 0, 90], [27, 39, 62], [11, 72, 41], [86, 29, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 102], []]
 b := ![[], [82, 16, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [17, 56, 42, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172065095, -10976916, 9780656]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1608085, -102588, 91408]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16126, -5691, 8641]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-16126, -5691, 8641]] 
 ![![109, 0, 0], ![0, 109, 0], ![22, 61, 1]] where
  M :=![![![-16126, -5691, 8641], ![916155, -79354, -42787], ![-1107165, 198325, -62281]]]
  hmulB := by decide  
  f := ![![![123192461, 12470506, 8524759]], ![![958085490, 96984919, 66298277]], ![![568939013, 57592464, 39369844]]]
  g := ![![![-1892, -4888, 8641], ![17041, 23217, -42787], ![2413, 36674, -62281]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [78, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 108], [0, 1]]
 g := ![![[67, 7], [73], [104, 82], [100, 22], [20], [6, 1]], ![[0, 102], [73], [51, 27], [14, 87], [20], [12, 108]]]
 h' := ![![[6, 108], [19, 15], [63, 20], [48, 55], [9, 83], [77, 67], [0, 1]], ![[0, 1], [0, 94], [74, 89], [51, 54], [71, 26], [43, 42], [6, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [45, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [78, 103, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-637, 171, -351]
  a := ![-2, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65, 198, -351]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123192461, 12470506, 8524759]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![123192461, 12470506, 8524759]] 
 ![![109, 0, 0], ![71, 1, 0], ![45, 0, 1]] where
  M :=![![![123192461, 12470506, 8524759], ![958085490, 96984919, 66298277], ![860903385, 87147385, 59573401]]]
  hmulB := by decide  
  f := ![![![-16126, -5691, 8641]], ![![-2099, -4435, 5236]], ![![-16815, -530, 2996]]]
  g := ![![![-10512180, 12470506, 8524759], ![-81754736, 96984919, 66298277], ![-73462055, 87147385, 59573401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-16126, -5691, 8641]] ![![123192461, 12470506, 8524759]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, 1, 4]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-34, 1, 4]] 
 ![![113, 0, 0], ![0, 113, 0], ![48, 85, 1]] where
  M :=![![![-34, 1, 4], ![435, -56, 2], ![-120, 70, -59]]]
  hmulB := by decide  
  f := ![![![28, 3, 2]], ![![225, 22, 16]], ![![183, 18, 13]]]
  g := ![![![-2, -3, 4], ![3, -2, 2], ![24, 45, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [29, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 112], [0, 1]]
 g := ![![[2, 109], [53], [72], [22], [0, 87], [55, 1]], ![[8, 4], [53], [72], [22], [39, 26], [110, 112]]]
 h' := ![![[55, 112], [98, 83], [77, 77], [40, 80], [0, 19], [100, 58], [0, 1]], ![[0, 1], [30, 30], [18, 36], [33, 33], [28, 94], [13, 55], [55, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [2, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [29, 58, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4507, 3294, -158]
  a := ![7, 5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![107, 148, -158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 3, 2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![28, 3, 2]] 
 ![![113, 0, 0], ![56, 1, 0], ![43, 0, 1]] where
  M :=![![![28, 3, 2], ![225, 22, 16], ![210, 20, 13]]]
  hmulB := by decide  
  f := ![![![-34, 1, 4]], ![![-13, 0, 2]], ![![-14, 1, 1]]]
  g := ![![![-2, 3, 2], ![-15, 22, 16], ![-13, 20, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-34, 1, 4]] ![![28, 3, 2]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [68, 46, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 19, 93], [79, 107, 34], [0, 1]]
 g := ![![[70, 82, 82], [126, 49, 11], [71, 8, 41], [122, 23, 34], [115, 112, 70], [1]], ![[86, 89, 86, 80], [105, 119, 87, 102], [75, 13, 126, 20], [58, 62, 83, 93], [118, 47, 82, 105], [71, 105, 24, 66]], ![[117, 71, 61, 115], [28, 67, 10, 76], [74, 13, 34, 62], [16, 45, 76, 72], [72, 30, 80, 104], [18, 63, 64, 61]]]
 h' := ![![[66, 19, 93], [68, 20, 35], [125, 30, 97], [86, 58, 101], [54, 100, 65], [59, 81, 18], [0, 1]], ![[79, 107, 34], [62, 126, 17], [121, 62, 88], [44, 86, 72], [73, 122, 126], [93, 15, 61], [66, 19, 93]], ![[0, 1], [45, 108, 75], [59, 35, 69], [93, 110, 81], [24, 32, 63], [71, 31, 48], [79, 107, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 27], []]
 b := ![[], [58, 21, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [68, 46, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5743067, 880745, -310515]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45221, 6935, -2445]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9143810260964, 925608107801, 632739846121]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![9143810260964, 925608107801, 632739846121]] 
 ![![131, 0, 0], ![15, 1, 0], ![89, 0, 1]] where
  M :=![![![9143810260964, 925608107801, 632739846121], ![71112727704471, 7198587399840, 4920908800685], ![63899504413611, 6468408429493, 4421763076437]]]
  hmulB := by decide  
  f := ![![![-11032625, -938384, 2623045]], ![![877743, -326133, 237346]], ![![-9410402, -214107, 1584874]]]
  g := ![![![-466062272220, 925608107801, 632739846121], ![-3624633332474, 7198587399840, 4920908800685], ![-3256973555967, 6468408429493, 4421763076437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19504165493889638675644452375413, 1974364428153986844350891612660, 1349663031177242820243230030269]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![19504165493889638675644452375413, 1974364428153986844350891612660, 1349663031177242820243230030269]] 
 ![![131, 0, 0], ![21, 1, 0], ![51, 0, 1]] where
  M :=![![![19504165493889638675644452375413, 1974364428153986844350891612660, 1349663031177242820243230030269], ![151686700651604185119321518107032, 15354916163134155442886855419119, 10496523537746678245862119645691], ![136300565463527738436032182441947, 13797411023443692518516020899151, 9431822878672194909834180581139]]]
  hmulB := by decide  
  f := ![![![-22162252531311800, -539585363218121, 3771841758735049]], ![![-455474422166541, -436669972807167, 551139870193834]], ![![-10714084569254631, 361707267718706, 1130612305152546]]]
  g := ![![![-693055741125064648000984755986, 1974364428153986844350891612660, 1349663031177242820243230030269], ![-5389994192361020379544049981868, 15354916163134155442886855419119, 10496523537746678245862119645691], ![-4843267426267723243162957756323, 13797411023443692518516020899151, 9431822878672194909834180581139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38300171026865230387921152521277053, 3877043357294461097847239409044522, 2650322308786816156536524059859696]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![38300171026865230387921152521277053, 3877043357294461097847239409044522, 2650322308786816156536524059859696]] 
 ![![131, 0, 0], ![94, 1, 0], ![3, 0, 1]] where
  M :=![![![38300171026865230387921152521277053, 3877043357294461097847239409044522, 2650322308786816156536524059859696], ![297865939420859528199486316691980734, 30152323888733255644396486980207921, 20611937834979950430546912394407436], ![267652310986953277644919984764805704, 27093863723182740387110520683067092, 18521193816849872350854768753074355]]]
  hmulB := by decide  
  f := ![![![1450449941501269843, -247519364096709278, 67905660964013576]], ![![1091095784678951936, -173426282271503071, 36871070878419900]], ![![-200392092922821117, 15517295042796838, 11406506280198003]]]
  g := ![![![-2550327263245607338010144458843413, 3877043357294461097847239409044522, 2650322308786816156536524059859696], ![-19834261981870277508896367913212108, 30152323888733255644396486980207921, 20611937834979950430546912394407436], ![-17822400461395220883939185234371939, 27093863723182740387110520683067092, 18521193816849872350854768753074355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![9143810260964, 925608107801, 632739846121]] ![![19504165493889638675644452375413, 1974364428153986844350891612660, 1349663031177242820243230030269]]
  ![![404987627360873952745498019525818004935072351, 40996020340080292856899722462370537594194830, 28024620120476181050781649838755398777166626]] where
 M := ![![![404987627360873952745498019525818004935072351, 40996020340080292856899722462370537594194830, 28024620120476181050781649838755398777166626]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![404987627360873952745498019525818004935072351, 40996020340080292856899722462370537594194830, 28024620120476181050781649838755398777166626]] ![![38300171026865230387921152521277053, 3877043357294461097847239409044522, 2650322308786816156536524059859696]]
  ![![131, 0, 0]] where
 M := ![![![35223267842577437399381772777432155532199580800240499528346801488339780596701527, 3565575112327265084219581042485601722093446030292406663829320995999719054731244, 2437404587203404783696997539938933295708519111405799627245909037576119656097406]]]
 hmul := by decide  
 g := ![![![![268879907195247613735738723491848515512973899238477095636235125865189164860317, 27218130628452405223050236965538944443461420078567989800223824396944420265124, 18606141887048891478603034656022391570294039018364882650732130057832974474026]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [129, 126, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 115, 117], [113, 21, 20], [0, 1]]
 g := ![![[74, 112, 88], [47, 99], [72, 112], [112, 122, 22], [], [20, 1], []], ![[112, 121, 114, 57], [111, 119], [8, 18], [51, 97, 6, 23], [119, 14], [79, 30], [112, 126]], ![[117, 63, 136, 92], [110, 18], [80, 107], [55, 2, 73, 55], [8, 14], [40, 73], [72, 126]]]
 h' := ![![[44, 115, 117], [130, 128, 122], [24, 81, 109], [74, 103, 48], [118, 76, 61], [23, 91], [0, 0, 1], [0, 1]], ![[113, 21, 20], [135, 22, 2], [53, 118, 121], [117, 133, 44], [32, 21, 35], [54, 53, 98], [92, 30, 21], [44, 115, 117]], ![[0, 1], [54, 124, 13], [74, 75, 44], [16, 38, 45], [66, 40, 41], [31, 130, 39], [56, 107, 115], [113, 21, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 22], []]
 b := ![[], [44, 126, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [129, 126, 117, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![160701, -6028, 3836]
  a := ![0, -4, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1173, -44, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB158I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB158I2 : PrimesBelowBoundCertificateInterval O 79 137 158 where
  m := 11
  g := ![1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB158I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
    · exact ![2571353]
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
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I97N1, I103N1, I109N1, I113N1, I131N0, I131N1, I131N2]
  Il := ![[], [I89N1], [I97N1], [], [I103N1], [], [I109N1], [I113N1], [], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
