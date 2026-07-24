
import IdealArithmetic.Examples.NF3_1_251451_1.RI3_1_251451_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-14, 38, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-14, 38, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![69, 38, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-14, 38, 1], ![49, -50, 38], ![1862, -1319, -50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -38, 83]], ![![-1, 0, 1], ![-31, -18, 38], ![64, 7, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [50, 23, 1] where
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
 g := ![![[32, 59], [24, 59], [78], [65], [10, 31], [1]], ![[3, 24], [78, 24], [78], [65], [44, 52], [1]]]
 h' := ![![[60, 82], [45, 68], [82, 15], [74, 24], [81, 56], [33, 60], [0, 1]], ![[0, 1], [58, 15], [69, 68], [20, 59], [38, 27], [64, 23], [60, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [63, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [50, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148, -46, -58]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 26, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-38, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-38, 1, 0]] 
 ![![83, 0, 0], ![45, 1, 0], ![50, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-38, 1, 0], ![0, -38, 1], ![49, -36, -38]]]
  hmulB := by decide  
  f := ![![![2775, -73, 0], ![6059, 0, 0]], ![![1521, -40, 0], ![3321, 0, 0]], ![![1690, -44, 0], ![3690, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 83, 0], ![-50, 0, 83]], ![![-1, 1, 0], ![20, -38, 1], ![43, -36, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-14, 38, 1]] ![![83, 0, 0], ![-38, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3154, 83, 0]], ![![-1162, 3154, 83], ![581, -1494, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-38, 1, 0]]], ![![![-14, 38, 1]], ![![7, -18, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 21, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 21, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![32, 21, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 21, 1], ![49, -4, 21], ![1029, -707, -4]]]
  hmulB := by decide  
  f := ![![![-31, -21, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -21, 89]], ![![0, 0, 1], ![-7, -5, 21], ![13, -7, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [11, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 88], [0, 1]]
 g := ![![[23, 81], [50], [47], [65, 40], [33, 18], [1]], ![[0, 8], [50], [47], [2, 49], [18, 71], [1]]]
 h' := ![![[14, 88], [37, 80], [26, 36], [86, 74], [82, 29], [78, 14], [0, 1]], ![[0, 1], [0, 9], [85, 53], [54, 15], [43, 60], [7, 75], [14, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [20, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [11, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-651, 727, -101]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 32, -101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-21, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-21, 1, 0]] 
 ![![89, 0, 0], ![68, 1, 0], ![4, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-21, 1, 0], ![0, -21, 1], ![49, -36, -21]]]
  hmulB := by decide  
  f := ![![![526, -25, 0], ![2225, 0, 0]], ![![400, -19, 0], ![1692, 0, 0]], ![![26, -1, 0], ![110, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 89, 0], ![-4, 0, 89]], ![![-1, 1, 0], ![16, -21, 1], ![29, -36, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![32, 21, 1]] ![![89, 0, 0], ![-21, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1869, 89, 0]], ![![2848, 1869, 89], ![-623, -445, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-21, 1, 0]]], ![![![32, 21, 1]], ![![-7, -5, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [8, 89, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 25, 11], [13, 71, 86], [0, 1]]
 g := ![![[53, 65, 88], [63, 25], [50, 73], [33, 65], [75, 44], [1]], ![[95, 62, 91, 44], [73, 73], [24, 36], [16, 62], [95, 49], [14, 61, 93, 70]], ![[40, 31, 78, 61], [69, 93], [54, 6], [62, 72], [70, 62], [46, 2, 29, 27]]]
 h' := ![![[61, 25, 11], [86, 68, 66], [69, 25, 5], [9, 17, 48], [46, 23, 29], [89, 8, 74], [0, 1]], ![[13, 71, 86], [34, 25, 2], [6, 91, 48], [2, 71, 6], [18, 58, 81], [83, 18, 7], [61, 25, 11]], ![[0, 1], [12, 4, 29], [51, 78, 44], [80, 9, 43], [24, 16, 84], [83, 71, 16], [13, 71, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 59], []]
 b := ![[], [30, 92, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [8, 89, 23, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164706, -3783, -4559]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1698, -39, -47]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-18, -42, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-18, -42, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![83, 59, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-18, -42, 1], ![49, -54, -42], ![-2058, 1561, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -59, 101]], ![![-1, -1, 1], ![35, 24, -42], ![24, 47, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [11, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 100], [0, 1]]
 g := ![![[37, 43], [19], [86, 77], [31], [4], [98, 1]], ![[9, 58], [19], [57, 24], [31], [4], [95, 100]]]
 h' := ![![[98, 100], [49, 12], [64, 25], [76, 28], [35, 58], [33, 99], [0, 1]], ![[0, 1], [13, 89], [90, 76], [93, 73], [63, 43], [39, 2], [98, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [78, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [11, 3, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-279, 662, -338]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![275, 204, -338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![42, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![42, 1, 0]] 
 ![![101, 0, 0], ![42, 1, 0], ![54, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![42, 1, 0], ![0, 42, 1], ![49, -36, 42]]]
  hmulB := by decide  
  f := ![![![1387, 33, 0], ![-3333, 0, 0]], ![![546, 13, 0], ![-1312, 0, 0]], ![![690, 16, 0], ![-1658, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 101, 0], ![-54, 0, 101]], ![![0, 1, 0], ![-18, 42, 1], ![-7, -36, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-18, -42, 1]] ![![101, 0, 0], ![42, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4242, 101, 0]], ![![-1818, -4242, 101], ![-707, -1818, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![42, 1, 0]]], ![![![-18, -42, 1]], ![![-7, -18, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-354, 414, -109]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-354, 414, -109]] 
 ![![103, 0, 0], ![0, 103, 0], ![59, 34, 1]] where
  M :=![![![-354, 414, -109], ![-5341, 3570, 414], ![20286, -20245, 3570]]]
  hmulB := by decide  
  f := ![![![-205110, -7075, -5442]], ![![-266658, -9198, -7075]], ![![-208879, -7205, -5542]]]
  g := ![![![59, 40, -109], ![-289, -102, 414], ![-1848, -1375, 3570]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [92, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 102], [0, 1]]
 g := ![![[96, 28], [62, 61], [65, 49], [1], [23], [26, 1]], ![[0, 75], [0, 42], [0, 54], [1], [23], [52, 102]]]
 h' := ![![[26, 102], [64, 53], [97, 24], [24, 7], [61, 102], [80, 69], [0, 1]], ![[0, 1], [0, 50], [0, 79], [0, 96], [35, 1], [20, 34], [26, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [77, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [92, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![190, -100, -112]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 36, -112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205110, 7075, 5442]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![205110, 7075, 5442]] 
 ![![103, 0, 0], ![69, 1, 0], ![80, 0, 1]] where
  M :=![![![205110, 7075, 5442], ![266658, 9198, 7075], ![346675, 11958, 9198]]]
  hmulB := by decide  
  f := ![![![354, -414, 109]], ![![289, -312, 69]], ![![78, -125, 50]]]
  g := ![![![-6975, 7075, 5442], ![-9068, 9198, 7075], ![-11789, 11958, 9198]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-354, 414, -109]] ![![205110, 7075, 5442]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-19, -42, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-19, -42, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![88, 65, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-19, -42, 1], ![49, -55, -42], ![-2058, 1561, -55]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -65, 107]], ![![-1, -1, 1], ![35, 25, -42], ![26, 48, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [94, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 106], [0, 1]]
 g := ![![[52, 12], [33, 35], [16], [42, 34], [64], [34, 1]], ![[32, 95], [46, 72], [16], [21, 73], [64], [68, 106]]]
 h' := ![![[34, 106], [1, 36], [8, 28], [11, 103], [65, 26], [14, 99], [0, 1]], ![[0, 1], [48, 71], [104, 79], [89, 4], [93, 81], [63, 8], [34, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [8, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [94, 73, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2030, 106, 400]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-310, -242, 400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![42, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![42, 1, 0]] 
 ![![107, 0, 0], ![42, 1, 0], ![55, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![42, 1, 0], ![0, 42, 1], ![49, -36, 42]]]
  hmulB := by decide  
  f := ![![![1639, 39, 0], ![-4173, 0, 0]], ![![630, 15, 0], ![-1604, 0, 0]], ![![815, 19, 0], ![-2075, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 107, 0], ![-55, 0, 107]], ![![0, 1, 0], ![-17, 42, 1], ![-7, -36, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-19, -42, 1]] ![![107, 0, 0], ![42, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4494, 107, 0]], ![![-2033, -4494, 107], ![-749, -1819, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![42, 1, 0]]], ![![![-19, -42, 1]], ![![-7, -17, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![31, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![31, 1, 0]] 
 ![![109, 0, 0], ![31, 1, 0], ![20, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![31, 1, 0], ![0, 31, 1], ![49, -36, 31]]]
  hmulB := by decide  
  f := ![![![1551, 50, 0], ![-5450, 0, 0]], ![![403, 13, 0], ![-1416, 0, 0]], ![![288, 9, 0], ![-1012, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 109, 0], ![-20, 0, 109]], ![![0, 1, 0], ![-9, 31, 1], ![5, -36, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-18, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-18, 1, 0]] 
 ![![109, 0, 0], ![91, 1, 0], ![3, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-18, 1, 0], ![0, -18, 1], ![49, -36, -18]]]
  hmulB := by decide  
  f := ![![![1891, -105, 0], ![11445, 0, 0]], ![![1585, -88, 0], ![9593, 0, 0]], ![![57, -3, 0], ![345, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 109, 0], ![-3, 0, 109]], ![![-1, 1, 0], ![15, -18, 1], ![31, -36, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-13, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-13, 1, 0]] 
 ![![109, 0, 0], ![96, 1, 0], ![49, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-13, 1, 0], ![0, -13, 1], ![49, -36, -13]]]
  hmulB := by decide  
  f := ![![![651, -50, 0], ![5450, 0, 0]], ![![560, -43, 0], ![4688, 0, 0]], ![![301, -23, 0], ![2520, 1, 0]]]
  g := ![![![1, 0, 0], ![-96, 109, 0], ![-49, 0, 109]], ![![-1, 1, 0], ![11, -13, 1], ![38, -36, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![31, 1, 0]] ![![109, 0, 0], ![-18, 1, 0]]
  ![![109, 0, 0], ![-13, 13, 1]] where
 M := ![![![11881, 0, 0], ![-1962, 109, 0]], ![![3379, 109, 0], ![-558, 13, 1]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![-5, -12, -1], ![109, 0, 0]]], ![![![31, 1, 0], ![0, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-13, 13, 1]] ![![109, 0, 0], ![-13, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1417, 109, 0]], ![![-1417, 1417, 109], ![218, -218, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-13, 1, 0]]], ![![![-13, 13, 1]], ![![2, -2, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [36, 112, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 41, 81], [92, 71, 32], [0, 1]]
 g := ![![[54, 86, 31], [84, 50], [81, 88], [102, 56], [49, 43, 15], [1]], ![[100, 105, 6, 83], [19, 95], [62, 57], [109, 53], [104, 34, 39, 99], [109, 73, 95, 2]], ![[43, 10, 67, 91], [48, 36], [105, 49], [99, 77], [104, 28, 62, 1], [48, 98, 110, 111]]]
 h' := ![![[90, 41, 81], [91, 62, 101], [8, 97, 84], [72, 110, 38], [44, 23, 100], [77, 1, 69], [0, 1]], ![[92, 71, 32], [107, 102, 102], [0, 39, 35], [57, 108, 82], [79, 70, 36], [68, 59, 8], [90, 41, 81]], ![[0, 1], [81, 62, 23], [1, 90, 107], [74, 8, 106], [19, 20, 90], [85, 53, 36], [92, 71, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 82], []]
 b := ![[], [56, 54, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [36, 112, 44, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29041, 23843, -1017]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257, 211, -9]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [103, 100, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 75, 66], [40, 51, 61], [0, 1]]
 g := ![![[77, 80, 8], [115, 120, 36], [112, 16, 47], [55, 66, 71], [36, 11, 35], [1]], ![[1, 37, 97, 46], [123, 108, 42, 109], [39, 24, 102, 28], [107, 13, 49, 33], [97, 87, 48, 39], [37, 52, 77, 95]], ![[10, 12, 29, 100], [32, 16, 81, 16], [110, 36, 99, 16], [91, 66, 118, 49], [107, 77, 99, 115], [6, 22, 63, 32]]]
 h' := ![![[70, 75, 66], [93, 76, 95], [21, 66, 121], [50, 11, 89], [102, 34, 43], [24, 27, 110], [0, 1]], ![[40, 51, 61], [99, 9, 82], [41, 65, 113], [50, 28, 58], [58, 73, 119], [99, 101, 26], [70, 75, 66]], ![[0, 1], [11, 42, 77], [123, 123, 20], [37, 88, 107], [93, 20, 92], [9, 126, 118], [40, 51, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 59], []]
 b := ![[], [118, 67, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [103, 100, 17, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1524, -11430, 8509]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, -90, 67]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 20, 16]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![601, 20, 16]] 
 ![![131, 0, 0], ![0, 131, 0], ![13, 34, 1]] where
  M :=![![![601, 20, 16], ![784, 25, 20], ![980, 64, 25]]]
  hmulB := by decide  
  f := ![![![-5, 4, 0]], ![![0, -5, 4]], ![![1, -2, 1]]]
  g := ![![![3, -4, 16], ![4, -5, 20], ![5, -6, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [38, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 130], [0, 1]]
 g := ![![[28, 100], [18, 33], [48], [105], [4], [125], [1]], ![[0, 31], [14, 98], [48], [105], [4], [125], [1]]]
 h' := ![![[115, 130], [102, 121], [22, 66], [76, 21], [23, 74], [100, 2], [93, 115], [0, 1]], ![[0, 1], [0, 10], [14, 65], [2, 110], [18, 57], [68, 129], [87, 16], [115, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [20, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [38, 16, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1886, 1436, -4]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 12, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -4, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![5, -4, 0]] 
 ![![131, 0, 0], ![97, 1, 0], ![23, 0, 1]] where
  M :=![![![5, -4, 0], ![0, 5, -4], ![-196, 144, 5]]]
  hmulB := by decide  
  f := ![![![-601, -20, -16]], ![![-451, -15, -12]], ![![-113, -4, -3]]]
  g := ![![![3, -4, 0], ![-3, 5, -4], ![-109, 144, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![601, 20, 16]] ![![5, -4, 0]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![29, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![29, 1, 0]] 
 ![![137, 0, 0], ![29, 1, 0], ![118, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![29, 1, 0], ![0, 29, 1], ![49, -36, 29]]]
  hmulB := by decide  
  f := ![![![1219, 42, 0], ![-5754, 0, 0]], ![![261, 9, 0], ![-1232, 0, 0]], ![![1080, 37, 0], ![-5098, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 137, 0], ![-118, 0, 137]], ![![0, 1, 0], ![-7, 29, 1], ![-17, -36, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![43, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![43, 1, 0]] 
 ![![137, 0, 0], ![43, 1, 0], ![69, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![43, 1, 0], ![0, 43, 1], ![49, -36, 43]]]
  hmulB := by decide  
  f := ![![![1678, 39, 0], ![-5343, 0, 0]], ![![516, 12, 0], ![-1643, 0, 0]], ![![788, 18, 0], ![-2509, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 137, 0], ![-69, 0, 137]], ![![0, 1, 0], ![-14, 43, 1], ![-10, -36, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![65, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![65, 1, 0]] 
 ![![137, 0, 0], ![65, 1, 0], ![22, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![65, 1, 0], ![0, 65, 1], ![49, -36, 65]]]
  hmulB := by decide  
  f := ![![![2731, 42, 0], ![-5754, 0, 0]], ![![1235, 19, 0], ![-2602, 0, 0]], ![![356, 5, 0], ![-750, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 137, 0], ![-22, 0, 137]], ![![0, 1, 0], ![-31, 65, 1], ![7, -36, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![29, 1, 0]] ![![137, 0, 0], ![43, 1, 0]]
  ![![137, 0, 0], ![14, -65, 1]] where
 M := ![![![18769, 0, 0], ![5891, 137, 0]], ![![3973, 137, 0], ![1247, 72, 1]]]
 hmul := by decide  
 g := ![![![![123, 65, -1], ![137, 0, 0]], ![![29, 66, -1], ![137, 0, 0]]], ![![![15, 66, -1], ![137, 0, 0]], ![![9, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![14, -65, 1]] ![![137, 0, 0], ![65, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8905, 137, 0]], ![![1918, -8905, 137], ![959, -4247, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![65, 1, 0]]], ![![![14, -65, 1]], ![![7, -31, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB142I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB142I2 : PrimesBelowBoundCertificateInterval O 79 137 142 where
  m := 11
  g := ![2, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB142I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
      exact NI137N2
  β := ![I83N1, I89N1, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [], [], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
