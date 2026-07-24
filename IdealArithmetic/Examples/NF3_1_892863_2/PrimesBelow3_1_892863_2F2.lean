
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [8, 81, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 23, 17], [80, 59, 66], [0, 1]]
 g := ![![[64], [40, 17, 38], [21, 36], [58, 81], [42, 66, 1], []], ![[3, 7, 38, 28], [10, 20, 41, 41], [7, 59], [42, 37], [35, 51, 69, 81], [19, 40]], ![[29, 57, 1, 55], [29, 46, 29, 66], [64, 81], [68, 41], [0, 21, 41, 54], [53, 40]]]
 h' := ![![[69, 23, 17], [12, 8], [8, 49, 11], [50, 32, 6], [79, 54, 74], [0, 0, 1], [0, 1]], ![[80, 59, 66], [66, 18, 53], [55, 71, 71], [32, 77, 68], [6, 31, 55], [44, 70, 59], [69, 23, 17]], ![[0, 1], [71, 57, 30], [27, 46, 1], [37, 57, 9], [0, 81, 37], [0, 13, 23], [80, 59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 59], []]
 b := ![[], [24, 58, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [8, 81, 17, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1066301, 362876, -172972]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12847, 4372, -2084]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1274485, -56298, -39480]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-1274485, -56298, -39480]] 
 ![![89, 0, 0], ![0, 89, 0], ![32, 53, 1]] where
  M :=![![![-1274485, -56298, -39480], ![-5995116, -264823, -185712], ![-4914162, -217074, -152227]]]
  hmulB := by decide  
  f := ![![![403, -66, -24]], ![![-3708, 985, -240]], ![![-2150, 571, -139]]]
  g := ![![![-125, 22878, -39480], ![-588, 107617, -185712], ![-482, 88213, -152227]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [29, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 88], [0, 1]]
 g := ![![[50, 50], [4], [34], [36, 57], [41, 53], [1]], ![[85, 39], [4], [34], [67, 32], [87, 36], [1]]]
 h' := ![![[63, 88], [41, 36], [35, 2], [24, 37], [57, 18], [60, 63], [0, 1]], ![[0, 1], [84, 53], [72, 87], [41, 52], [34, 71], [24, 26], [63, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [88, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [29, 26, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2115, 1100, -525]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![165, 325, -525]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![403, -66, -24]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![403, -66, -24]] 
 ![![89, 0, 0], ![56, 1, 0], ![48, 0, 1]] where
  M :=![![![403, -66, -24], ![-3708, 985, -240], ![-7722, 726, 1117]]]
  hmulB := by decide  
  f := ![![![-1274485, -56298, -39480]], ![![-869284, -38399, -26928]], ![![-742578, -32802, -23003]]]
  g := ![![![59, -66, -24], ![-532, 985, -240], ![-1146, 726, 1117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-1274485, -56298, -39480]] ![![403, -66, -24]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [12, 47, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 30, 35], [25, 66, 62], [0, 1]]
 g := ![![[2], [49, 81], [12, 43], [71, 64], [4, 1], [1]], ![[8, 87, 21, 2], [46, 35], [67, 24], [20, 8], [7, 50], [92, 7, 59, 1]], ![[95, 53, 1, 95], [60, 85], [77, 2], [75, 35], [68, 94], [96, 87, 49, 96]]]
 h' := ![![[73, 30, 35], [67, 14], [49, 88, 88], [22, 53, 72], [96, 55, 8], [85, 50, 1], [0, 1]], ![[25, 66, 62], [22, 32, 5], [34, 47, 61], [16, 24, 11], [16, 21, 28], [10, 96, 70], [73, 30, 35]], ![[0, 1], [29, 51, 92], [19, 59, 45], [78, 20, 14], [69, 21, 61], [20, 48, 26], [25, 66, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 55], []]
 b := ![[], [80, 50, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [12, 47, 96, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36569894340, 11780938672, -5277477448]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-377009220, 121452976, -54406984]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [15, 85, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 73, 87], [26, 27, 14], [0, 1]]
 g := ![![[31, 37, 25], [61, 33], [88, 16, 70], [56, 80], [41, 13], [1]], ![[87, 71, 56, 47], [100, 58], [26, 72, 37, 21], [9, 19], [36, 31], [68, 32, 89, 84]], ![[33, 91, 70, 31], [87, 100], [73, 4, 8, 96], [62, 88], [59, 64], [54, 82, 30, 17]]]
 h' := ![![[40, 73, 87], [43, 71, 5], [94, 87, 72], [63, 73, 75], [14, 82, 79], [86, 16, 66], [0, 1]], ![[26, 27, 14], [64, 21, 50], [7, 72, 19], [88, 13, 94], [83, 35, 76], [57, 33, 43], [40, 73, 87]], ![[0, 1], [85, 9, 46], [73, 43, 10], [50, 15, 33], [24, 85, 47], [0, 52, 93], [26, 27, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 94], []]
 b := ![[], [6, 24, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [15, 85, 35, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2539342, 757601, -266337]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25142, 7501, -2637]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![19, -20, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![19, -20, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![19, 83, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![19, -20, 1], ![109, -28, -81], ![-3068, 584, 12]]]
  hmulB := by decide  
  f := ![![![-18, 20, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -83, 103]], ![![0, -1, 1], ![16, 65, -81], ![-32, -4, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [46, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 102], [0, 1]]
 g := ![![[4, 56], [22, 8], [30, 79], [32], [58], [22, 1]], ![[0, 47], [95, 95], [17, 24], [32], [58], [44, 102]]]
 h' := ![![[22, 102], [18, 46], [62, 27], [80, 64], [25, 49], [18, 26], [0, 1]], ![[0, 1], [0, 57], [38, 76], [46, 39], [73, 54], [75, 77], [22, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [9, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [46, 81, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![228, 790, -1430]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![266, 1160, -1430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-22, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-22, 1, 0]] 
 ![![103, 0, 0], ![81, 1, 0], ![91, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-22, 1, 0], ![2, -21, 4], ![149, -27, -23]]]
  hmulB := by decide  
  f := ![![![-2141, 24101, -4592], ![721, 118244, 0]], ![![-1671, 18936, -3608], ![619, 92906, 0]], ![![-1889, 21293, -4057], ![649, 104468, 0]]]
  g := ![![![1, 0, 0], ![-81, 103, 0], ![-91, 0, 103]], ![![-1, 1, 0], ![13, -21, 4], ![43, -27, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![19, -20, 1]] ![![103, 0, 0], ![-22, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2266, 103, 0]], ![![1957, -2060, 103], ![-309, 412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-22, 1, 0]]], ![![![19, -20, 1]], ![![-3, 4, -1]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [73, 88, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 5, 63], [63, 101, 44], [0, 1]]
 g := ![![[42, 48, 92], [25, 12, 11], [1, 81], [79, 98, 39], [33, 49], [1]], ![[20, 68, 42, 74], [73, 100, 94, 104], [66, 64], [93, 17, 102, 63], [77, 99], [86, 10, 20, 95]], ![[85, 36, 16, 52], [86, 27, 43, 102], [50, 75], [45, 83, 64, 35], [78, 29], [101, 51, 57, 12]]]
 h' := ![![[37, 5, 63], [101, 84, 78], [48, 22, 92], [11, 16, 98], [31, 54, 50], [34, 19, 100], [0, 1]], ![[63, 101, 44], [62, 81, 9], [105, 97, 85], [106, 8, 99], [94, 28, 106], [77, 39, 62], [37, 5, 63]], ![[0, 1], [25, 49, 20], [30, 95, 37], [91, 83, 17], [88, 25, 58], [105, 49, 52], [63, 101, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 3], []]
 b := ![[], [27, 44, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [73, 88, 7, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![313317507, -118257042, 69854094]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2928201, -1105206, 652842]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-28, -46, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-28, -46, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![81, 63, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-28, -46, 1], ![57, -101, -185], ![-6942, 1286, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -63, 109]], ![![-1, -1, 1], ![138, 106, -185], ![-57, 17, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [80, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 108], [0, 1]]
 g := ![![[68, 15], [88], [50, 28], [3, 60], [73], [10, 1]], ![[0, 94], [88], [3, 81], [58, 49], [73], [20, 108]]]
 h' := ![![[10, 108], [44, 61], [33, 52], [87, 30], [107, 13], [72, 20], [0, 1]], ![[0, 1], [0, 48], [8, 57], [60, 79], [19, 96], [54, 89], [10, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [104, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [80, 99, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-402, 196, -118]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 70, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-33, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-33, 1, 0]] 
 ![![109, 0, 0], ![76, 1, 0], ![9, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-33, 1, 0], ![2, -32, 4], ![149, -27, -34]]]
  hmulB := by decide  
  f := ![![![-5708, 104519, -13068], ![2725, 356103, 0]], ![![-3959, 72846, -9108], ![1963, 248193, 0]], ![![-471, 8630, -1079], ![226, 29403, 0]]]
  g := ![![![1, 0, 0], ![-76, 109, 0], ![-9, 0, 109]], ![![-1, 1, 0], ![22, -32, 4], ![23, -27, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-28, -46, 1]] ![![109, 0, 0], ![-33, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3597, 109, 0]], ![![-3052, -5014, 109], ![981, 1417, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-33, 1, 0]]], ![![![-28, -46, 1]], ![![9, 13, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-51, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-51, 1, 0]] 
 ![![113, 0, 0], ![62, 1, 0], ![41, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-51, 1, 0], ![2, -50, 4], ![149, -27, -52]]]
  hmulB := by decide  
  f := ![![![-5158, 173565, -13888], ![3955, 392336, 0]], ![![-2838, 95181, -7616], ![2148, 215152, 0]], ![![-1876, 62975, -5039], ![1425, 142352, 0]]]
  g := ![![![1, 0, 0], ![-62, 113, 0], ![-41, 0, 113]], ![![-1, 1, 0], ![26, -50, 4], ![35, -27, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-48, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-48, 1, 0]] 
 ![![113, 0, 0], ![65, 1, 0], ![58, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-48, 1, 0], ![2, -47, 4], ![149, -27, -49]]]
  hmulB := by decide  
  f := ![![![497, -15037, 1280], ![-339, -36160, 0]], ![![321, -8647, 736], ![-112, -20792, 0]], ![![298, -7719, 657], ![-73, -18560, 0]]]
  g := ![![![1, 0, 0], ![-65, 113, 0], ![-58, 0, 113]], ![![-1, 1, 0], ![25, -47, 4], ![42, -27, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-14, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-14, 1, 0]] 
 ![![113, 0, 0], ![99, 1, 0], ![68, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-14, 1, 0], ![2, -13, 4], ![149, -27, -15]]]
  hmulB := by decide  
  f := ![![![-609, 4055, -1248], ![113, 35256, 0]], ![![-531, 3548, -1092], ![114, 30849, 0]], ![![-364, 2440, -751], ![88, 21216, 0]]]
  g := ![![![1, 0, 0], ![-99, 113, 0], ![-68, 0, 113]], ![![-1, 1, 0], ![9, -13, 4], ![34, -27, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-51, 1, 0]] ![![113, 0, 0], ![-48, 1, 0]]
  ![![113, 0, 0], ![-9, 32, 1]] where
 M := ![![![12769, 0, 0], ![-5424, 113, 0]], ![![-5763, 113, 0], ![2450, -98, 4]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![-39, -31, -1], ![113, 0, 0]]], ![![![-42, -31, -1], ![113, 0, 0]], ![![22, -2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-9, 32, 1]] ![![113, 0, 0], ![-14, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1582, 113, 0]], ![![-1017, 3616, 113], ![339, -452, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-14, 1, 0]]], ![![![-9, 32, 1]], ![![3, -4, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [105, 15, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52, 124], [70, 74, 3], [0, 1]]
 g := ![![[48, 15, 98], [15, 80, 19], [30, 89, 113], [18, 91, 11], [16, 42, 35], [1]], ![[109, 102, 112, 49], [70, 121, 87, 16], [0, 87, 115, 9], [119, 110, 98, 11], [66, 109, 111, 32], [108, 88, 85, 100]], ![[53, 86, 105, 53], [88, 10, 88, 24], [90, 5, 13, 27], [76, 11, 49, 118], [52, 48, 79, 101], [13, 95, 15, 27]]]
 h' := ![![[40, 52, 124], [76, 1, 15], [25, 82, 107], [15, 33, 42], [98, 25, 97], [22, 112, 110], [0, 1]], ![[70, 74, 3], [79, 121, 91], [10, 108, 52], [63, 55, 88], [29, 19, 118], [82, 107, 57], [40, 52, 124]], ![[0, 1], [4, 5, 21], [70, 64, 95], [124, 39, 124], [100, 83, 39], [5, 35, 87], [70, 74, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 98], []]
 b := ![[], [19, 85, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [105, 15, 17, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5357622, -1632077, 666242]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42186, -12851, 5246]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [88, 85, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 73, 101], [11, 57, 30], [0, 1]]
 g := ![![[91, 15, 60], [44, 24, 7], [70, 102], [53, 35], [44, 43], [125, 1], []], ![[67, 56, 83, 20], [27, 28, 33, 112], [41, 27], [6, 100], [105, 25], [68, 105], [45, 114]], ![[79, 71, 20, 87], [17, 20, 61, 8], [126, 74], [77, 34], [94, 102], [105, 89], [116, 114]]]
 h' := ![![[114, 73, 101], [58, 105, 86], [18, 18, 111], [26, 106, 44], [74, 44, 67], [4, 29, 82], [0, 0, 1], [0, 1]], ![[11, 57, 30], [111, 19, 49], [34, 70, 23], [57, 21, 114], [42, 122, 10], [51, 91, 5], [128, 36, 57], [114, 73, 101]], ![[0, 1], [34, 7, 127], [85, 43, 128], [13, 4, 104], [34, 96, 54], [61, 11, 44], [0, 95, 73], [11, 57, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 27], []]
 b := ![[], [60, 18, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [88, 85, 6, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16774812, 5410300, -2436600]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128052, 41300, -18600]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![45, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![45, 1, 0]] 
 ![![137, 0, 0], ![45, 1, 0], ![31, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![45, 1, 0], ![2, 46, 4], ![149, -27, 44]]]
  hmulB := by decide  
  f := ![![![-14096, -379033, -32964], ![-7261, 1129017, 0]], ![![-4647, -124459, -10824], ![-2328, 370722, 0]], ![![-3208, -85767, -7459], ![-1587, 255471, 0]]]
  g := ![![![1, 0, 0], ![-45, 137, 0], ![-31, 0, 137]], ![![0, 1, 0], ![-16, 46, 4], ![0, -27, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-27, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-27, 1, 0]] 
 ![![137, 0, 0], ![110, 1, 0], ![99, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-27, 1, 0], ![2, -26, 4], ![149, -27, -28]]]
  hmulB := by decide  
  f := ![![![7122, -97823, 15052], ![-2055, -515531, 0]], ![![5719, -78534, 12084], ![-1643, -413877, 0]], ![![5157, -70690, 10877], ![-1432, -372537, 0]]]
  g := ![![![1, 0, 0], ![-110, 137, 0], ![-99, 0, 137]], ![![-1, 1, 0], ![18, -26, 4], ![43, -27, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-18, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-18, 1, 0]] 
 ![![137, 0, 0], ![119, 1, 0], ![61, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-18, 1, 0], ![2, -17, 4], ![149, -27, -19]]]
  hmulB := by decide  
  f := ![![![-2073, 18085, -4256], ![411, 145768, 0]], ![![-1793, 15705, -3696], ![412, 126588, 0]], ![![-915, 8052, -1895], ![244, 64904, 0]]]
  g := ![![![1, 0, 0], ![-119, 137, 0], ![-61, 0, 137]], ![![-1, 1, 0], ![13, -17, 4], ![33, -27, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![45, 1, 0]] ![![137, 0, 0], ![-27, 1, 0]]
  ![![137, 0, 0], ![5, 39, 1]] where
 M := ![![![18769, 0, 0], ![-3699, 137, 0]], ![![6165, 137, 0], ![-1213, 19, 4]]]
 hmul := by decide  
 g := ![![![![132, -39, -1], ![137, 0, 0]], ![![-27, 1, 0], ![0, 0, 0]]], ![![![40, -38, -1], ![137, 0, 0]], ![![-9, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![5, 39, 1]] ![![137, 0, 0], ![-18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2466, 137, 0]], ![![685, 5343, 137], ![137, -685, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-18, 1, 0]]], ![![![5, 39, 1]], ![![1, -5, 1]]]]
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


lemma PB268I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB268I2 : PrimesBelowBoundCertificateInterval O 79 137 268 where
  m := 11
  g := ![1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB268I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![137, 137, 137]
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I89N1, I103N1, I109N1, I113N0, I113N1, I113N2, I137N0, I137N1, I137N2]
  Il := ![[], [I89N1], [], [], [I103N1], [], [I109N1], [I113N0, I113N1, I113N2], [], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
