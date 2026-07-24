
import IdealArithmetic.Examples.NF3_3_600925_1.RI3_3_600925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![16, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![16, 1, 0]] 
 ![![139, 0, 0], ![16, 1, 0], ![59, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![16, 1, 0], ![0, 15, 3], ![146, 47, 18]]]
  hmulB := by decide  
  f := ![![![1521, 95, 0], ![-13205, 0, 0]], ![![144, 9, 0], ![-1250, 0, 0]], ![![641, 30, -2], ![-5565, 93, 0]]]
  g := ![![![1, 0, 0], ![-16, 139, 0], ![-59, 0, 139]], ![![0, 1, 0], ![-3, 15, 3], ![-12, 47, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![45, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![45, 1, 0]] 
 ![![139, 0, 0], ![45, 1, 0], ![35, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![45, 1, 0], ![0, 44, 3], ![146, 47, 47]]]
  hmulB := by decide  
  f := ![![![991, 22, 0], ![-3058, 0, 0]], ![![315, 7, 0], ![-972, 0, 0]], ![![245, -24, -2], ![-756, 93, 0]]]
  g := ![![![1, 0, 0], ![-45, 139, 0], ![-35, 0, 139]], ![![0, 1, 0], ![-15, 44, 3], ![-26, 47, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-62, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-62, 1, 0]] 
 ![![139, 0, 0], ![77, 1, 0], ![88, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-62, 1, 0], ![0, -63, 3], ![146, 47, -60]]]
  hmulB := by decide  
  f := ![![![6077, -98, 0], ![13622, 0, 0]], ![![3411, -55, 0], ![7646, 0, 0]], ![![3916, -21, -2], ![8778, 93, 0]]]
  g := ![![![1, 0, 0], ![-77, 139, 0], ![-88, 0, 139]], ![![-1, 1, 0], ![33, -63, 3], ![13, 47, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![16, 1, 0]] ![![139, 0, 0], ![45, 1, 0]]
  ![![139, 0, 0], ![-38, 20, 1]] where
 M := ![![![19321, 0, 0], ![6255, 139, 0]], ![![2224, 139, 0], ![720, 60, 3]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![45, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-38, 20, 1]] ![![139, 0, 0], ![-62, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8618, 139, 0]], ![![-5282, 2780, 139], ![2502, -1251, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-62, 1, 0]]], ![![![-38, 20, 1]], ![![18, -9, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-98, 11, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-98, 11, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![51, 11, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-98, 11, 1], ![146, -62, 35], ![1752, 597, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -11, 149]], ![![-1, 0, 1], ![-11, -3, 35], ![21, 6, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [134, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 148], [0, 1]]
 g := ![![[104, 49], [121], [75, 45], [24], [123, 107], [132], [1]], ![[107, 100], [121], [96, 104], [24], [14, 42], [132], [1]]]
 h' := ![![[70, 148], [46, 142], [82, 11], [33, 55], [57, 89], [119, 16], [15, 70], [0, 1]], ![[0, 1], [3, 7], [107, 138], [9, 94], [29, 60], [47, 133], [147, 79], [70, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [64, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [134, 79, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1302, 982, 455]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-147, -27, 455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-35, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-35, 1, 0]] 
 ![![149, 0, 0], ![114, 1, 0], ![27, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-35, 1, 0], ![0, -36, 3], ![146, 47, -33]]]
  hmulB := by decide  
  f := ![![![4691, -134, 0], ![19966, 0, 0]], ![![3606, -103, 0], ![15348, 0, 0]], ![![913, -14, -1], ![3886, 50, 0]]]
  g := ![![![1, 0, 0], ![-114, 149, 0], ![-27, 0, 149]], ![![-1, 1, 0], ![27, -36, 3], ![-29, 47, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-98, 11, 1]] ![![149, 0, 0], ![-35, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-5215, 149, 0]], ![![-14602, 1639, 149], ![3576, -447, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-35, 1, 0]]], ![![![-98, 11, 1]], ![![24, -3, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-547, -201, -51]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-547, -201, -51]] 
 ![![151, 0, 0], ![0, 151, 0], ![141, 75, 1]] where
  M :=![![![-547, -201, -51], ![-7446, -2743, -705], ![-36792, -13527, -3448]]]
  hmulB := by decide  
  f := ![![![521, 21, -12]], ![![-1752, -64, 39]], ![![-375, -12, 8]]]
  g := ![![![44, 24, -51], ![609, 332, -705], ![2976, 1623, -3448]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [52, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 150], [0, 1]]
 g := ![![[136, 128], [121, 32], [35, 124], [139], [77, 11], [21], [1]], ![[14, 23], [15, 119], [115, 27], [139], [50, 140], [21], [1]]]
 h' := ![![[25, 150], [50, 66], [143, 33], [64, 107], [73, 130], [102, 39], [99, 25], [0, 1]], ![[0, 1], [39, 85], [62, 118], [21, 44], [1, 21], [20, 112], [120, 126], [25, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [79, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [52, 126, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![949, 1565, 3212]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2993, -1585, 3212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, 21, -12]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![521, 21, -12]] 
 ![![151, 0, 0], ![75, 1, 0], ![113, 0, 1]] where
  M :=![![![521, 21, -12], ![-1752, -64, 39], ![1314, 27, -25]]]
  hmulB := by decide  
  f := ![![![-547, -201, -51]], ![![-321, -118, -30]], ![![-653, -240, -61]]]
  g := ![![![2, 21, -12], ![-9, -64, 39], ![14, 27, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-547, -201, -51]] ![![521, 21, -12]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [101, 56, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 45, 122], [154, 111, 35], [0, 1]]
 g := ![![[139, 24, 51], [40, 86], [155, 9, 1], [113, 24, 113], [79, 52, 25], [88, 1], []], ![[49, 65, 69, 153], [107, 68], [44, 87, 148, 17], [14, 114, 59, 75], [65, 30, 18, 144], [129, 75], [88, 126]], ![[30, 113, 153, 154], [58, 126], [41, 75, 108, 1], [63, 106, 42, 64], [111, 128, 13, 124], [40, 141], [18, 126]]]
 h' := ![![[91, 45, 122], [26, 46, 88], [45, 94, 137], [48, 39, 1], [28, 11, 120], [61, 152, 152], [0, 0, 1], [0, 1]], ![[154, 111, 35], [94, 82, 151], [15, 86, 142], [7, 141, 2], [95, 82, 61], [129, 152, 91], [21, 113, 111], [91, 45, 122]], ![[0, 1], [51, 29, 75], [147, 134, 35], [6, 134, 154], [46, 64, 133], [15, 10, 71], [75, 44, 45], [154, 111, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 136], []]
 b := ![[], [21, 56, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [101, 56, 69, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49141, -46629, -48984]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-313, -297, -312]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![38, -48, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![38, -48, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![38, 115, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![38, -48, 1], ![146, 133, -142], ![-6862, -2176, -9]]]
  hmulB := by decide  
  f := ![![![-37, 48, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -115, 163]], ![![0, -1, 1], ![34, 101, -142], ![-40, -7, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [103, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 162], [0, 1]]
 g := ![![[110, 144], [], [], [46], [33], [0, 43], [1]], ![[57, 19], [], [], [46], [33], [17, 120], [1]]]
 h' := ![![[80, 162], [0, 151], [71], [76], [24, 32], [0, 149], [60, 80], [0, 1]], ![[0, 1], [18, 12], [71], [76], [139, 131], [21, 14], [103, 83], [80, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [55, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [103, 83, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2523, 3110, 2387]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-541, -1665, 2387]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-21, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-21, 1, 0]] 
 ![![163, 0, 0], ![142, 1, 0], ![9, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-21, 1, 0], ![0, -22, 3], ![146, 47, -19]]]
  hmulB := by decide  
  f := ![![![2941, -140, 0], ![22820, 0, 0]], ![![2542, -121, 0], ![19724, 0, 0]], ![![183, 6, -2], ![1420, 109, 0]]]
  g := ![![![1, 0, 0], ![-142, 163, 0], ![-9, 0, 163]], ![![-1, 1, 0], ![19, -22, 3], ![-39, 47, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![38, -48, 1]] ![![163, 0, 0], ![-21, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-3423, 163, 0]], ![![6194, -7824, 163], ![-652, 1141, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-21, 1, 0]]], ![![![38, -48, 1]], ![![-4, 7, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-16, 45, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-16, 45, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![151, 45, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-16, 45, 1], ![146, -14, 137], ![6716, 2195, 123]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-151, -45, 167]], ![![-1, 0, 1], ![-123, -37, 137], ![-71, -20, 123]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [145, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 166], [0, 1]]
 g := ![![[105, 93], [98, 98], [41, 57], [4], [137], [29, 116], [1]], ![[6, 74], [26, 69], [115, 110], [4], [137], [121, 51], [1]]]
 h' := ![![[139, 166], [152, 60], [67, 91], [73, 97], [73, 165], [137, 53], [22, 139], [0, 1]], ![[0, 1], [142, 107], [24, 76], [29, 70], [129, 2], [156, 114], [138, 28], [139, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [85, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [145, 28, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1313, 931, 659]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-588, -172, 659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![30, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![30, 1, 0]] 
 ![![167, 0, 0], ![30, 1, 0], ![44, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![30, 1, 0], ![0, 29, 3], ![146, 47, 32]]]
  hmulB := by decide  
  f := ![![![811, 27, 0], ![-4509, 0, 0]], ![![90, 3, 0], ![-500, 0, 0]], ![![172, -4, -1], ![-956, 56, 0]]]
  g := ![![![1, 0, 0], ![-30, 167, 0], ![-44, 0, 167]], ![![0, 1, 0], ![-6, 29, 3], ![-16, 47, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-16, 45, 1]] ![![167, 0, 0], ![30, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![5010, 167, 0]], ![![-2672, 7515, 167], ![-334, 1336, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![30, 1, 0]]], ![![![-16, 45, 1]], ![![-2, 8, 1]]]]
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


lemma PB173I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 172 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 172 (by omega)

def PB173I3 : PrimesBelowBoundCertificateInterval O 137 172 173 where
  m := 6
  g := ![3, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB173I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I163N1, I167N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [], [I163N1], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
