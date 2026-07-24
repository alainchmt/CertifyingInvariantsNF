
import IdealArithmetic.Examples.NF3_1_393835_1.RI3_1_393835_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![16, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![16, 1, 0]] 
 ![![139, 0, 0], ![16, 1, 0], ![22, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![16, 1, 0], ![0, 16, 1], ![280, 81, 17]]]
  hmulB := by decide  
  f := ![![![1457, 91, 0], ![-12649, 0, 0]], ![![144, 9, 0], ![-1250, 0, 0]], ![![226, 14, 0], ![-1962, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 139, 0], ![-22, 0, 139]], ![![0, 1, 0], ![-2, 16, 1], ![-10, 81, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-13, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-13, 1, 0]] 
 ![![139, 0, 0], ![126, 1, 0], ![109, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-13, 1, 0], ![0, -13, 1], ![280, 81, -12]]]
  hmulB := by decide  
  f := ![![![1470, -113, 0], ![15707, 0, 0]], ![![1340, -103, 0], ![14318, 0, 0]], ![![1146, -88, 0], ![12245, 1, 0]]]
  g := ![![![1, 0, 0], ![-126, 139, 0], ![-109, 0, 139]], ![![-1, 1, 0], ![11, -13, 1], ![-62, 81, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-309, -118, -12]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-309, -118, -12]] 
 ![![139, 0, 0], ![135, 1, 0], ![123, 0, 1]] where
  M :=![![![-309, -118, -12], ![-3360, -1281, -130], ![-36400, -13890, -1411]]]
  hmulB := by decide  
  f := ![![![-1791, -182, 32]], ![![-1675, -171, 30]], ![![-1887, -184, 33]]]
  g := ![![![123, -118, -12], ![1335, -1281, -130], ![14477, -13890, -1411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![16, 1, 0]] ![![139, 0, 0], ![-13, 1, 0]]
  ![![-1791, -182, 32]] where
 M := ![![![19321, 0, 0], ![-1807, 139, 0]], ![![2224, 139, 0], ![-208, 3, 1]]]
 hmul := by decide  
 g := ![![![![-42951, -16402, -1668]], ![![657, 253, 26]]], ![![![-8304, -3169, -322]], ![![128, 49, 5]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-1791, -182, 32]] ![![-309, -118, -12]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34414601, -13128342, -1333214]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-34414601, -13128342, -1333214]] 
 ![![149, 0, 0], ![14, 1, 0], ![102, 0, 1]] where
  M :=![![![-34414601, -13128342, -1333214], ![-373299920, -142404935, -14461556], ![-4049235680, -1544685956, -156866491]]]
  hmulB := by decide  
  f := ![![![574451, 45338, -9062]], ![![36946, 3189, -608]], ![![461418, 33728, -7031]]]
  g := ![![![1915235, -13128342, -1333214], ![20774818, -142404935, -14461556], ![225347314, -1544685956, -156866491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![39, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![39, 1, 0]] 
 ![![149, 0, 0], ![39, 1, 0], ![118, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![39, 1, 0], ![0, 39, 1], ![280, 81, 40]]]
  hmulB := by decide  
  f := ![![![2692, 69, 0], ![-10281, 0, 0]], ![![702, 18, 0], ![-2681, 0, 0]], ![![2078, 53, 0], ![-7936, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 149, 0], ![-118, 0, 149]], ![![0, 1, 0], ![-11, 39, 1], ![-51, 81, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-54, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-54, 1, 0]] 
 ![![149, 0, 0], ![95, 1, 0], ![64, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-54, 1, 0], ![0, -54, 1], ![280, 81, -53]]]
  hmulB := by decide  
  f := ![![![5023, -93, 0], ![13857, 0, 0]], ![![3241, -60, 0], ![8941, 0, 0]], ![![2180, -40, 0], ![6014, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 149, 0], ![-64, 0, 149]], ![![-1, 1, 0], ![34, -54, 1], ![-27, 81, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-34414601, -13128342, -1333214]] ![![149, 0, 0], ![39, 1, 0]]
  ![![149, 0, 0], ![-50, 53, 1]] where
 M := ![![![-5127775549, -1956122958, -198648886], ![-1715469359, -654410273, -66456902]]]
 hmul := by decide  
 g := ![![![![-32554251, -15100313, -1370421], ![5543843, 0, 0]], ![![-10890841, -5051734, -458467], ![1854681, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-50, 53, 1]] ![![149, 0, 0], ![-54, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-8046, 149, 0]], ![![-7450, 7897, 149], ![2980, -2831, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-54, 1, 0]]], ![![![-50, 53, 1]], ![![20, -19, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [108, 16, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 32, 103], [127, 118, 48], [0, 1]]
 g := ![![[74, 36, 39], [74, 76, 39], [26, 116, 55], [54, 128], [5, 46, 4], [138, 1], []], ![[83, 110, 46, 74], [65, 45, 150, 34], [56, 109, 79, 37], [43, 58], [122, 128, 144, 80], [37, 32], [45, 39]], ![[35, 88, 23, 66], [123, 120, 9, 56], [39, 128, 50, 106], [61, 25], [94, 72, 24, 77], [127, 118], [100, 39]]]
 h' := ![![[11, 32, 103], [11, 67, 48], [61, 80, 48], [76, 28, 120], [64, 148, 66], [45, 100, 2], [0, 0, 1], [0, 1]], ![[127, 118, 48], [78, 30, 32], [120, 144, 12], [68, 141, 132], [129, 55, 80], [123, 29, 117], [93, 0, 118], [11, 32, 103]], ![[0, 1], [62, 54, 71], [102, 78, 91], [3, 133, 50], [20, 99, 5], [149, 22, 32], [44, 0, 32], [127, 118, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 95], []]
 b := ![[], [67, 44, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [108, 16, 13, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-183012, -73990, -7852]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1212, -490, -52]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-84, 48, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-84, 48, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![73, 48, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-84, 48, 1], ![280, -3, 49], ![13720, 4249, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -48, 157]], ![![-1, 0, 1], ![-21, -15, 49], ![66, 13, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [65, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 156], [0, 1]]
 g := ![![[126, 106], [47], [52, 101], [126, 52], [91, 117], [48], [1]], ![[39, 51], [47], [95, 56], [30, 105], [32, 40], [48], [1]]]
 h' := ![![[131, 156], [66, 48], [74, 138], [131, 27], [51, 113], [6, 91], [92, 131], [0, 1]], ![[0, 1], [74, 109], [97, 19], [57, 130], [96, 44], [152, 66], [140, 26], [131, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [49, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [65, 26, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-800, 2229, 802]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-378, -231, 802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-49, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-49, 1, 0]] 
 ![![157, 0, 0], ![108, 1, 0], ![111, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-49, 1, 0], ![0, -49, 1], ![280, 81, -48]]]
  hmulB := by decide  
  f := ![![![7400, -151, 0], ![23707, 0, 0]], ![![5048, -103, 0], ![16172, 0, 0]], ![![5210, -106, 0], ![16691, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 157, 0], ![-111, 0, 157]], ![![-1, 1, 0], ![33, -49, 1], ![-20, 81, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-84, 48, 1]] ![![157, 0, 0], ![-49, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-7693, 157, 0]], ![![-13188, 7536, 157], ![4396, -2355, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-49, 1, 0]]], ![![![-84, 48, 1]], ![![28, -15, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [45, 93, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 90, 125], [97, 72, 38], [0, 1]]
 g := ![![[39, 49, 160], [153, 24, 22], [114, 22], [80, 38], [], [39, 135, 1], []], ![[65, 79, 54, 109], [83, 120, 69, 147], [157, 58], [66, 34], [57, 85], [138, 38, 37, 75], [161, 140]], ![[45, 121, 41, 160], [19, 0, 87, 14], [114, 121], [75, 51], [104, 85], [109, 27, 3, 56], [85, 140]]]
 h' := ![![[38, 90, 125], [124, 51, 46], [110, 61, 48], [26, 152, 115], [140, 60, 53], [38, 78], [0, 0, 1], [0, 1]], ![[97, 72, 38], [91, 7, 70], [102, 77, 160], [141, 22, 59], [103, 31, 69], [68, 11, 133], [67, 74, 72], [38, 90, 125]], ![[0, 1], [157, 105, 47], [56, 25, 118], [40, 152, 152], [36, 72, 41], [106, 74, 30], [42, 89, 90], [97, 72, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121, 37], []]
 b := ![[], [157, 43, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [45, 93, 28, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163163, -62918, -28362]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1001, -386, -174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -13, -2]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-19, -13, -2]] 
 ![![167, 0, 0], ![0, 167, 0], ![93, 90, 1]] where
  M :=![![![-19, -13, -2], ![-560, -181, -15], ![-4200, -1775, -196]]]
  hmulB := by decide  
  f := ![![![-53, -6, 1]], ![![280, 28, -5]], ![![113, 11, -2]]]
  g := ![![![1, 1, -2], ![5, 7, -15], ![84, 95, -196]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [55, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 166], [0, 1]]
 g := ![![[160, 152], [89, 116], [81, 87], [21], [114], [121, 96], [1]], ![[63, 15], [160, 51], [9, 80], [21], [114], [7, 71], [1]]]
 h' := ![![[51, 166], [115, 73], [54, 28], [101, 33], [33, 45], [25, 75], [112, 51], [0, 1]], ![[0, 1], [164, 94], [146, 139], [114, 134], [157, 122], [9, 92], [41, 116], [51, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [141, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [55, 116, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1012, 2881, 379]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-205, -187, 379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, -6, 1]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-53, -6, 1]] 
 ![![167, 0, 0], ![76, 1, 0], ![69, 0, 1]] where
  M :=![![![-53, -6, 1], ![280, 28, -5], ![-1400, -125, 23]]]
  hmulB := by decide  
  f := ![![![-19, -13, -2]], ![![-12, -7, -1]], ![![-33, -16, -2]]]
  g := ![![![2, -6, 1], ![-9, 28, -5], ![39, -125, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-19, -13, -2]] ![![-53, -6, 1]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-59, -38, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-59, -38, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![114, 135, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-59, -38, 1], ![280, 22, -37], ![-10360, -2717, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -135, 173]], ![![-1, -1, 1], ![26, 29, -37], ![-50, -4, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [142, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 172], [0, 1]]
 g := ![![[60, 106], [81], [31, 151], [128, 90], [31], [2, 119], [1]], ![[0, 67], [81], [112, 22], [64, 83], [31], [75, 54], [1]]]
 h' := ![![[130, 172], [136, 148], [96, 9], [162, 18], [134, 104], [62, 66], [31, 130], [0, 1]], ![[0, 1], [0, 25], [55, 164], [80, 155], [160, 69], [165, 107], [150, 43], [130, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [76, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [142, 43, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![982, 480, 42]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -30, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![37, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![37, 1, 0]] 
 ![![173, 0, 0], ![37, 1, 0], ![15, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![37, 1, 0], ![0, 37, 1], ![280, 81, 38]]]
  hmulB := by decide  
  f := ![![![3664, 99, 0], ![-17127, 0, 0]], ![![740, 20, 0], ![-3459, 0, 0]], ![![304, 8, 0], ![-1421, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 173, 0], ![-15, 0, 173]], ![![0, 1, 0], ![-8, 37, 1], ![-19, 81, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-59, -38, 1]] ![![173, 0, 0], ![37, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![6401, 173, 0]], ![![-10207, -6574, 173], ![-1903, -1384, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![37, 1, 0]]], ![![![-59, -38, 1]], ![![-11, -8, 0]]]]
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


lemma PB178I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 177 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 177 (by omega)

def PB178I3 : PrimesBelowBoundCertificateInterval O 137 177 178 where
  m := 7
  g := ![3, 3, 1, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB178I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
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
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I139N0, I139N1, I139N2, I149N0, I149N1, I149N2, I157N1, I167N1, I173N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N0, I149N1, I149N2], [], [I157N1], [], [I167N1], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
