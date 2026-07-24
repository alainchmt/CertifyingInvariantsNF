
import IdealArithmetic.Examples.NF3_1_399916_3.RI3_1_399916_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![23, 30, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![23, 30, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![23, 30, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![23, 30, 1], ![152, 23, 61], ![3721, 61, 53]]]
  hmulB := by decide  
  f := ![![![-22, -30, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -30, 139]], ![![0, 0, 1], ![-9, -13, 61], ![18, -11, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [65, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 138], [0, 1]]
 g := ![![[21, 77], [67, 83], [25], [73, 5], [16], [69], [1]], ![[0, 62], [57, 56], [25], [59, 134], [16], [69], [1]]]
 h' := ![![[25, 138], [93, 63], [126, 120], [120, 134], [118, 127], [18, 4], [74, 25], [0, 1]], ![[0, 1], [0, 76], [68, 19], [134, 5], [96, 12], [118, 135], [4, 114], [25, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [61, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [65, 114, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![685, 132, -218]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 48, -218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-61, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-61, 1, 0]] 
 ![![139, 0, 0], ![78, 1, 0], ![86, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-61, 1, 0], ![1, -61, 2], ![122, 0, -60]]]
  hmulB := by decide  
  f := ![![![-370, 37511, -1230], ![556, 85485, 0]], ![![-222, 21043, -690], ![279, 47955, 0]], ![![-214, 23208, -761], ![378, 52890, 0]]]
  g := ![![![1, 0, 0], ![-78, 139, 0], ![-86, 0, 139]], ![![-1, 1, 0], ![33, -61, 2], ![38, 0, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![23, 30, 1]] ![![139, 0, 0], ![-61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8479, 139, 0]], ![![3197, 4170, 139], ![-1251, -1807, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-61, 1, 0]]], ![![![23, 30, 1]], ![![-9, -13, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -5, 2]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-10, -5, 2]] 
 ![![149, 0, 0], ![48, 1, 0], ![115, 0, 1]] where
  M :=![![![-10, -5, 2], ![239, -10, -8], ![-488, 122, -15]]]
  hmulB := by decide  
  f := ![![![-1126, -169, -60]], ![![-413, -62, -22]], ![![-1032, -155, -55]]]
  g := ![![![0, -5, 2], ![11, -10, -8], ![-31, 122, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -3, -1]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-18, -3, -1]] 
 ![![149, 0, 0], ![50, 1, 0], ![17, 0, 1]] where
  M :=![![![-18, -3, -1], ![-125, -18, -7], ![-427, -61, -21]]]
  hmulB := by decide  
  f := ![![![49, 2, -3]], ![![14, 1, -1]], ![![6, -1, 0]]]
  g := ![![![1, -3, -1], ![6, -18, -7], ![20, -61, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-10, -5, 2]] ![![-18, -3, -1]]
  ![![-49, -2, 3]] where
 M := ![![![-49, -2, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-49, -2, 3]] ![![-18, -3, -1]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19574, -2145, -246]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![19574, -2145, -246]] 
 ![![151, 0, 0], ![0, 151, 0], ![150, 110, 1]] where
  M :=![![![19574, -2145, -246], ![-32157, 19574, -4536], ![-276696, -15006, 17429]]]
  hmulB := by decide  
  f := ![![![-1808530, -272031, -96324]], ![![-12023559, -1808530, -640386]], ![![-10814136, -1626614, -575971]]]
  g := ![![![374, 165, -246], ![4293, 3434, -4536], ![-19146, -12796, 17429]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [41, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 150], [0, 1]]
 g := ![![[124, 2], [8, 98], [105, 72], [42], [24, 34], [84], [1]], ![[73, 149], [76, 53], [81, 79], [42], [63, 117], [84], [1]]]
 h' := ![![[50, 150], [125, 46], [74, 20], [134, 125], [73, 93], [49, 100], [110, 50], [0, 1]], ![[0, 1], [9, 105], [17, 131], [42, 26], [42, 58], [66, 51], [43, 101], [50, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [56, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [41, 101, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-664, 1315, 513]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-514, -365, 513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1808530, 272031, 96324]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![1808530, 272031, 96324]] 
 ![![151, 0, 0], ![81, 1, 0], ![42, 0, 1]] where
  M :=![![![1808530, 272031, 96324], ![12023559, 1808530, 640386], ![39063546, 5875764, 2080561]]]
  hmulB := by decide  
  f := ![![![-19574, 2145, 246]], ![![-10287, 1021, 162]], ![![-3612, 696, -47]]]
  g := ![![![-160739, 272031, 96324], ![-1068633, 1808530, 640386], ![-3471900, 5875764, 2080561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![19574, -2145, -246]] ![![1808530, 272031, 96324]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![7, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![7, 1, 0]] 
 ![![157, 0, 0], ![7, 1, 0], ![133, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![7, 1, 0], ![1, 7, 2], ![122, 0, 8]]]
  hmulB := by decide  
  f := ![![![-2782, -19529, -5580], ![-157, 438030, 0]], ![![-124, -868, -248], ![1, 19468, 0]], ![![-2359, -16544, -4727], ![-82, 371070, 0]]]
  g := ![![![1, 0, 0], ![-7, 157, 0], ![-133, 0, 157]], ![![0, 1, 0], ![-2, 7, 2], ![-6, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-206, -31, -11]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-206, -31, -11]] 
 ![![157, 0, 0], ![74, 1, 0], ![10, 0, 1]] where
  M :=![![![-206, -31, -11], ![-1373, -206, -73], ![-4453, -671, -237]]]
  hmulB := by decide  
  f := ![![![161, -34, 3]], ![![78, -15, 1]], ![![-15, -1, 1]]]
  g := ![![![14, -31, -11], ![93, -206, -73], ![303, -671, -237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![75, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![75, 1, 0]] 
 ![![157, 0, 0], ![75, 1, 0], ![14, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![75, 1, 0], ![1, 75, 2], ![122, 0, 76]]]
  hmulB := by decide  
  f := ![![![2454, 296455, 7906], ![3140, -620621, 0]], ![![1138, 141590, 3776], ![1571, -296416, 0]], ![![183, 26435, 705], ![355, -55342, 0]]]
  g := ![![![1, 0, 0], ![-75, 157, 0], ![-14, 0, 157]], ![![0, 1, 0], ![-36, 75, 2], ![-6, 0, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![7, 1, 0]] ![![-206, -31, -11]]
  ![![157, 0, 0], ![24, -38, 1]] where
 M := ![![![-32342, -4867, -1727]], ![![-2815, -423, -150]]]
 hmul := by decide  
 g := ![![![![-206, -31, -11], ![0, 0, 0]]], ![![![-19, -1, -1], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![24, -38, 1]] ![![157, 0, 0], ![75, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![11775, 157, 0]], ![![3768, -5966, 157], ![1884, -2826, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![75, 1, 0]]], ![![![24, -38, 1]], ![![12, -18, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-621844, -93535, -33120]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-621844, -93535, -33120]] 
 ![![163, 0, 0], ![0, 163, 0], ![21, 78, 1]] where
  M :=![![![-621844, -93535, -33120], ![-4134175, -621844, -220190], ![-13431590, -2020320, -715379]]]
  hmulB := by decide  
  f := ![![![748, -145, 10]], ![![1075, 748, -280]], ![![506, 343, -129]]]
  g := ![![![452, 15275, -33120], ![3005, 101552, -220190], ![9763, 329934, -715379]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [162, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 162], [0, 1]]
 g := ![![[54, 22], [141, 118], [4], [84], [91], [114, 145], [1]], ![[101, 141], [156, 45], [4], [84], [91], [120, 18], [1]]]
 h' := ![![[54, 162], [141, 48], [125, 97], [11, 2], [47, 35], [114, 108], [1, 54], [0, 1]], ![[0, 1], [125, 115], [147, 66], [119, 161], [144, 128], [78, 55], [146, 109], [54, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [66, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [162, 109, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246915, 265695, 1256]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1353, 1029, 1256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-748, 145, -10]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-748, 145, -10]] 
 ![![163, 0, 0], ![6, 1, 0], ![64, 0, 1]] where
  M :=![![![-748, 145, -10], ![-1075, -748, 280], ![17080, -610, -603]]]
  hmulB := by decide  
  f := ![![![621844, 93535, 33120]], ![![48253, 7258, 2570]], ![![326562, 49120, 17393]]]
  g := ![![![-6, 145, -10], ![-89, -748, 280], ![364, -610, -603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-621844, -93535, -33120]] ![![-748, 145, -10]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [116, 123, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 161, 145], [13, 5, 22], [0, 1]]
 g := ![![[147, 20, 162], [117, 43, 50], [35, 3, 9], [126, 64], [162, 2], [69, 162, 1], []], ![[112, 121, 80, 119], [114, 14, 54, 102], [155, 65, 103, 43], [157, 137], [63, 94], [106, 53, 119, 118], [15, 150]], ![[67, 157, 68, 89], [159, 80, 153, 112], [116, 52, 41, 112], [104, 47], [151, 6], [39, 52, 99, 124], [138, 150]]]
 h' := ![![[149, 161, 145], [122, 25, 50], [115, 35, 102], [43, 8, 3], [56, 160, 159], [12, 109, 154], [0, 0, 1], [0, 1]], ![[13, 5, 22], [14, 133, 34], [9, 40, 74], [160, 146, 6], [154, 137, 114], [92, 64, 42], [87, 9, 5], [149, 161, 145]], ![[0, 1], [77, 9, 83], [49, 92, 158], [58, 13, 158], [91, 37, 61], [89, 161, 138], [26, 158, 161], [13, 5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 143], []]
 b := ![[], [40, 83, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [116, 123, 5, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-927685, 1336, -6680]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5555, 8, -40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-79, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-79, 1, 0]] 
 ![![173, 0, 0], ![94, 1, 0], ![167, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-79, 1, 0], ![1, -79, 2], ![122, 0, -78]]]
  hmulB := by decide  
  f := ![![![12669, -1524932, 38608], ![-14532, -3339592, 0]], ![![6934, -828507, 20976], ![-7784, -1814424, 0]], ![![12215, -1472044, 37269], ![-14060, -3223768, 0]]]
  g := ![![![1, 0, 0], ![-94, 173, 0], ![-167, 0, 173]], ![![-1, 1, 0], ![41, -79, 2], ![76, 0, -78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 4, -6]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![103, 4, -6]] 
 ![![173, 0, 0], ![105, 1, 0], ![24, 0, 1]] where
  M :=![![![103, 4, -6], ![-728, 103, 2], ![122, -366, 107]]]
  hmulB := by decide  
  f := ![![![-11753, -1768, -626]], ![![-7585, -1141, -404]], ![![-3098, -466, -165]]]
  g := ![![![-1, 4, -6], ![-67, 103, 2], ![208, -366, 107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-27, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-27, 1, 0]] 
 ![![173, 0, 0], ![146, 1, 0], ![155, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-27, 1, 0], ![1, -27, 2], ![122, 0, -26]]]
  hmulB := by decide  
  f := ![![![-1326, 38013, -2816], ![519, 243584, 0]], ![![-1106, 32073, -2376], ![520, 205524, 0]], ![![-1191, 34058, -2523], ![446, 218240, 0]]]
  g := ![![![1, 0, 0], ![-146, 173, 0], ![-155, 0, 173]], ![![-1, 1, 0], ![21, -27, 2], ![24, 0, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-79, 1, 0]] ![![103, 4, -6]]
  ![![173, 0, 0], ![5, 13, 1]] where
 M := ![![![17819, 692, -1038]], ![![-8865, -213, 476]]]
 hmul := by decide  
 g := ![![![![98, -9, -7], ![173, 0, 0]]], ![![![-55, -11, 2], ![130, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![5, 13, 1]] ![![173, 0, 0], ![-27, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-4671, 173, 0]], ![![865, 2249, 173], ![0, -346, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-27, 1, 0]]], ![![![5, 13, 1]], ![![0, -2, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)


lemma PB179I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 178 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 178 (by omega)

def PB179I3 : PrimesBelowBoundCertificateInterval O 137 178 179 where
  m := 7
  g := ![2, 3, 2, 3, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB179I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
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
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
  β := ![I139N1, I149N0, I149N1, I151N1, I157N0, I157N1, I157N2, I163N1, I173N0, I173N1, I173N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N1], [I151N1], [I157N0, I157N1, I157N2], [I163N1], [], [I173N0, I173N1, I173N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
