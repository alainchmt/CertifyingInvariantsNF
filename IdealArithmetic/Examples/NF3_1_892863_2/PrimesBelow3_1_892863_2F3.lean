
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-22, 65, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-22, 65, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![117, 65, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-22, 65, 1], ![279, 16, 259], ![9597, -1711, -114]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-117, -65, 139]], ![![-1, 0, 1], ![-216, -121, 259], ![165, 41, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [101, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 138], [0, 1]]
 g := ![![[4, 99], [137, 96], [129], [91, 42], [5], [30], [1]], ![[40, 40], [134, 43], [129], [81, 97], [5], [30], [1]]]
 h' := ![![[13, 138], [63, 88], [48, 42], [122, 44], [103, 43], [82, 127], [38, 13], [0, 1]], ![[0, 1], [95, 51], [38, 97], [138, 95], [106, 96], [65, 12], [68, 126], [13, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [10, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [101, 126, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148, 700, -1700]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1432, 800, -1700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![19, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![19, 1, 0]] 
 ![![139, 0, 0], ![19, 1, 0], ![114, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![19, 1, 0], ![2, 20, 4], ![149, -27, 18]]]
  hmulB := by decide  
  f := ![![![-1256, -12759, -2552], ![-139, 88682, 0]], ![![-174, -1740, -348], ![1, 12093, 0]], ![![-1026, -10464, -2093], ![-144, 72732, 0]]]
  g := ![![![1, 0, 0], ![-19, 139, 0], ![-114, 0, 139]], ![![0, 1, 0], ![-6, 20, 4], ![-10, -27, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-22, 65, 1]] ![![139, 0, 0], ![19, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2641, 139, 0]], ![![-3058, 9035, 139], ![-139, 1251, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![19, 1, 0]]], ![![![-22, 65, 1]], ![![-1, 9, 2]]]]
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
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-39, 54, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-39, 54, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![110, 54, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-39, 54, 1], ![257, -12, 215], ![7958, -1414, -120]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-110, -54, 149]], ![![-1, 0, 1], ![-157, -78, 215], ![142, 34, -120]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [116, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 148], [0, 1]]
 g := ![![[123, 9], [69], [51, 19], [6], [114, 121], [104], [1]], ![[0, 140], [69], [139, 130], [6], [0, 28], [104], [1]]]
 h' := ![![[36, 148], [41, 3], [44, 48], [77, 82], [37, 119], [51, 11], [33, 36], [0, 1]], ![[0, 1], [0, 146], [133, 101], [49, 67], [0, 30], [0, 138], [137, 113], [36, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [134, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [116, 113, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1854, 1100, -90]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 40, -90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-66, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-66, 1, 0]] 
 ![![149, 0, 0], ![83, 1, 0], ![120, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-66, 1, 0], ![2, -65, 4], ![149, -27, -67]]]
  hmulB := by decide  
  f := ![![![251, -10269, 632], ![-149, -23542, 0]], ![![177, -5720, 352], ![1, -13112, 0]], ![![246, -8271, 509], ![-21, -18960, 0]]]
  g := ![![![1, 0, 0], ![-83, 149, 0], ![-120, 0, 149]], ![![-1, 1, 0], ![33, -65, 4], ![70, -27, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-39, 54, 1]] ![![149, 0, 0], ![-66, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9834, 149, 0]], ![![-5811, 8046, 149], ![2831, -3576, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-66, 1, 0]]], ![![![-39, 54, 1]], ![![19, -24, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-56, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-56, 1, 0]] 
 ![![151, 0, 0], ![95, 1, 0], ![61, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-56, 1, 0], ![2, -55, 4], ![149, -27, -57]]]
  hmulB := by decide  
  f := ![![![12633, -422791, 30752], ![-7399, -1160888, 0]], ![![7937, -265949, 19344], ![-4680, -730236, 0]], ![![5139, -170797, 12423], ![-2893, -468968, 0]]]
  g := ![![![1, 0, 0], ![-95, 151, 0], ![-61, 0, 151]], ![![-1, 1, 0], ![33, -55, 4], ![41, -27, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435340608719, -19230359694, -13485640310]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-435340608719, -19230359694, -13485640310]] 
 ![![151, 0, 0], ![112, 1, 0], ![83, 0, 1]] where
  M :=![![![-435340608719, -19230359694, -13485640310], ![-2047821125578, -90458680043, -63435798466], ![-1678587247126, -74148461902, -51997960655]]]
  hmulB := by decide  
  f := ![![![3334167, -630050, -96074]], ![![2369878, -432235, -87314]], ![![1266973, -261656, -9377]]]
  g := ![![![18793164389, -19230359694, -13485640310], ![88402134516, -90458680043, -63435798466], ![72462723313, -74148461902, -51997960655]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-56, 1, 0]] ![![151, 0, 0], ![-56, 1, 0]]
  ![![-3334167, 630050, 96074]] where
 M := ![![![22801, 0, 0], ![-8456, 151, 0]], ![![-8456, 151, 0], ![3138, -111, 4]]]
 hmul := by decide  
 g := ![![![![65736431916569, 2903784313794, 2036331686810]], ![![-22331252962686, -986441462821, -691760058894]]], ![![![-22331252962686, -986441462821, -691760058894]], ![![7586126054368, 335102974057, 234997069574]]]]
 hle2 := by decide  
def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-3334167, 630050, 96074]] ![![-435340608719, -19230359694, -13485640310]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [53, 35, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 8, 37], [119, 148, 120], [0, 1]]
 g := ![![[117, 67, 130], [114, 11], [116, 155, 57], [55, 7, 31], [155, 121, 124], [41, 1], []], ![[61, 96, 70, 27], [78, 14], [133, 109, 65, 81], [80, 121, 71, 57], [105, 88, 35, 140], [68, 81], [44, 113]], ![[10, 118, 1, 106], [152, 75], [46, 119, 89, 52], [80, 63, 21, 93], [5, 33, 87, 156], [29, 64], [118, 113]]]
 h' := ![![[79, 8, 37], [78, 78, 82], [132, 42, 110], [68, 148, 34], [106, 91, 119], [25, 82, 76], [0, 0, 1], [0, 1]], ![[119, 148, 120], [61, 127, 107], [120, 102, 93], [69, 124, 146], [53, 1, 98], [106, 69, 152], [141, 15, 148], [79, 8, 37]], ![[0, 1], [61, 109, 125], [96, 13, 111], [150, 42, 134], [134, 65, 97], [142, 6, 86], [57, 142, 8], [119, 148, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 78], []]
 b := ![[], [29, 44, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [53, 35, 116, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36561636091, 11801062000, -5296966480]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-232876663, 75166000, -33738640]
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
 ![![163, 0, 0], ![12, 1, 0], ![43, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![12, 1, 0], ![2, 13, 4], ![149, -27, 11]]]
  hmulB := by decide  
  f := ![![![-14839, -97230, -29920], ![-1630, 1219240, 0]], ![![-1100, -7150, -2200], ![1, 89650, 0]], ![![-3919, -25650, -7893], ![-370, 321640, 0]]]
  g := ![![![1, 0, 0], ![-12, 163, 0], ![-43, 0, 163]], ![![0, 1, 0], ![-2, 13, 4], ![0, -27, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![67, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![67, 1, 0]] 
 ![![163, 0, 0], ![67, 1, 0], ![84, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![67, 1, 0], ![2, 68, 4], ![149, -27, 66]]]
  hmulB := by decide  
  f := ![![![-2687, -114162, -6716], ![-1630, 273677, 0]], ![![-1112, -46916, -2760], ![-651, 112470, 0]], ![![-1388, -58832, -3461], ![-832, 141036, 0]]]
  g := ![![![1, 0, 0], ![-67, 163, 0], ![-84, 0, 163]], ![![0, 1, 0], ![-30, 68, 4], ![-22, -27, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-79, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-79, 1, 0]] 
 ![![163, 0, 0], ![84, 1, 0], ![90, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-79, 1, 0], ![2, -78, 4], ![149, -27, -80]]]
  hmulB := by decide  
  f := ![![![-2774, 154425, -7920], ![2445, 322740, 0]], ![![-1407, 79552, -4080], ![1305, 166260, 0]], ![![-1505, 85265, -4373], ![1405, 178200, 0]]]
  g := ![![![1, 0, 0], ![-84, 163, 0], ![-90, 0, 163]], ![![-1, 1, 0], ![38, -78, 4], ![59, -27, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![12, 1, 0]] ![![163, 0, 0], ![67, 1, 0]]
  ![![163, 0, 0], ![-43, 20, 1]] where
 M := ![![![26569, 0, 0], ![10921, 163, 0]], ![![1956, 163, 0], ![806, 80, 4]]]
 hmul := by decide  
 g := ![![![![163, 0, 0], ![0, 0, 0]], ![![67, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-43, 20, 1]] ![![163, 0, 0], ![-79, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-12877, 163, 0]], ![![-7009, 3260, 163], ![3586, -1630, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-79, 1, 0]]], ![![![-43, 20, 1]], ![![22, -10, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-28, 59, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-28, 59, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![139, 59, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-28, 59, 1], ![267, 4, 235], ![8703, -1549, -114]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -59, 167]], ![![-1, 0, 1], ![-194, -83, 235], ![147, 31, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [53, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 166], [0, 1]]
 g := ![![[158, 93], [123, 42], [56, 72], [128], [89], [76, 75], [1]], ![[97, 74], [117, 125], [165, 95], [128], [89], [113, 92], [1]]]
 h' := ![![[143, 166], [161, 107], [38, 83], [20, 78], [25, 63], [147, 16], [114, 143], [0, 1]], ![[0, 1], [98, 60], [50, 84], [152, 89], [16, 104], [97, 151], [22, 24], [143, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [66, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [53, 24, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2234, 1761, -1459]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1201, 526, -1459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-68, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-68, 1, 0]] 
 ![![167, 0, 0], ![99, 1, 0], ![114, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-68, 1, 0], ![2, -67, 4], ![149, -27, -69]]]
  hmulB := by decide  
  f := ![![![-4135, 177265, -10584], ![2839, 441882, 0]], ![![-2455, 105046, -6272], ![1671, 261856, 0]], ![![-2806, 121007, -7225], ![1979, 301644, 0]]]
  g := ![![![1, 0, 0], ![-99, 167, 0], ![-114, 0, 167]], ![![-1, 1, 0], ![37, -67, 4], ![64, -27, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-28, 59, 1]] ![![167, 0, 0], ![-68, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11356, 167, 0]], ![![-4676, 9853, 167], ![2171, -4008, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-68, 1, 0]]], ![![![-28, 59, 1]], ![![13, -24, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [22, 132, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 113, 71], [141, 59, 102], [0, 1]]
 g := ![![[55, 122, 157], [22, 29], [167, 130, 4], [86, 162, 36], [147, 16], [137, 142, 1], []], ![[153, 96, 99, 46], [41, 13], [162, 169, 15, 165], [6, 43, 133, 94], [171, 137], [131, 77, 51, 107], [78, 24]], ![[128, 58, 1, 5], [67, 1], [8, 161, 108, 79], [94, 153, 109, 171], [102, 119], [93, 90, 15, 94], [47, 24]]]
 h' := ![![[1, 113, 71], [159, 66, 26], [132, 129, 78], [11, 150, 2], [19, 153, 167], [100, 71, 169], [0, 0, 1], [0, 1]], ![[141, 59, 102], [96, 60, 165], [47, 168, 94], [18, 79, 42], [82, 86, 129], [111, 72, 134], [15, 128, 59], [1, 113, 71]], ![[0, 1], [36, 47, 155], [68, 49, 1], [35, 117, 129], [27, 107, 50], [117, 30, 43], [163, 45, 113], [141, 59, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 69], []]
 b := ![[], [24, 84, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [22, 132, 31, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1060490, 376102, -186494]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6130, 2174, -1078]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [5, 90, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 53, 70], [133, 125, 109], [0, 1]]
 g := ![![[105, 36, 93], [146, 170, 83], [165, 5], [7, 138], [138, 0, 106], [171, 145, 1], []], ![[72, 34, 174, 46], [65, 111, 104, 12], [104, 36], [53, 61], [150, 23, 18, 83], [120, 164, 71, 60], [130, 67]], ![[62, 76, 65, 32], [112, 68, 155, 7], [74, 39], [145, 80], [56, 121, 115, 174], [61, 146, 161, 91], [91, 67]]]
 h' := ![![[12, 53, 70], [165, 166, 56], [146, 14, 158], [104, 69, 149], [26, 99, 106], [40, 174, 105], [0, 0, 1], [0, 1]], ![[133, 125, 109], [134, 171, 4], [21, 151, 145], [2, 51, 6], [25, 124, 132], [13, 5, 66], [31, 156, 125], [12, 53, 70]], ![[0, 1], [162, 21, 119], [63, 14, 55], [84, 59, 24], [56, 135, 120], [150, 0, 8], [50, 23, 53], [133, 125, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 43], []]
 b := ![[], [52, 20, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [5, 90, 34, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![316147652, -117191121, 68430447]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1766188, -654699, 382293]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-53, 30, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-53, 30, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![128, 30, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-53, 30, 1], ![209, -50, 119], ![4382, -766, -110]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-128, -30, 181]], ![![-1, 0, 1], ![-83, -20, 119], ![102, 14, -110]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [88, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 180], [0, 1]]
 g := ![![[74, 100], [178], [156, 3], [9], [145, 82], [84, 16], [1]], ![[112, 81], [178], [168, 178], [9], [111, 99], [148, 165], [1]]]
 h' := ![![[4, 180], [143, 171], [28, 97], [68, 33], [91, 178], [29, 156], [93, 4], [0, 1]], ![[0, 1], [103, 10], [54, 84], [19, 148], [79, 3], [110, 25], [109, 177], [4, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [28, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [88, 177, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-472, 274, -196]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 34, -196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![62, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![62, 1, 0]] 
 ![![181, 0, 0], ![62, 1, 0], ![110, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![62, 1, 0], ![2, 63, 4], ![149, -27, 61]]]
  hmulB := by decide  
  f := ![![![-3007, -110368, -7008], ![-1448, 317112, 0]], ![![-1014, -37797, -2400], ![-542, 108600, 0]], ![![-1798, -67074, -4259], ![-966, 192720, 0]]]
  g := ![![![1, 0, 0], ![-62, 181, 0], ![-110, 0, 181]], ![![0, 1, 0], ![-24, 63, 4], ![-27, -27, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-53, 30, 1]] ![![181, 0, 0], ![62, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![11222, 181, 0]], ![![-9593, 5430, 181], ![-3077, 1810, 181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![62, 1, 0]]], ![![![-53, 30, 1]], ![![-17, 10, 1]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![22, -18, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![22, -18, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![22, 173, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![22, -18, 1], ![113, -23, -73], ![-2770, 530, 13]]]
  hmulB := by decide  
  f := ![![![-21, 18, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -173, 191]], ![![0, -1, 1], ![9, 66, -73], ![-16, -9, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [41, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 190], [0, 1]]
 g := ![![[62, 85], [39, 3], [63, 20], [119, 18], [60, 72], [9, 43], [1]], ![[13, 106], [53, 188], [29, 171], [12, 173], [14, 119], [146, 148], [1]]]
 h' := ![![[132, 190], [120, 127], [91, 167], [87, 28], [23, 171], [13, 151], [150, 132], [0, 1]], ![[0, 1], [76, 64], [170, 24], [154, 163], [57, 20], [81, 40], [2, 59], [132, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [51, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [41, 59, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519, 2996, -2034]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![237, 1858, -2034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![73, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![73, 1, 0]] 
 ![![191, 0, 0], ![73, 1, 0], ![178, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![73, 1, 0], ![2, 74, 4], ![149, -27, 72]]]
  hmulB := by decide  
  f := ![![![38531, 1765810, 95456], ![24066, -4558024, 0]], ![![14736, 674832, 36480], ![9169, -1741920, 0]], ![![35910, 1645624, 88959], ![22424, -4247792, 0]]]
  g := ![![![1, 0, 0], ![-73, 191, 0], ![-178, 0, 191]], ![![0, 1, 0], ![-32, 74, 4], ![-56, -27, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![22, -18, 1]] ![![191, 0, 0], ![73, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![13943, 191, 0]], ![![4202, -3438, 191], ![1719, -1337, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![73, 1, 0]]], ![![![22, -18, 1]], ![![9, -7, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![20, -30, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![20, -30, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![20, 163, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![20, -30, 1], ![89, -37, -121], ![-4558, 854, 23]]]
  hmulB := by decide  
  f := ![![![-19, 30, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -163, 193]], ![![0, -1, 1], ![13, 102, -121], ![-26, -15, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [146, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 192], [0, 1]]
 g := ![![[155, 107], [55], [157], [49], [3], [54], [144, 1]], ![[123, 86], [55], [157], [49], [3], [54], [95, 192]]]
 h' := ![![[144, 192], [40, 53], [93, 21], [137, 100], [166, 186], [5, 14], [13, 132], [0, 1]], ![[0, 1], [145, 140], [29, 172], [62, 93], [123, 7], [91, 179], [107, 61], [144, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164]]
 b := ![[], [79, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [146, 49, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2356, 5730, -6560]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![692, 5570, -6560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-72, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-72, 1, 0]] 
 ![![193, 0, 0], ![121, 1, 0], ![170, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-72, 1, 0], ![2, -71, 4], ![149, -27, -73]]]
  hmulB := by decide  
  f := ![![![1785, -76107, 4288], ![-965, -206896, 0]], ![![1129, -47709, 2688], ![-578, -129696, 0]], ![![1554, -67037, 3777], ![-899, -182240, 0]]]
  g := ![![![1, 0, 0], ![-121, 193, 0], ![-170, 0, 193]], ![![-1, 1, 0], ![41, -71, 4], ![82, -27, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![20, -30, 1]] ![![193, 0, 0], ![-72, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-13896, 193, 0]], ![![3860, -5790, 193], ![-1351, 2123, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-72, 1, 0]]], ![![![20, -30, 1]], ![![-7, 11, -1]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB268I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB268I3 : PrimesBelowBoundCertificateInterval O 137 193 268 where
  m := 11
  g := ![2, 2, 3, 1, 3, 2, 1, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB268I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N0
      exact NI151N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I163N0, I163N1, I163N2, I167N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N0, I151N1], [], [I163N0, I163N1, I163N2], [I167N1], [], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
