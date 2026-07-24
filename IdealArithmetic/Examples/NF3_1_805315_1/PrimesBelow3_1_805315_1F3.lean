
import IdealArithmetic.Examples.NF3_1_805315_1.RI3_1_805315_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1983054472005, -1399862770043, -509989762833]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![1983054472005, -1399862770043, -509989762833]] 
 ![![139, 0, 0], ![17, 1, 0], ![50, 0, 1]] where
  M :=![![![1983054472005, -1399862770043, -509989762833], ![112197747823260, -13186531894529, -6999313850215], ![285530259844808, -15356745226509, -11786669124486]]]
  hmulB := by decide  
  f := ![![![47938608782167312249987659, -8667936434229143784032901, 3073082601281670610868588]], ![![999123575646595495386337, -180654797117641506252897, 64048360076566053702169]], ![![31935914310037199653703878, -5774436977640558116897491, 2047237187632057189114165]]]
  g := ![![![368922371974, -1399862770043, -509989762833], ![4937658147777, -13186531894529, -6999313850215], ![8172146654099, -15356745226509, -11786669124486]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40613659, -2391249, 161736]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-40613659, -2391249, 161736]] 
 ![![139, 0, 0], ![123, 1, 0], ![91, 0, 1]] where
  M :=![![![-40613659, -2391249, 161736], ![-35581920, -38638036, -11956245], ![533191164, -71680107, -36246787]]]
  hmulB := by decide  
  f := ![![![-543479740072117, 98268346952715, -34839520290501]], ![![-425779234280289, 76986534059144, -27294383172432]], ![![-522364255891669, 94450387289226, -33485921829865]]]
  g := ![![![1717928, -2391249, 161736], ![41761977, -38638036, -11956245], ![90994978, -71680107, -36246787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-943, 60, 42]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-943, 60, 42]] 
 ![![139, 0, 0], ![137, 1, 0], ![83, 0, 1]] where
  M :=![![![-943, 60, 42], ![-9240, 251, 300], ![-11352, -228, 191]]]
  hmulB := by decide  
  f := ![![![-116341, 21036, -7458]], ![![-102863, 18599, -6594]], ![![-105125, 19008, -6739]]]
  g := ![![![-91, 60, 42], ![-493, 251, 300], ![29, -228, 191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![1983054472005, -1399862770043, -509989762833]] ![![-40613659, -2391249, 161736]]
  ![![-302651328282798901347, 85902091849627734434, 35543323848685236786]] where
 M := ![![![-302651328282798901347, 85902091849627734434, 35543323848685236786]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-302651328282798901347, 85902091849627734434, 35543323848685236786]] ![![-943, 60, 42]]
  ![![139, 0, 0]] where
 M := ![![![-911822938450155710194611, -4701532480211606725094, 19848046622109646699752]]]
 hmul := by decide  
 g := ![![![![-6559877255037091440249, -33823974677781343346, 142791702317335587768]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [115, 112, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 96, 34], [25, 52, 115], [0, 1]]
 g := ![![[112, 14, 68], [36, 61], [12, 132, 130], [15, 64], [116, 15, 132], [108, 1], []], ![[2, 122, 130, 122], [72, 31], [107, 108, 48, 115], [30, 64], [136, 19, 34, 92], [8, 22], [107, 113]], ![[14, 128, 22, 136], [65, 16], [95, 6, 124, 21], [90, 107], [11, 90, 107, 137], [116, 127], [26, 113]]]
 h' := ![![[83, 96, 34], [63, 45, 51], [110, 45, 106], [46, 90, 32], [70, 12, 141], [96, 7, 79], [0, 0, 1], [0, 1]], ![[25, 52, 115], [103, 110, 10], [121, 107, 39], [41, 129, 105], [141, 39, 141], [145, 134, 25], [97, 46, 52], [83, 96, 34]], ![[0, 1], [71, 143, 88], [120, 146, 4], [73, 79, 12], [69, 98, 16], [133, 8, 45], [19, 103, 96], [25, 52, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 1], []]
 b := ![[], [136, 93, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [115, 112, 41, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5205613, 1291234, -381738]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34937, 8666, -2562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-63, 75, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-63, 75, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![88, 75, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-63, 75, 1], ![-220, 39, 375], ![-16456, 1981, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -75, 151]], ![![-1, 0, 1], ![-220, -186, 375], ![-88, 31, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [3, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 150], [0, 1]]
 g := ![![[16, 62], [18, 91], [142, 74], [99], [21, 40], [39], [1]], ![[60, 89], [29, 60], [63, 77], [99], [64, 111], [39], [1]]]
 h' := ![![[103, 150], [97, 45], [27, 98], [48, 136], [88, 117], [43, 77], [148, 103], [0, 1]], ![[0, 1], [51, 106], [4, 53], [13, 15], [59, 34], [122, 74], [36, 48], [103, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [15, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [3, 48, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-968, -1731, 1650]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-968, -831, 1650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-73, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-73, 1, 0]] 
 ![![151, 0, 0], ![78, 1, 0], ![36, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-73, 1, 0], ![0, -72, 5], ![-220, 27, -73]]]
  hmulB := by decide  
  f := ![![![7447, -102, 0], ![15402, 0, 0]], ![![3870, -53, 0], ![8004, 0, 0]], ![![1876, 32, -4], ![3880, 121, 0]]]
  g := ![![![1, 0, 0], ![-78, 151, 0], ![-36, 0, 151]], ![![-1, 1, 0], ![36, -72, 5], ![2, 27, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-63, 75, 1]] ![![151, 0, 0], ![-73, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-11023, 151, 0]], ![![-9513, 11325, 151], ![4379, -5436, 302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-73, 1, 0]]], ![![![-63, 75, 1]], ![![29, -36, 2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-54, -5, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-54, -5, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![103, 152, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-54, -5, 1], ![-220, -32, -25], ![1144, -179, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -152, 157]], ![![-1, -1, 1], ![15, 24, -25], ![25, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [63, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 156], [0, 1]]
 g := ![![[103, 141], [115], [68, 111], [23, 115], [10, 13], [35], [1]], ![[150, 16], [115], [105, 46], [9, 42], [119, 144], [35], [1]]]
 h' := ![![[105, 156], [118, 112], [112, 30], [121, 41], [155, 30], [37, 22], [94, 105], [0, 1]], ![[0, 1], [103, 45], [122, 127], [30, 116], [8, 127], [149, 135], [129, 52], [105, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [116, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [63, 52, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![875, -44, 103]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, -100, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![25, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![25, 1, 0]] 
 ![![157, 0, 0], ![25, 1, 0], ![27, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![25, 1, 0], ![0, 26, 5], ![-220, 27, 25]]]
  hmulB := by decide  
  f := ![![![751, 30, 0], ![-4710, 0, 0]], ![![75, 3, 0], ![-470, 0, 0]], ![![111, -6, -2], ![-696, 63, 0]]]
  g := ![![![1, 0, 0], ![-25, 157, 0], ![-27, 0, 157]], ![![0, 1, 0], ![-5, 26, 5], ![-10, 27, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-54, -5, 1]] ![![157, 0, 0], ![25, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![3925, 157, 0]], ![![-8478, -785, 157], ![-1570, -157, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![25, 1, 0]]], ![![![-54, -5, 1]], ![![-10, -1, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![42, 30, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![42, 30, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![42, 30, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![42, 30, 1], ![-220, 99, 150], ![-6556, 766, 69]]]
  hmulB := by decide  
  f := ![![![-41, -30, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -30, 163]], ![![0, 0, 1], ![-40, -27, 150], ![-58, -8, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [136, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 162], [0, 1]]
 g := ![![[144, 6], [84, 85], [4], [69], [40], [39, 87], [1]], ![[0, 157], [0, 78], [4], [69], [40], [70, 76], [1]]]
 h' := ![![[139, 162], [149, 13], [95, 133], [65, 161], [22, 45], [75, 23], [27, 139], [0, 1]], ![[0, 1], [0, 150], [0, 30], [113, 2], [83, 118], [12, 140], [114, 24], [139, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [40, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [136, 24, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4195, -4184, 3001]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-799, -578, 3001]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![13, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![13, 1, 0]] 
 ![![163, 0, 0], ![13, 1, 0], ![94, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![13, 1, 0], ![0, 14, 5], ![-220, 27, 13]]]
  hmulB := by decide  
  f := ![![![1717, 132, 0], ![-21516, 0, 0]], ![![117, 9, 0], ![-1466, 0, 0]], ![![994, 68, -3], ![-12456, 98, 0]]]
  g := ![![![1, 0, 0], ![-13, 163, 0], ![-94, 0, 163]], ![![0, 1, 0], ![-4, 14, 5], ![-11, 27, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![42, 30, 1]] ![![163, 0, 0], ![13, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![2119, 163, 0]], ![![6846, 4890, 163], ![326, 489, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![13, 1, 0]]], ![![![42, 30, 1]], ![![2, 3, 1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [83, 10, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 160, 128], [101, 6, 39], [0, 1]]
 g := ![![[158, 93, 29], [42, 46, 49], [139, 16, 18], [36, 130], [18, 122], [159, 13, 1], []], ![[122, 32, 42, 29], [159, 153, 137, 31], [108, 25, 117, 14], [53, 115], [128, 58], [35, 134, 18, 99], [112, 18]], ![[36, 50, 111, 80], [98, 150, 75, 46], [14, 83, 89, 10], [109, 12], [25, 4], [81, 84, 21, 74], [34, 18]]]
 h' := ![![[79, 160, 128], [21, 133, 14], [153, 78, 160], [142, 70, 39], [25, 24, 56], [163, 3, 17], [0, 0, 1], [0, 1]], ![[101, 6, 39], [156, 95, 74], [145, 110, 89], [87, 54, 9], [12, 95, 68], [68, 32, 152], [118, 121, 6], [79, 160, 128]], ![[0, 1], [27, 106, 79], [132, 146, 85], [71, 43, 119], [10, 48, 43], [158, 132, 165], [31, 46, 160], [101, 6, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 57], []]
 b := ![[], [37, 37, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [83, 10, 154, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5697873, 998994, -131429]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34119, 5982, -787]
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


def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![32, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![32, 1, 0]] 
 ![![173, 0, 0], ![32, 1, 0], ![31, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![32, 1, 0], ![0, 33, 5], ![-220, 27, 32]]]
  hmulB := by decide  
  f := ![![![4417, 138, 0], ![-23874, 0, 0]], ![![800, 25, 0], ![-4324, 0, 0]], ![![763, 4, -3], ![-4124, 104, 0]]]
  g := ![![![1, 0, 0], ![-32, 173, 0], ![-31, 0, 173]], ![![0, 1, 0], ![-7, 33, 5], ![-12, 27, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![70, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![70, 1, 0]] 
 ![![173, 0, 0], ![70, 1, 0], ![44, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![70, 1, 0], ![0, 71, 5], ![-220, 27, 70]]]
  hmulB := by decide  
  f := ![![![7631, 109, 0], ![-18857, 0, 0]], ![![3010, 43, 0], ![-7438, 0, 0]], ![![1868, -16, -3], ![-4616, 104, 0]]]
  g := ![![![1, 0, 0], ![-70, 173, 0], ![-44, 0, 173]], ![![0, 1, 0], ![-30, 71, 5], ![-30, 27, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![32, 1, 0]] ![![173, 0, 0], ![70, 1, 0]]
  ![![173, 0, 0], ![-71, -14, 1]] where
 M := ![![![29929, 0, 0], ![12110, 173, 0]], ![![5536, 173, 0], ![2240, 103, 5]]]
 hmul := by decide  
 g := ![![![![173, 0, 0], ![0, 0, 0]], ![![70, 1, 0], ![0, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![15, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-71, -14, 1]] ![![173, 0, 0], ![70, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![12110, 173, 0]], ![![-12283, -2422, 173], ![-5190, -1038, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![70, 1, 0]]], ![![![-71, -14, 1]], ![![-30, -6, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![9, 15, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![9, 15, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![9, 15, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![9, 15, 1], ![-220, 51, 75], ![-3256, 361, 36]]]
  hmulB := by decide  
  f := ![![![-8, -15, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -15, 179]], ![![0, 0, 1], ![-5, -6, 75], ![-20, -1, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [42, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 178], [0, 1]]
 g := ![![[9, 81], [81, 13], [64], [107], [95, 139], [124, 42], [1]], ![[0, 98], [0, 166], [64], [107], [0, 40], [0, 137], [1]]]
 h' := ![![[159, 178], [178, 170], [176, 152], [0, 171], [127, 69], [162, 26], [137, 159], [0, 1]], ![[0, 1], [0, 9], [0, 27], [160, 8], [0, 110], [0, 153], [0, 20], [159, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [3, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [42, 20, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-424053, -200364, 180929]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11466, -16281, 180929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-75, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-75, 1, 0]] 
 ![![179, 0, 0], ![104, 1, 0], ![143, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-75, 1, 0], ![0, -74, 5], ![-220, 27, -75]]]
  hmulB := by decide  
  f := ![![![7951, -106, 0], ![18974, 0, 0]], ![![4576, -61, 0], ![10920, 0, 0]], ![![6367, -70, -1], ![15194, 36, 0]]]
  g := ![![![1, 0, 0], ![-104, 179, 0], ![-143, 0, 179]], ![![-1, 1, 0], ![39, -74, 5], ![43, 27, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![9, 15, 1]] ![![179, 0, 0], ![-75, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-13425, 179, 0]], ![![1611, 2685, 179], ![-895, -1074, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-75, 1, 0]]], ![![![9, 15, 1]], ![![-5, -6, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1744652875557672001761, 315456384932773117631, -111840175035424231193]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-1744652875557672001761, 315456384932773117631, -111840175035424231193]] 
 ![![181, 0, 0], ![36, 1, 0], ![168, 0, 1]] where
  M :=![![![-1744652875557672001761, 315456384932773117631, -111840175035424231193], ![24604838507793330862460, -4448881216581353126341, 1577281924663865588155], ![-74321372386768752051312, 13438290094743540348529, -4764337601514126243972]]]
  hmulB := by decide  
  f := ![![![-899631592457, -63467205235, 106894008]], ![![-179062176852, -17928353856, -1731977027]], ![![-757848724004, -68402256117, -4855178237]]]
  g := ![![![31425782722727992287, 315456384932773117631, -111840175035424231193], ![-443197795794515886184, -4448881216581353126341, 1577281924663865588155], ![1338723211363740355740, 13438290094743540348529, -4764337601514126243972]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30651966261, 2869696582, 1669579800]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-30651966261, 2869696582, 1669579800]] 
 ![![181, 0, 0], ![45, 1, 0], ![129, 0, 1]] where
  M :=![![![-30651966261, 2869696582, 1669579800], ![-367307556000, 17296384921, 14348482910], ![-557871736840, 4020296514, 14426688339]]]
  hmulB := by decide  
  f := ![![![191844398822384560479, -34688012366222740098, 12298097486586217820]], ![![32748157458333355255, -5921301314287478469, 2099305663344011610]], ![![181880698663350302251, -32886443196356580328, 11659379042706268179]]]
  g := ![![![-2072729871, 2869696582, 1669579800], ![-16555796535, 17296384921, 14348482910], ![-14363689921, 4020296514, 14426688339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, 3, 2]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-43, 3, 2]] 
 ![![181, 0, 0], ![99, 1, 0], ![11, 0, 1]] where
  M :=![![![-43, 3, 2], ![-440, 14, 15], ![-572, -7, 11]]]
  hmulB := by decide  
  f := ![![![-259, 47, -17]], ![![-121, 22, -8]], ![![-77, 14, -5]]]
  g := ![![![-2, 3, 2], ![-11, 14, 15], ![0, -7, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-1744652875557672001761, 315456384932773117631, -111840175035424231193]] ![![-30651966261, 2869696582, 1669579800]]
  ![![-259, 47, -17]] where
 M := ![![![-259, 47, -17]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-259, 47, -17]] ![![-43, 3, 2]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![31, 91, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![31, 91, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![31, 91, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![31, 91, 1], ![-220, 149, 455], ![-19976, 2413, 58]]]
  hmulB := by decide  
  f := ![![![-30, -91, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -91, 191]], ![![0, 0, 1], ![-75, -216, 455], ![-114, -15, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [49, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 190], [0, 1]]
 g := ![![[101, 39], [122, 49], [57, 109], [174, 1], [90, 39], [0, 98], [1]], ![[0, 152], [0, 142], [0, 82], [0, 190], [180, 152], [138, 93], [1]]]
 h' := ![![[17, 190], [134, 82], [72, 7], [69, 142], [174, 1], [0, 82], [142, 17], [0, 1]], ![[0, 1], [0, 109], [0, 184], [0, 49], [0, 190], [57, 109], [49, 174], [17, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [146, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [49, 174, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4128, -1052, 2547]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-435, -1219, 2547]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-73, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-73, 1, 0]] 
 ![![191, 0, 0], ![118, 1, 0], ![133, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-73, 1, 0], ![0, -72, 5], ![-220, 27, -73]]]
  hmulB := by decide  
  f := ![![![12630, -173, 0], ![33043, 0, 0]], ![![7812, -107, 0], ![20438, 0, 0]], ![![8810, -63, -4], ![23049, 153, 0]]]
  g := ![![![1, 0, 0], ![-118, 191, 0], ![-133, 0, 191]], ![![-1, 1, 0], ![41, -72, 5], ![33, 27, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![31, 91, 1]] ![![191, 0, 0], ![-73, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13943, 191, 0]], ![![5921, 17381, 191], ![-2483, -6494, 382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-73, 1, 0]]], ![![![31, 91, 1]], ![![-13, -34, 2]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-27, -77, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-27, -77, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![166, 116, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-27, -77, 1], ![-220, -77, -385], ![16984, -2123, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -116, 193]], ![![-1, -1, 1], ![330, 231, -385], ![88, -11, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [20, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [177, 192], [0, 1]]
 g := ![![[78, 165], [50], [14], [150], [7], [112], [177, 1]], ![[140, 28], [50], [14], [150], [7], [112], [161, 192]]]
 h' := ![![[177, 192], [109, 101], [181, 67], [70, 20], [102, 27], [186, 59], [127, 43], [0, 1]], ![[0, 1], [37, 92], [74, 126], [136, 173], [56, 166], [14, 134], [18, 150], [177, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [35, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [20, 16, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9836, -6299, 5561]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4834, -3375, 5561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-1, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-1, 1, 0]] 
 ![![193, 0, 0], ![192, 1, 0], ![0, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-1, 1, 0], ![0, 0, 5], ![-220, 27, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -3], ![0, 116, 0]]]
  g := ![![![1, 0, 0], ![-192, 193, 0], ![0, 0, 193]], ![![-1, 1, 0], ![0, 0, 5], ![-28, 27, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-27, -77, 1]] ![![193, 0, 0], ![-1, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-193, 193, 0]], ![![-5211, -14861, 193], ![-193, 0, -386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-1, 1, 0]]], ![![![-27, -77, 1]], ![![-1, 0, -2]]]]
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


lemma PB254I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB254I3 : PrimesBelowBoundCertificateInterval O 137 193 254 where
  m := 11
  g := ![3, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB254I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
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
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I151N1, I157N1, I163N1, I173N0, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [], [I151N1], [I157N1], [I163N1], [], [I173N0, I173N1, I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
