
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [133, 20, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 44, 10], [50, 94, 129], [0, 1]]
 g := ![![[71, 28, 9], [133, 33, 52], [9, 7], [55, 57, 55], [95, 57], [59, 1], []], ![[49, 8, 5, 32], [116, 138, 64, 59], [82, 112], [4, 18, 96, 58], [136, 100], [111, 79], [108, 100]], ![[34, 58, 127, 37], [62, 44, 93, 136], [78, 36], [86, 80, 87, 37], [76, 16], [135, 129], [128, 100]]]
 h' := ![![[9, 44, 10], [103, 107, 136], [117, 101, 82], [52, 17, 29], [91, 138, 65], [76, 77, 125], [0, 0, 1], [0, 1]], ![[50, 94, 129], [130, 62, 93], [61, 126, 100], [79, 21, 116], [68, 76, 123], [15, 101, 10], [34, 66, 94], [9, 44, 10]], ![[0, 1], [97, 109, 49], [8, 51, 96], [42, 101, 133], [69, 64, 90], [13, 100, 4], [71, 73, 44], [50, 94, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 129], []]
 b := ![[], [78, 20, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [133, 20, 80, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-257289, 121208, -862356]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1851, 872, -6204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-63, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-63, 1, 0]] 
 ![![149, 0, 0], ![86, 1, 0], ![109, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-63, 1, 0], ![-1, -59, 11], ![106, -23, -67]]]
  hmulB := by decide  
  f := ![![![3641, 214760, -40040], ![0, 542360, 0]], ![![2101, 123900, -23100], ![1, 312900, 0]], ![![2683, 157106, -29291], ![46, 396760, 0]]]
  g := ![![![1, 0, 0], ![-86, 149, 0], ![-109, 0, 149]], ![![-1, 1, 0], ![26, -59, 11], ![63, -23, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-61, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-61, 1, 0]] 
 ![![149, 0, 0], ![88, 1, 0], ![36, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-61, 1, 0], ![-1, -57, 11], ![106, -23, -65]]]
  hmulB := by decide  
  f := ![![![-8259, -477776, 92202], ![298, -1248918, 0]], ![![-4888, -282151, 54450], ![150, -737550, 0]], ![![-1984, -115436, 22277], ![100, -301752, 0]]]
  g := ![![![1, 0, 0], ![-88, 149, 0], ![-36, 0, 149]], ![![-1, 1, 0], ![31, -57, 11], ![30, -23, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-25, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-25, 1, 0]] 
 ![![149, 0, 0], ![124, 1, 0], ![47, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-25, 1, 0], ![-1, -21, 11], ![106, -23, -29]]]
  hmulB := by decide  
  f := ![![![-1547, -33034, 17303], ![149, -234377, 0]], ![![-1283, -27490, 14399], ![150, -195041, 0]], ![![-491, -10420, 5458], ![29, -73931, 0]]]
  g := ![![![1, 0, 0], ![-124, 149, 0], ![-47, 0, 149]], ![![-1, 1, 0], ![14, -21, 11], ![29, -23, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-63, 1, 0]] ![![149, 0, 0], ![-61, 1, 0]]
  ![![149, 0, 0], ![-30, -38, 1]] where
 M := ![![![22201, 0, 0], ![-9089, 149, 0]], ![![-9387, 149, 0], ![3842, -120, 11]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![-31, 39, -1], ![149, 0, 0]]], ![![![-33, 39, -1], ![149, 0, 0]], ![![28, 2, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-30, -38, 1]] ![![149, 0, 0], ![-25, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3725, 149, 0]], ![![-4470, -5662, 149], ![894, 745, -447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-25, 1, 0]]], ![![![-30, -38, 1]], ![![6, 5, -3]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![26, -14, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![26, -14, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![26, 137, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![26, -14, 1], ![120, -53, -158], ![-1559, 340, 62]]]
  hmulB := by decide  
  f := ![![![-25, 14, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -137, 151]], ![![0, -1, 1], ![28, 143, -158], ![-21, -54, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [145, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 150], [0, 1]]
 g := ![![[129, 25], [41, 125], [10, 25], [59], [140, 100], [59], [1]], ![[0, 126], [0, 26], [32, 126], [59], [77, 51], [59], [1]]]
 h' := ![![[19, 150], [95, 146], [60, 124], [29, 5], [85, 132], [88, 141], [6, 19], [0, 1]], ![[0, 1], [0, 5], [0, 27], [124, 146], [26, 19], [49, 10], [65, 132], [19, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [73, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [145, 132, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16067, 6642, -17861]
  a := ![-3, 9, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2969, 16249, -17861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![7, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![7, 1, 0]] 
 ![![151, 0, 0], ![7, 1, 0], ![89, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![7, 1, 0], ![-1, 11, 11], ![106, -23, 3]]]
  hmulB := by decide  
  f := ![![![-3570, 39203, 39204], ![151, -538164, 0]], ![![-172, 1814, 1815], ![152, -24915, 0]], ![![-2107, 23106, 23107], ![150, -317196, 0]]]
  g := ![![![1, 0, 0], ![-7, 151, 0], ![-89, 0, 151]], ![![0, 1, 0], ![-7, 11, 11], ![0, -23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![26, -14, 1]] ![![151, 0, 0], ![7, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![1057, 151, 0]], ![![3926, -2114, 151], ![302, -151, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![7, 1, 0]]], ![![![26, -14, 1]], ![![2, -1, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-53, 25, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-53, 25, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![104, 25, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-53, 25, 1], ![81, 24, 271], ![2575, -557, -173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -25, 157]], ![![-1, 0, 1], ![-179, -43, 271], ![131, 24, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [90, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 156], [0, 1]]
 g := ![![[6, 82], [124], [62, 90], [134, 90], [27, 106], [51], [1]], ![[0, 75], [124], [132, 67], [47, 67], [92, 51], [51], [1]]]
 h' := ![![[88, 156], [147, 125], [72, 81], [29, 54], [82, 54], [56, 109], [67, 88], [0, 1]], ![[0, 1], [0, 32], [135, 76], [71, 103], [124, 103], [71, 48], [118, 69], [88, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [49, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [90, 69, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![639096, -116701, -108646]
  a := ![1, -67, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76040, 16557, -108646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![43, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![43, 1, 0]] 
 ![![157, 0, 0], ![43, 1, 0], ![16, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![43, 1, 0], ![-1, 47, 11], ![106, -23, 39]]]
  hmulB := by decide  
  f := ![![![-546, 23687, 5544], ![157, -79128, 0]], ![![-181, 6485, 1518], ![158, -21666, 0]], ![![-54, 2414, 565], ![10, -8064, 0]]]
  g := ![![![1, 0, 0], ![-43, 157, 0], ![-16, 0, 157]], ![![0, 1, 0], ![-14, 47, 11], ![3, -23, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-53, 25, 1]] ![![157, 0, 0], ![43, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![6751, 157, 0]], ![![-8321, 3925, 157], ![-2198, 1099, 314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![43, 1, 0]]], ![![![-53, 25, 1]], ![![-14, 7, 2]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![11, 52, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![11, 52, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![11, 52, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![11, 52, 1], ![54, 196, 568], ![5437, -1178, -217]]]
  hmulB := by decide  
  f := ![![![-10, -52, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -52, 163]], ![![0, 0, 1], ![-38, -180, 568], ![48, 62, -217]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [155, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 162], [0, 1]]
 g := ![![[137, 61], [46, 56], [21], [36], [54], [87, 69], [1]], ![[0, 102], [134, 107], [21], [36], [54], [79, 94], [1]]]
 h' := ![![[118, 162], [42, 77], [45, 43], [23, 64], [86, 6], [44, 124], [8, 118], [0, 1]], ![[0, 1], [0, 86], [66, 120], [77, 99], [142, 157], [6, 39], [77, 45], [118, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [98, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [155, 45, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8761, 3602, -23572]
  a := ![3, -10, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1537, 7542, -23572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-79, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-79, 1, 0]] 
 ![![163, 0, 0], ![84, 1, 0], ![54, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-79, 1, 0], ![-1, -75, 11], ![106, -23, -83]]]
  hmulB := by decide  
  f := ![![![2179, 163350, -23958], ![0, 355014, 0]], ![![1123, 84150, -12342], ![1, 182886, 0]], ![![718, 54116, -7937], ![-8, 117612, 0]]]
  g := ![![![1, 0, 0], ![-84, 163, 0], ![-54, 0, 163]], ![![-1, 1, 0], ![35, -75, 11], ![40, -23, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![11, 52, 1]] ![![163, 0, 0], ![-79, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-12877, 163, 0]], ![![1793, 8476, 163], ![-815, -3912, 489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-79, 1, 0]]], ![![![11, 52, 1]], ![![-5, -24, 3]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-21, -3, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-21, -3, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![146, 164, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-21, -3, 1], ![109, -56, -37], ![-393, 87, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -164, 167]], ![![-1, -1, 1], ![33, 36, -37], ![23, 29, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [72, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 166], [0, 1]]
 g := ![![[12, 58], [13, 49], [95, 85], [66], [42], [161, 6], [1]], ![[0, 109], [95, 118], [135, 82], [66], [42], [154, 161], [1]]]
 h' := ![![[138, 166], [66, 152], [7, 7], [71, 98], [67, 20], [98, 83], [95, 138], [0, 1]], ![[0, 1], [0, 15], [138, 160], [68, 69], [155, 147], [29, 84], [101, 29], [138, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [99, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [72, 29, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2662, -407, -2926]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2574, 2871, -2926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![37, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![37, 1, 0]] 
 ![![167, 0, 0], ![37, 1, 0], ![29, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![37, 1, 0], ![-1, 41, 11], ![106, -23, 33]]]
  hmulB := by decide  
  f := ![![![19035, -777358, -208560], ![-334, 3166320, 0]], ![![4200, -172200, -46200], ![1, 701400, 0]], ![![3280, -134991, -36217], ![57, 549840, 0]]]
  g := ![![![1, 0, 0], ![-37, 167, 0], ![-29, 0, 167]], ![![0, 1, 0], ![-11, 41, 11], ![0, -23, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-21, -3, 1]] ![![167, 0, 0], ![37, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![6179, 167, 0]], ![![-3507, -501, 167], ![-668, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![37, 1, 0]]], ![![![-21, -3, 1]], ![![-4, -1, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-72, 63, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-72, 63, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![101, 63, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-72, 63, 1], ![43, 157, 689], ![6603, -1431, -344]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -63, 173]], ![![-1, 0, 1], ![-402, -250, 689], ![239, 117, -344]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [139, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 172], [0, 1]]
 g := ![![[149, 117], [113], [111, 92], [72, 126], [157], [54, 152], [1]], ![[0, 56], [113], [121, 81], [18, 47], [157], [63, 21], [1]]]
 h' := ![![[49, 172], [22, 109], [141, 74], [26, 145], [139, 105], [106, 147], [34, 49], [0, 1]], ![[0, 1], [0, 64], [134, 99], [38, 28], [94, 68], [43, 26], [13, 124], [49, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [26, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [139, 124, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49696, -5424, 2616]
  a := ![-1, 24, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1240, -984, 2616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![3, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![3, 1, 0]] 
 ![![173, 0, 0], ![3, 1, 0], ![171, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![3, 1, 0], ![-1, 7, 11], ![106, -23, -1]]]
  hmulB := by decide  
  f := ![![![-466, 3247, 5104], ![173, -80272, 0]], ![![-8, 56, 88], ![1, -1384, 0]], ![![-459, 3210, 5045], ![78, -79344, 0]]]
  g := ![![![1, 0, 0], ![-3, 173, 0], ![-171, 0, 173]], ![![0, 1, 0], ![-11, 7, 11], ![2, -23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-72, 63, 1]] ![![173, 0, 0], ![3, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![519, 173, 0]], ![![-12456, 10899, 173], ![-173, 346, 692]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![3, 1, 0]]], ![![![-72, 63, 1]], ![![-1, 2, 4]]]]
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
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-38, -69, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-38, -69, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![141, 110, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-38, -69, 1], ![175, -337, -763], ![-7389, 1605, 218]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-141, -110, 179]], ![![-1, -1, 1], ![602, 467, -763], ![-213, -125, 218]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [83, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 178], [0, 1]]
 g := ![![[151, 110], [118, 5], [45], [153], [41, 76], [113, 9], [1]], ![[0, 69], [103, 174], [45], [153], [171, 103], [86, 170], [1]]]
 h' := ![![[176, 178], [51, 17], [41, 30], [14, 89], [177, 42], [108, 75], [96, 176], [0, 1]], ![[0, 1], [0, 162], [130, 149], [105, 90], [51, 137], [62, 104], [105, 3], [176, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [138, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [83, 3, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5629, 1494, -3088]
  a := ![1, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2401, 1906, -3088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![47, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![47, 1, 0]] 
 ![![179, 0, 0], ![47, 1, 0], ![140, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![47, 1, 0], ![-1, 51, 11], ![106, -23, 43]]]
  hmulB := by decide  
  f := ![![![-3326, 167279, 36080], ![179, -587120, 0]], ![![-908, 43910, 9471], ![180, -154119, 0]], ![![-2589, 130833, 28219], ![93, -459200, 0]]]
  g := ![![![1, 0, 0], ![-47, 179, 0], ![-140, 0, 179]], ![![0, 1, 0], ![-22, 51, 11], ![-27, -23, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-38, -69, 1]] ![![179, 0, 0], ![47, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![8413, 179, 0]], ![![-6802, -12351, 179], ![-1611, -3580, -716]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![47, 1, 0]]], ![![![-38, -69, 1]], ![![-9, -20, -4]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-43, 73, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-43, 73, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![138, 73, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-43, 73, 1], ![33, 226, 799], ![7663, -1661, -355]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-138, -73, 181]], ![![-1, 0, 1], ![-609, -321, 799], ![313, 134, -355]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [173, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 180], [0, 1]]
 g := ![![[117, 39], [145], [12, 126], [45], [109, 180], [60, 56], [1]], ![[59, 142], [145], [117, 55], [45], [78, 1], [167, 125], [1]]]
 h' := ![![[31, 180], [59, 138], [96, 114], [1, 44], [148, 100], [118, 19], [8, 31], [0, 1]], ![[0, 1], [174, 43], [10, 67], [98, 137], [171, 81], [164, 162], [64, 150], [31, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [60, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [173, 150, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5472, 1242, -7161]
  a := ![-2, 9, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5490, 2895, -7161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-75, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-75, 1, 0]] 
 ![![181, 0, 0], ![106, 1, 0], ![174, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-75, 1, 0], ![-1, -71, 11], ![106, -23, -79]]]
  hmulB := by decide  
  f := ![![![-9470, -677767, 105006], ![181, -1727826, 0]], ![![-5514, -396891, 61490], ![182, -1011790, 0]], ![![-9030, -651556, 100945], ![352, -1661004, 0]]]
  g := ![![![1, 0, 0], ![-106, 181, 0], ![-174, 0, 181]], ![![-1, 1, 0], ![31, -71, 11], ![90, -23, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-43, 73, 1]] ![![181, 0, 0], ![-75, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-13575, 181, 0]], ![![-7783, 13213, 181], ![3258, -5249, 724]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-75, 1, 0]]], ![![![-43, 73, 1]], ![![18, -29, 4]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [22, 89, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 109, 165], [49, 81, 26], [0, 1]]
 g := ![![[114, 27, 25], [111, 116, 48], [104, 176, 52], [164, 135, 54], [66, 173, 18], [105, 24, 1], []], ![[15, 139, 41, 189], [169, 169, 158, 131], [95, 54, 174, 91], [166, 21, 34, 19], [130, 79, 97, 124], [76, 84, 185, 168], [51, 103]], ![[89, 131, 48, 138], [164, 97, 63, 8], [147, 114, 89, 80], [117, 118, 146, 32], [132, 73, 89, 79], [167, 24, 170, 59], [190, 103]]]
 h' := ![![[166, 109, 165], [41, 0, 186], [4, 110, 96], [21, 52, 166], [76, 3, 93], [173, 59, 171], [0, 0, 1], [0, 1]], ![[49, 81, 26], [43, 155, 168], [157, 37, 141], [68, 140, 61], [2, 118, 6], [43, 175, 93], [76, 160, 81], [166, 109, 165]], ![[0, 1], [150, 36, 28], [16, 44, 145], [58, 190, 155], [182, 70, 92], [62, 148, 118], [131, 31, 109], [49, 81, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 75], []]
 b := ![[], [25, 135, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [22, 89, 167, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![948697, -185270, -118420]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4967, -970, -620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![43, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![43, 1, 0]] 
 ![![193, 0, 0], ![43, 1, 0], ![132, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![43, 1, 0], ![-1, 47, 11], ![106, -23, 39]]]
  hmulB := by decide  
  f := ![![![-1500, 68525, 16038], ![193, -281394, 0]], ![![-367, 15227, 3564], ![194, -62532, 0]], ![![-1019, 46867, 10969], ![101, -192456, 0]]]
  g := ![![![1, 0, 0], ![-43, 193, 0], ![-132, 0, 193]], ![![0, 1, 0], ![-18, 47, 11], ![-21, -23, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![67, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![67, 1, 0]] 
 ![![193, 0, 0], ![67, 1, 0], ![164, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![67, 1, 0], ![-1, 71, 11], ![106, -23, 63]]]
  hmulB := by decide  
  f := ![![![-23432, 1649469, 255552], ![579, -4483776, 0]], ![![-8131, 572543, 88704], ![194, -1556352, 0]], ![![-19933, 1401621, 217153], ![555, -3810048, 0]]]
  g := ![![![1, 0, 0], ![-67, 193, 0], ![-164, 0, 193]], ![![0, 1, 0], ![-34, 71, 11], ![-45, -23, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![83, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![83, 1, 0]] 
 ![![193, 0, 0], ![83, 1, 0], ![133, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![83, 1, 0], ![-1, 87, 11], ![106, -23, 79]]]
  hmulB := by decide  
  f := ![![![-3282, 278399, 35200], ![193, -617600, 0]], ![![-1459, 119711, 15136], ![194, -265568, 0]], ![![-2269, 191850, 24257], ![150, -425600, 0]]]
  g := ![![![1, 0, 0], ![-83, 193, 0], ![-133, 0, 193]], ![![0, 1, 0], ![-45, 87, 11], ![-44, -23, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![43, 1, 0]] ![![193, 0, 0], ![67, 1, 0]]
  ![![193, 0, 0], ![-54, 63, 1]] where
 M := ![![![37249, 0, 0], ![12931, 193, 0]], ![![8299, 193, 0], ![2880, 114, 11]]]
 hmul := by decide  
 g := ![![![![193, 0, 0], ![0, 0, 0]], ![![67, 1, 0], ![0, 0, 0]]], ![![![43, 1, 0], ![0, 0, 0]], ![![18, -3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-54, 63, 1]] ![![193, 0, 0], ![83, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![16019, 193, 0]], ![![-10422, 12159, 193], ![-4439, 5404, 772]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![83, 1, 0]]], ![![![-54, 63, 1]], ![![-23, 28, 4]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB245I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB245I3 : PrimesBelowBoundCertificateInterval O 137 193 245 where
  m := 11
  g := ![1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB245I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![6967871]
    · exact ![193, 193, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
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
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I149N0, I149N1, I149N2, I151N1, I157N1, I163N1, I167N1, I173N1, I179N1, I181N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N1], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [I181N1], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
