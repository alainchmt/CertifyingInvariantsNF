
import IdealArithmetic.Examples.NF3_1_649415_1.RI3_1_649415_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![44, -32, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![44, -32, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![44, 107, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![44, -32, 1], ![93, 84, -159], ![-4958, -223, 20]]]
  hmulB := by decide  
  f := ![![![-43, 32, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -107, 139]], ![![0, -1, 1], ![51, 123, -159], ![-42, -17, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [116, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 138], [0, 1]]
 g := ![![[43, 6], [104, 63], [57], [54, 125], [116], [117], [1]], ![[0, 133], [0, 76], [57], [108, 14], [116], [117], [1]]]
 h' := ![![[16, 138], [29, 59], [2, 52], [130, 125], [0, 60], [23, 106], [23, 16], [0, 1]], ![[0, 1], [0, 80], [0, 87], [45, 14], [126, 79], [51, 33], [1, 123], [16, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [32, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [116, 123, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1524, 825, -395]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 310, -395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![20, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![20, 1, 0]] 
 ![![139, 0, 0], ![20, 1, 0], ![119, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![20, 1, 0], ![2, 19, 5], ![157, 8, 21]]]
  hmulB := by decide  
  f := ![![![373, 3723, 980], ![139, -27244, 0]], ![![36, 531, 140], ![140, -3892, 0]], ![![313, 3187, 839], ![163, -23324, 0]]]
  g := ![![![1, 0, 0], ![-20, 139, 0], ![-119, 0, 139]], ![![0, 1, 0], ![-7, 19, 5], ![-18, 8, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![44, -32, 1]] ![![139, 0, 0], ![20, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2780, 139, 0]], ![![6116, -4448, 139], ![973, -556, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![20, 1, 0]]], ![![![44, -32, 1]], ![![7, -4, -1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [121, 0, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 109, 93], [101, 39, 56], [0, 1]]
 g := ![![[15, 60, 95], [101, 68], [99, 39, 63], [7, 107], [32, 0, 28], [74, 1], []], ![[115, 6, 110, 32], [77, 69], [89, 87, 15, 40], [75, 37], [12, 102, 35, 122], [110, 31], [81, 7]], ![[62, 12, 105, 135], [87, 116], [139, 27, 123, 70], [50, 36], [87, 91, 113, 131], [89, 110], [118, 7]]]
 h' := ![![[122, 109, 93], [51, 18, 63], [90, 117, 98], [51, 55, 130], [2, 47, 133], [135, 28, 112], [0, 0, 1], [0, 1]], ![[101, 39, 56], [40, 49, 108], [87, 26, 101], [31, 120, 53], [100, 58, 22], [91, 65, 118], [17, 121, 39], [122, 109, 93]], ![[0, 1], [106, 82, 127], [59, 6, 99], [76, 123, 115], [100, 44, 143], [44, 56, 68], [95, 28, 109], [101, 39, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 145], []]
 b := ![[], [44, 136, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [121, 0, 75, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8435784, 1463776, 91486]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56616, 9824, 614]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6046483, -789231, -404331]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-6046483, -789231, -404331]] 
 ![![151, 0, 0], ![61, 1, 0], ![114, 0, 1]] where
  M :=![![![-6046483, -789231, -404331], ![-65058429, -8491900, -4350486], ![-150595113, -19656771, -10070362]]]
  hmulB := by decide  
  f := ![![![-27094, -3579, 2634]], ![![-8254, -1462, 963]], ![![-23025, -2316, 1925]]]
  g := ![![![584042, -789231, -404331], ![6284125, -8491900, -4350486], ![14546286, -19656771, -10070362]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![849, 16, -41]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![849, 16, -41]] 
 ![![151, 0, 0], ![104, 1, 0], ![123, 0, 1]] where
  M :=![![![849, 16, -41], ![-6405, 505, 39], ![-194, -1225, 537]]]
  hmulB := by decide  
  f := ![![![-318960, -41633, -21329]], ![![-242409, -31641, -16210]], ![![-312425, -40780, -20892]]]
  g := ![![![28, 16, -41], ![-422, 505, 39], ![405, -1225, 537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 1, -2]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![39, 1, -2]] 
 ![![151, 0, 0], ![137, 1, 0], ![49, 0, 1]] where
  M :=![![![39, 1, -2], ![-312, 22, 3], ![25, -58, 24]]]
  hmulB := by decide  
  f := ![![![-702, -92, -47]], ![![-687, -90, -46]], ![![-344, -45, -23]]]
  g := ![![![0, 1, -2], ![-23, 22, 3], ![45, -58, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-6046483, -789231, -404331]] ![![849, 16, -41]]
  ![![702, 92, 47]] where
 M := ![![![702, 92, 47]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![702, 92, 47]] ![![39, 1, -2]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![60, 43, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![60, 43, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![60, 43, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![60, 43, 1], ![243, 25, 216], ![6817, 377, 111]]]
  hmulB := by decide  
  f := ![![![-59, -43, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -43, 157]], ![![0, 0, 1], ![-81, -59, 216], ![1, -28, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [59, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 156], [0, 1]]
 g := ![![[144, 58], [82], [107, 132], [104, 144], [148, 146], [10], [1]], ![[42, 99], [82], [86, 25], [24, 13], [32, 11], [10], [1]]]
 h' := ![![[139, 156], [19, 23], [124, 32], [144, 140], [60, 12], [65, 60], [98, 139], [0, 1]], ![[0, 1], [76, 134], [19, 125], [136, 17], [1, 145], [84, 97], [108, 18], [139, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [89, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [59, 18, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1087185, 579249, 156162]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52755, -39081, 156162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-59, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-59, 1, 0]] 
 ![![157, 0, 0], ![98, 1, 0], ![46, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-59, 1, 0], ![2, -60, 5], ![157, 8, -58]]]
  hmulB := by decide  
  f := ![![![32021, -1179956, 98340], ![-19468, -3087876, 0]], ![![20010, -736483, 61380], ![-12088, -1927332, 0]], ![![9406, -345720, 28813], ![-5640, -904728, 0]]]
  g := ![![![1, 0, 0], ![-98, 157, 0], ![-46, 0, 157]], ![![-1, 1, 0], ![36, -60, 5], ![13, 8, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![60, 43, 1]] ![![157, 0, 0], ![-59, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-9263, 157, 0]], ![![9420, 6751, 157], ![-3297, -2512, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-59, 1, 0]]], ![![![60, 43, 1]], ![![-21, -16, 1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![55, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![55, 1, 0]] 
 ![![163, 0, 0], ![55, 1, 0], ![91, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![55, 1, 0], ![2, 54, 5], ![157, 8, 56]]]
  hmulB := by decide  
  f := ![![![-20716, -658787, -61005], ![-10921, 1988763, 0]], ![![-7022, -222242, -20580], ![-3585, 670908, 0]], ![![-11562, -367789, -34058], ![-6107, 1110291, 0]]]
  g := ![![![1, 0, 0], ![-55, 163, 0], ![-91, 0, 163]], ![![0, 1, 0], ![-21, 54, 5], ![-33, 8, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-35, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-35, 1, 0]] 
 ![![163, 0, 0], ![128, 1, 0], ![107, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-35, 1, 0], ![2, -36, 5], ![157, 8, -34]]]
  hmulB := by decide  
  f := ![![![16989, -327170, 45445], ![-5542, -1481507, 0]], ![![13330, -256905, 35685], ![-4400, -1163331, 0]], ![![11151, -214768, 29832], ![-3644, -972523, 0]]]
  g := ![![![1, 0, 0], ![-128, 163, 0], ![-107, 0, 163]], ![![-1, 1, 0], ![25, -36, 5], ![17, 8, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-20, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-20, 1, 0]] 
 ![![163, 0, 0], ![143, 1, 0], ![112, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-20, 1, 0], ![2, -21, 5], ![157, 8, -19]]]
  hmulB := by decide  
  f := ![![![-7115, 76599, -18240], ![1467, 594624, 0]], ![![-6239, 67192, -16000], ![1305, 521600, 0]], ![![-4880, 52632, -12533], ![1080, 408576, 0]]]
  g := ![![![1, 0, 0], ![-143, 163, 0], ![-112, 0, 163]], ![![-1, 1, 0], ![15, -21, 5], ![7, 8, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![55, 1, 0]] ![![163, 0, 0], ![-35, 1, 0]]
  ![![163, 0, 0], ![-26, 69, 1]] where
 M := ![![![26569, 0, 0], ![-5705, 163, 0]], ![![8965, 163, 0], ![-1923, 19, 5]]]
 hmul := by decide  
 g := ![![![![163, 0, 0], ![0, 0, 0]], ![![-9, -68, -1], ![163, 0, 0]]], ![![![55, 1, 0], ![0, 0, 0]], ![![-11, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-26, 69, 1]] ![![163, 0, 0], ![-20, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-3260, 163, 0]], ![![-4238, 11247, 163], ![815, -1467, 326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-20, 1, 0]]], ![![![-26, 69, 1]], ![![5, -9, 2]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [165, 1, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 67, 120], [158, 99, 47], [0, 1]]
 g := ![![[60, 89, 108], [153, 92, 94], [20, 159, 14], [1, 3], [43, 58], [129, 111, 1], []], ![[117, 20, 6, 153], [28, 134, 39, 149], [105, 137, 33, 163], [107, 14], [61, 38], [141, 52, 114, 106], [91, 38]], ![[7, 83, 126, 48], [158, 78, 75, 157], [51, 158, 89, 89], [106, 16], [59, 22], [118, 44, 140, 62], [164, 38]]]
 h' := ![![[120, 67, 120], [139, 128, 129], [40, 143, 125], [124, 151, 101], [17, 132, 62], [91, 93, 15], [0, 0, 1], [0, 1]], ![[158, 99, 47], [125, 141, 75], [111, 12, 143], [50, 90, 63], [105, 35, 101], [22, 46, 120], [53, 33, 99], [120, 67, 120]], ![[0, 1], [145, 65, 130], [112, 12, 66], [161, 93, 3], [139, 0, 4], [45, 28, 32], [75, 134, 67], [158, 99, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 27], []]
 b := ![[], [159, 68, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [165, 1, 56, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10128884, -866563, 27889]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60652, -5189, 167]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![2, 41, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![2, 41, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![2, 41, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![2, 41, 1], ![239, -31, 206], ![6503, 361, 51]]]
  hmulB := by decide  
  f := ![![![-1, -41, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -41, 173]], ![![0, 0, 1], ![-1, -49, 206], ![37, -10, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [154, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 172], [0, 1]]
 g := ![![[9, 117], [34], [143, 172], [122, 55], [130], [89, 4], [1]], ![[121, 56], [34], [145, 1], [12, 118], [130], [81, 169], [1]]]
 h' := ![![[171, 172], [133, 64], [122, 131], [69, 80], [12, 125], [134, 86], [19, 171], [0, 1]], ![[0, 1], [5, 109], [33, 42], [82, 93], [108, 48], [135, 87], [23, 2], [171, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [160, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [154, 2, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1804, 825, 210]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -45, 210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-33, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-33, 1, 0]] 
 ![![173, 0, 0], ![140, 1, 0], ![122, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-33, 1, 0], ![2, -34, 5], ![157, 8, -32]]]
  hmulB := by decide  
  f := ![![![18738, -335889, 49400], ![-5363, -1709240, 0]], ![![15166, -271805, 39975], ![-4324, -1383135, 0]], ![![13224, -236870, 34837], ![-3730, -1205360, 0]]]
  g := ![![![1, 0, 0], ![-140, 173, 0], ![-122, 0, 173]], ![![-1, 1, 0], ![24, -34, 5], ![17, 8, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![2, 41, 1]] ![![173, 0, 0], ![-33, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-5709, 173, 0]], ![![346, 7093, 173], ![173, -1384, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-33, 1, 0]]], ![![![2, 41, 1]], ![![1, -8, 1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-54, 42, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-54, 42, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![125, 42, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-54, 42, 1], ![241, -88, 211], ![6660, 369, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -42, 179]], ![![-1, 0, 1], ![-146, -50, 211], ![40, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [57, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 178], [0, 1]]
 g := ![![[152, 22], [110, 12], [70], [135], [110, 42], [120, 172], [1]], ![[0, 157], [141, 167], [70], [135], [129, 137], [87, 7], [1]]]
 h' := ![![[107, 178], [174, 77], [140, 38], [27, 41], [174, 80], [141, 20], [122, 107], [0, 1]], ![[0, 1], [0, 102], [89, 141], [118, 138], [142, 99], [133, 159], [115, 72], [107, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [78, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [57, 72, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43728, 4713, 2810]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1718, -633, 2810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-32, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-32, 1, 0]] 
 ![![179, 0, 0], ![147, 1, 0], ![4, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-32, 1, 0], ![2, -33, 5], ![157, 8, -31]]]
  hmulB := by decide  
  f := ![![![31383, -543099, 82295], ![-8592, -2946161, 0]], ![![25785, -445989, 67580], ![-6980, -2419364, 0]], ![![724, -12137, 1839], ![-65, -65836, 0]]]
  g := ![![![1, 0, 0], ![-147, 179, 0], ![-4, 0, 179]], ![![-1, 1, 0], ![27, -33, 5], ![-5, 8, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-54, 42, 1]] ![![179, 0, 0], ![-32, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-5728, 179, 0]], ![![-9666, 7518, 179], ![1969, -1432, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-32, 1, 0]]], ![![![-54, 42, 1]], ![![11, -8, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![24, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![24, 1, 0]] 
 ![![181, 0, 0], ![24, 1, 0], ![71, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![24, 1, 0], ![2, 23, 5], ![157, 8, 25]]]
  hmulB := by decide  
  f := ![![![-16191, -190883, -41500], ![-3077, 1502300, 0]], ![![-2152, -25298, -5500], ![-361, 199100, 0]], ![![-6357, -74877, -16279], ![-1163, 589300, 0]]]
  g := ![![![1, 0, 0], ![-24, 181, 0], ![-71, 0, 181]], ![![0, 1, 0], ![-5, 23, 5], ![-10, 8, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![59, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![59, 1, 0]] 
 ![![181, 0, 0], ![59, 1, 0], ![40, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![59, 1, 0], ![2, 58, 5], ![157, 8, 60]]]
  hmulB := by decide  
  f := ![![![8094, 274027, 23625], ![4163, -855225, 0]], ![![2608, 89312, 7700], ![1449, -278740, 0]], ![![1762, 60558, 5221], ![1002, -189000, 0]]]
  g := ![![![1, 0, 0], ![-59, 181, 0], ![-40, 0, 181]], ![![0, 1, 0], ![-20, 58, 5], ![-15, 8, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-83, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-83, 1, 0]] 
 ![![181, 0, 0], ![98, 1, 0], ![54, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-83, 1, 0], ![2, -84, 5], ![157, 8, -82]]]
  hmulB := by decide  
  f := ![![![1239, -65936, 3925], ![-724, -142085, 0]], ![![685, -35698, 2125], ![-361, -76925, 0]], ![![410, -19672, 1171], ![-128, -42390, 0]]]
  g := ![![![1, 0, 0], ![-98, 181, 0], ![-54, 0, 181]], ![![-1, 1, 0], ![44, -84, 5], ![21, 8, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![24, 1, 0]] ![![181, 0, 0], ![59, 1, 0]]
  ![![181, 0, 0], ![-6, -56, 1]] where
 M := ![![![32761, 0, 0], ![10679, 181, 0]], ![![4344, 181, 0], ![1418, 82, 5]]]
 hmul := by decide  
 g := ![![![![181, 0, 0], ![0, 0, 0]], ![![59, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![8, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-6, -56, 1]] ![![181, 0, 0], ![-83, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-15023, 181, 0]], ![![-1086, -10136, 181], ![543, 4706, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-83, 1, 0]]], ![![![-6, -56, 1]], ![![3, 26, -2]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![48, -18, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![48, -18, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![48, 173, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![48, -18, 1], ![121, 74, -89], ![-2760, -111, 38]]]
  hmulB := by decide  
  f := ![![![-47, 18, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -173, 191]], ![![0, -1, 1], ![23, 81, -89], ![-24, -35, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [131, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 190], [0, 1]]
 g := ![![[123, 177], [81, 130], [152, 184], [102, 30], [180, 92], [135, 177], [1]], ![[134, 14], [88, 61], [62, 7], [133, 161], [135, 99], [146, 14], [1]]]
 h' := ![![[122, 190], [85, 122], [143, 43], [8, 39], [104, 139], [78, 130], [60, 122], [0, 1]], ![[0, 1], [71, 69], [41, 148], [182, 152], [63, 52], [85, 61], [46, 69], [122, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [129, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [131, 69, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5593, 1405, -25]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, 30, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![89, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![89, 1, 0]] 
 ![![191, 0, 0], ![89, 1, 0], ![153, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![89, 1, 0], ![2, 88, 5], ![157, 8, 90]]]
  hmulB := by decide  
  f := ![![![-11569, -689170, -39160], ![-8786, 1495912, 0]], ![![-5429, -321091, -18245], ![-4010, 696959, 0]], ![![-9210, -552057, -31369], ![-7161, 1198296, 0]]]
  g := ![![![1, 0, 0], ![-89, 191, 0], ![-153, 0, 191]], ![![0, 1, 0], ![-45, 88, 5], ![-75, 8, 90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![48, -18, 1]] ![![191, 0, 0], ![89, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![16999, 191, 0]], ![![9168, -3438, 191], ![4393, -1528, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![89, 1, 0]]], ![![![48, -18, 1]], ![![23, -8, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -15, 6]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![13, -15, 6]] 
 ![![193, 0, 0], ![0, 193, 0], ![163, 94, 1]] where
  M :=![![![13, -15, 6], ![912, 76, -69], ![-1959, 78, 46]]]
  hmulB := by decide  
  f := ![![![46, 6, 3]], ![![483, 64, 33]], ![![280, 37, 19]]]
  g := ![![![-5, -3, 6], ![63, 34, -69], ![-49, -22, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [181, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 192], [0, 1]]
 g := ![![[138, 16], [145], [8], [109], [192], [121], [112, 1]], ![[0, 177], [145], [8], [109], [192], [121], [31, 192]]]
 h' := ![![[112, 192], [62, 189], [161, 97], [114, 104], [100, 63], [150, 81], [186, 11], [0, 1]], ![[0, 1], [0, 4], [24, 96], [182, 89], [15, 130], [151, 112], [67, 182], [112, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [142, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [181, 81, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3983, 3050, 1675]
  a := ![4, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1394, -800, 1675]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46, 6, 3]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![46, 6, 3]] 
 ![![193, 0, 0], ![108, 1, 0], ![121, 0, 1]] where
  M :=![![![46, 6, 3], ![483, 64, 33], ![1140, 147, 76]]]
  hmulB := by decide  
  f := ![![![13, -15, 6]], ![![12, -8, 3]], ![![-2, -9, 4]]]
  g := ![![![-5, 6, 3], ![-54, 64, 33], ![-124, 147, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![13, -15, 6]] ![![46, 6, 3]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB229I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB229I3 : PrimesBelowBoundCertificateInterval O 137 193 229 where
  m := 11
  g := ![2, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB229I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![4657463]
    · exact ![29929, 173]
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
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N0, I151N1, I151N2, I157N1, I163N0, I163N1, I163N2, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N0, I151N1, I151N2], [I157N1], [I163N0, I163N1, I163N2], [], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
