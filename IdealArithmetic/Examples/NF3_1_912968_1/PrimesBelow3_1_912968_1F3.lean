
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547704, -373167, 64636]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![547704, -373167, 64636]] 
 ![![139, 0, 0], ![0, 139, 0], ![44, 48, 1]] where
  M :=![![![547704, -373167, 64636], ![11843037, 2163604, -681698], ![-63612511, -2413123, 1790437]]]
  hmulB := by decide  
  f := ![![![16034356346, 3684585509, 824032298]], ![![159426689831, 36635163796, 8193203316]], ![![65773747541, 15114357685, 3380222515]]]
  g := ![![![-16520, -25005, 64636], ![300991, 250972, -681698], ![-1024401, -635641, 1790437]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [138, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 138], [0, 1]]
 g := ![![[89, 1], [0, 137], [1], [], [], [137], [1]], ![[39, 138], [100, 2], [1], [], [], [137], [1]]]
 h' := ![![[89, 138], [0, 138], [1, 89], [0, 1], [1], [138], [1, 89], [0, 1]], ![[0, 1], [50, 1], [138, 50], [89, 138], [1], [138], [138, 50], [89, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [114, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [138, 50, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1274, 480, 10]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 0, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16034356346, 3684585509, 824032298]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![16034356346, 3684585509, 824032298]] 
 ![![139, 0, 0], ![42, 1, 0], ![22, 0, 1]] where
  M :=![![![16034356346, 3684585509, 824032298], ![159426689831, 36635163796, 8193203316], ![784558117087, 180286093611, 40319749305]]]
  hmulB := by decide  
  f := ![![![547704, -373167, 64636]], ![![250695, -97190, 14626]], ![![-370957, -76423, 23111]]]
  g := ![![![-1128395292, 3684585509, 824032298], ![-11219429227, 36635163796, 8193203316], ![-55212174815, 180286093611, 40319749305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![547704, -373167, 64636]] ![![16034356346, 3684585509, 824032298]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [138, 9, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 132, 44], [140, 16, 105], [0, 1]]
 g := ![![[51, 18, 124], [128, 30], [141, 50, 113], [3, 7], [112, 125, 100], [105, 1], []], ![[37, 19, 53, 147], [44, 45], [18, 133, 135, 12], [87, 45], [96, 63, 45, 51], [24, 107], [38, 148]], ![[98, 75, 2, 56], [148, 81], [113, 138, 122, 66], [14, 103], [10, 21, 77, 79], [97, 140], [126, 148]]]
 h' := ![![[114, 132, 44], [63, 37, 78], [61, 62, 103], [143, 62, 115], [40, 97, 93], [112, 109, 139], [0, 0, 1], [0, 1]], ![[140, 16, 105], [123, 140, 45], [91, 78, 55], [72, 139, 98], [146, 53, 94], [131, 58, 17], [4, 92, 16], [114, 132, 44]], ![[0, 1], [22, 121, 26], [114, 9, 140], [69, 97, 85], [8, 148, 111], [106, 131, 142], [126, 57, 132], [140, 16, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 110], []]
 b := ![[], [66, 76, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [138, 9, 44, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2092556, 679738, 103704]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14044, 4562, 696]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-79, 42, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-79, 42, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![72, 42, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-79, 42, 1], ![231, -54, 85], ![8045, 1157, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -42, 151]], ![![-1, 0, 1], ![-39, -24, 85], ![59, 11, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [60, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 150], [0, 1]]
 g := ![![[107, 36], [3, 58], [125, 84], [69], [32, 11], [44], [1]], ![[17, 115], [9, 93], [66, 67], [69], [80, 140], [44], [1]]]
 h' := ![![[73, 150], [122, 145], [50, 80], [125, 101], [43, 62], [54, 39], [91, 73], [0, 1]], ![[0, 1], [137, 6], [1, 71], [99, 50], [39, 89], [32, 112], [135, 78], [73, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [42, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [60, 78, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440360, 462740, 112202]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50584, -28144, 112202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![66, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![66, 1, 0]] 
 ![![151, 0, 0], ![66, 1, 0], ![12, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![66, 1, 0], ![1, 66, 2], ![189, 25, 67]]]
  hmulB := by decide  
  f := ![![![-10643, -1033484, -31320], ![-11476, 2364660, 0]], ![![-4666, -451671, -13688], ![-4982, 1033444, 0]], ![![-900, -82132, -2489], ![-788, 187920, 0]]]
  g := ![![![1, 0, 0], ![-66, 151, 0], ![-12, 0, 151]], ![![0, 1, 0], ![-29, 66, 2], ![-15, 25, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-79, 42, 1]] ![![151, 0, 0], ![66, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![9966, 151, 0]], ![![-11929, 6342, 151], ![-4983, 2718, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![66, 1, 0]]], ![![![-79, 42, 1]], ![![-33, 18, 1]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [64, 62, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 109, 45], [100, 47, 112], [0, 1]]
 g := ![![[8, 106, 30], [56, 51], [70, 2, 93], [38, 20, 71], [140, 132, 126], [59, 1], []], ![[10, 50, 150, 23], [114, 143], [128, 57, 68, 135], [42, 88, 23, 96], [27, 81, 2, 78], [135, 11], [74, 141]], ![[48, 54, 146, 62], [36, 58], [31, 140, 65, 131], [49, 37, 136, 38], [59, 116, 84, 72], [47, 106], [7, 141]]]
 h' := ![![[116, 109, 45], [18, 115, 117], [73, 48, 69], [80, 96, 90], [146, 49, 68], [149, 46, 122], [0, 0, 1], [0, 1]], ![[100, 47, 112], [67, 10, 155], [45, 128, 65], [26, 141, 72], [149, 22, 63], [155, 1, 111], [85, 58, 47], [116, 109, 45]], ![[0, 1], [115, 32, 42], [8, 138, 23], [51, 77, 152], [49, 86, 26], [129, 110, 81], [132, 99, 109], [100, 47, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 37], []]
 b := ![[], [87, 40, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [64, 62, 98, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2430046, -394227, -29359]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15478, -2511, -187]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [102, 125, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 152, 41], [133, 10, 122], [0, 1]]
 g := ![![[103, 149, 140], [69, 94, 14], [78, 41], [81, 87], [62, 74], [96, 59, 1], []], ![[142, 120, 40, 62], [92, 85, 29, 34], [43, 146], [36, 51], [125, 58], [8, 122, 111, 25], [151, 51]], ![[7, 140, 52, 148], [76, 150, 102, 142], [23, 55], [129, 126], [65, 47], [46, 103, 115, 92], [70, 51]]]
 h' := ![![[89, 152, 41], [134, 96, 125], [78, 55, 103], [84, 59, 81], [14, 17, 24], [151, 75, 143], [0, 0, 1], [0, 1]], ![[133, 10, 122], [45, 5, 133], [41, 118, 25], [29, 62, 132], [142, 78, 122], [129, 68, 104], [17, 45, 10], [89, 152, 41]], ![[0, 1], [143, 62, 68], [47, 153, 35], [130, 42, 113], [30, 68, 17], [125, 20, 79], [117, 118, 152], [133, 10, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 116], []]
 b := ![[], [142, 32, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [102, 125, 104, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123065, 489, 978]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-755, 3, 6]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193675864725433770688029, -44505390126769897497934, -9953325498884162503650]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-193675864725433770688029, -44505390126769897497934, -9953325498884162503650]] 
 ![![167, 0, 0], ![86, 1, 0], ![60, 0, 1]] where
  M :=![![![-193675864725433770688029, -44505390126769897497934, -9953325498884162503650], ![-1925683909415876610687784, -442509002197537833279279, -98964105752423957499518], ![-9476524562340116015000076, -2177640581549852825338900, -487014392324307730777213]]]
  hmulB := by decide  
  f := ![![![-12908221619227, -409855207058, 347095872538]], ![![-6256980805694, -236397440795, 175913955070]], ![![-4879141754048, 13781830908, 96916600835]]]
  g := ![![![25335252791076809367385, -44505390126769897497934, -9953325498884162503650], ![251903812124058769468870, -442509002197537833279279, -98964105752423957499518], ![1239649275391650843178312, -2177640581549852825338900, -487014392324307730777213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12504337284555918, 2873411252944797, 642618734747666]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![12504337284555918, 2873411252944797, 642618734747666]] 
 ![![167, 0, 0], ![106, 1, 0], ![144, 0, 1]] where
  M :=![![![12504337284555918, 2873411252944797, 642618734747666], ![124328352120253671, 28569805653247568, 6389441240637260], ![611834931424566895, 140595485941620187, 31443216906192365]]]
  hmulB := by decide  
  f := ![![![2816050700, -151141363, -26840068]], ![![1756152455, -83089434, -19007006]], ![![2239962251, -170148369, -11203965]]]
  g := ![![![-2303079960067404, 2873411252944797, 642618734747666], ![-22899105304046431, 28569805653247568, 6389441240637260], ![-112689280316639961, 140595485941620187, 31443216906192365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22455, -5160, -1154]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-22455, -5160, -1154]] 
 ![![167, 0, 0], ![141, 1, 0], ![80, 0, 1]] where
  M :=![![![-22455, -5160, -1154], ![-223266, -51305, -11474], ![-1098718, -252478, -56465]]]
  hmulB := by decide  
  f := ![![![-4253, -212, 130]], ![![-3445, -185, 108]], ![![-2194, -50, 55]]]
  g := ![![![4775, -5160, -1154], ![47477, -51305, -11474], ![233640, -252478, -56465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-193675864725433770688029, -44505390126769897497934, -9953325498884162503650]] ![![12504337284555918, 2873411252944797, 642618734747666]]
  ![![-14044862375391343446810814056294968788086, -3227413390820392781381034887827017442175, -721788886847002336402263188435129943404]] where
 M := ![![![-14044862375391343446810814056294968788086, -3227413390820392781381034887827017442175, -721788886847002336402263188435129943404]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-14044862375391343446810814056294968788086, -3227413390820392781381034887827017442175, -721788886847002336402263188435129943404]] ![![-22455, -5160, -1154]]
  ![![167, 0, 0]] where
 M := ![![![1828991504933083144873176770770759501538070752, 420289748446417039724468400740171906668067247, 93994921923290784036139464658881204367274054]]]
 hmul := by decide  
 g := ![![![![10952044939719060747743573477669218572084256, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [111, 153, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 153, 9], [120, 19, 164], [0, 1]]
 g := ![![[26, 105, 29], [156, 16], [153, 151, 67], [46, 25, 6], [89, 10], [24, 2, 1], []], ![[43, 75, 49, 157], [93, 33], [23, 168, 11, 136], [56, 50, 129, 22], [154, 151], [100, 15, 24, 135], [148, 81]], ![[138, 102, 128, 43], [113, 43], [30, 99, 115, 55], [19, 138, 13, 106], [130, 124], [102, 128, 70, 33], [166, 81]]]
 h' := ![![[55, 153, 9], [133, 99, 78], [144, 102, 4], [84, 42, 97], [72, 12, 51], [104, 85, 150], [0, 0, 1], [0, 1]], ![[120, 19, 164], [47, 81, 124], [63, 155, 129], [149, 13, 145], [10, 23, 39], [91, 81, 155], [91, 73, 19], [55, 153, 9]], ![[0, 1], [43, 166, 144], [86, 89, 40], [46, 118, 104], [153, 138, 83], [140, 7, 41], [126, 100, 153], [120, 19, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 121], []]
 b := ![[], [55, 55, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [111, 153, 171, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10434149, 2256093, 515021]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60313, 13041, 2977]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![13, 50, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![13, 50, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![13, 50, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![13, 50, 1], ![239, 38, 101], ![9557, 1357, 88]]]
  hmulB := by decide  
  f := ![![![-12, -50, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -50, 179]], ![![0, 0, 1], ![-6, -28, 101], ![47, -17, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [88, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 178], [0, 1]]
 g := ![![[112, 59], [162, 31], [87], [135], [67, 172], [68, 121], [1]], ![[0, 120], [0, 148], [87], [135], [144, 7], [169, 58], [1]]]
 h' := ![![[168, 178], [64, 136], [23, 116], [55, 96], [11, 80], [102, 107], [91, 168], [0, 1]], ![[0, 1], [0, 43], [0, 63], [73, 83], [26, 99], [178, 72], [33, 11], [168, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [162, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [88, 11, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2360, 534, 204]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -54, 204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![78, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![78, 1, 0]] 
 ![![179, 0, 0], ![78, 1, 0], ![91, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![78, 1, 0], ![1, 78, 2], ![189, 25, 79]]]
  hmulB := by decide  
  f := ![![![-2547, -283906, -7280], ![-2506, 651560, 0]], ![![-1118, -123702, -3172], ![-1073, 283894, 0]], ![![-1287, -144332, -3701], ![-1292, 331240, 0]]]
  g := ![![![1, 0, 0], ![-78, 179, 0], ![-91, 0, 179]], ![![0, 1, 0], ![-35, 78, 2], ![-50, 25, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![13, 50, 1]] ![![179, 0, 0], ![78, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![13962, 179, 0]], ![![2327, 8950, 179], ![1253, 3938, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![78, 1, 0]]], ![![![13, 50, 1]], ![![7, 22, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [129, 86, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 92, 96], [170, 88, 85], [0, 1]]
 g := ![![[39, 167, 122], [19, 37], [49, 5, 52], [102, 138], [74, 174, 172], [47, 26, 1], []], ![[81, 2, 99, 54], [125, 139], [133, 1, 106, 57], [11, 165], [102, 63, 155, 58], [67, 7, 135, 57], [79, 166]], ![[154, 23, 41, 90], [165, 144], [124, 180, 80, 68], [112, 169], [38, 33, 144, 72], [75, 166, 43, 146], [90, 166]]]
 h' := ![![[37, 92, 96], [98, 51, 22], [14, 166, 134], [92, 129, 140], [47, 105, 92], [91, 25, 124], [0, 0, 1], [0, 1]], ![[170, 88, 85], [123, 148, 135], [146, 51, 35], [42, 15, 88], [111, 4, 76], [147, 169, 99], [47, 139, 88], [37, 92, 96]], ![[0, 1], [179, 163, 24], [58, 145, 12], [27, 37, 134], [30, 72, 13], [12, 168, 139], [95, 42, 92], [170, 88, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158, 24], []]
 b := ![[], [90, 130, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [129, 86, 155, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2220508, 688705, 134664]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12268, 3805, 744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [124, 53, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 73, 63], [140, 117, 128], [0, 1]]
 g := ![![[165, 46, 16], [48, 169, 72], [39, 82, 68], [142, 177, 162], [91, 168, 134], [75, 117, 1], []], ![[90, 126, 176, 105], [123, 13, 63, 152], [160, 72, 151, 66], [73, 45, 59, 11], [184, 174, 33, 126], [32, 183, 51, 42], [82, 149]], ![[120, 145, 129, 136], [41, 84, 87, 5], [69, 45, 22, 59], [134, 48, 96, 162], [30, 128, 85, 2], [169, 179, 107, 51], [17, 149]]]
 h' := ![![[168, 73, 63], [160, 85, 187], [130, 139, 151], [155, 165, 100], [176, 173, 60], [59, 44, 158], [0, 0, 1], [0, 1]], ![[140, 117, 128], [89, 145, 112], [111, 162, 66], [66, 49, 130], [25, 7, 156], [74, 12, 57], [102, 178, 117], [168, 73, 63]], ![[0, 1], [156, 152, 83], [61, 81, 165], [166, 168, 152], [114, 11, 166], [73, 135, 167], [111, 13, 73], [140, 117, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 110], []]
 b := ![[], [115, 132, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [124, 53, 74, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2702841, -510925, -64940]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14151, -2675, -340]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-51, 67, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-51, 67, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![142, 67, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-51, 67, 1], ![256, -26, 135], ![12770, 1782, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-142, -67, 193]], ![![-1, 0, 1], ![-98, -47, 135], ![36, -5, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [43, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 192], [0, 1]]
 g := ![![[120, 9], [14], [18], [112], [63], [85], [51, 1]], ![[0, 184], [14], [18], [112], [63], [85], [102, 192]]]
 h' := ![![[51, 192], [40, 3], [177, 173], [76, 37], [35, 43], [87, 177], [123, 49], [0, 1]], ![[0, 1], [0, 190], [122, 20], [33, 156], [105, 150], [43, 16], [113, 144], [51, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [161, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [43, 142, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18101, -648, 1880]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1477, -656, 1880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![58, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![58, 1, 0]] 
 ![![193, 0, 0], ![58, 1, 0], ![152, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![58, 1, 0], ![1, 58, 2], ![189, 25, 59]]]
  hmulB := by decide  
  f := ![![![1543, 109614, 3780], ![1158, -364770, 0]], ![![451, 32884, 1134], ![387, -109431, 0]], ![![1208, 86328, 2977], ![936, -287280, 0]]]
  g := ![![![1, 0, 0], ![-58, 193, 0], ![-152, 0, 193]], ![![0, 1, 0], ![-19, 58, 2], ![-53, 25, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-51, 67, 1]] ![![193, 0, 0], ![58, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![11194, 193, 0]], ![![-9843, 12931, 193], ![-2702, 3860, 193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![58, 1, 0]]], ![![![-51, 67, 1]], ![![-14, 20, 1]]]]
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


lemma PB271I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB271I3 : PrimesBelowBoundCertificateInterval O 137 193 271 where
  m := 11
  g := ![2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB271I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0]
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
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![6967871]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I167N0, I167N1, I167N2, I179N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [], [], [I167N0, I167N1, I167N2], [], [I179N1], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
