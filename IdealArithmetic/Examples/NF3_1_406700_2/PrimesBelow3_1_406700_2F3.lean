
import IdealArithmetic.Examples.NF3_1_406700_2.RI3_1_406700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 6, 2]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![17, 6, 2]] 
 ![![139, 0, 0], ![0, 139, 0], ![78, 3, 1]] where
  M :=![![![17, 6, 2], ![-128, -37, 34], ![-492, -190, -17]]]
  hmulB := by decide  
  f := ![![![51, -2, 2]], ![![-136, 5, -6]], ![![26, -1, 1]]]
  g := ![![![-1, 0, 2], ![-20, -1, 34], ![6, -1, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [92, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 138], [0, 1]]
 g := ![![[112, 30], [59, 24], [113], [90, 4], [46], [46], [1]], ![[128, 109], [44, 115], [113], [18, 135], [46], [46], [1]]]
 h' := ![![[121, 138], [132, 13], [15, 21], [60, 104], [29, 137], [62, 121], [47, 121], [0, 1]], ![[0, 1], [37, 126], [54, 118], [134, 35], [65, 2], [108, 18], [93, 18], [121, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [32, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [92, 18, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1050, -575, -655]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![360, 10, -655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -2, 2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![51, -2, 2]] 
 ![![139, 0, 0], ![122, 1, 0], ![78, 0, 1]] where
  M :=![![![51, -2, 2], ![-136, 5, -6], ![44, 2, 1]]]
  hmulB := by decide  
  f := ![![![17, 6, 2]], ![![14, 5, 2]], ![![6, 2, 1]]]
  g := ![![![1, -2, 2], ![-2, 5, -6], ![-2, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![17, 6, 2]] ![![51, -2, 2]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![55, 26, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![55, 26, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![55, 26, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![55, 26, 1], ![-41, 5, 132], ![-1787, -647, 84]]]
  hmulB := by decide  
  f := ![![![-54, -26, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -26, 149]], ![![0, 0, 1], ![-49, -23, 132], ![-43, -19, 84]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [77, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 148], [0, 1]]
 g := ![![[134, 143], [46], [16, 88], [17], [83, 61], [28], [1]], ![[58, 6], [46], [38, 61], [17], [61, 88], [28], [1]]]
 h' := ![![[112, 148], [144, 128], [109, 33], [139, 45], [16, 49], [48, 43], [72, 112], [0, 1]], ![[0, 1], [27, 21], [80, 116], [113, 104], [140, 100], [96, 106], [100, 37], [112, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [89, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [77, 37, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2105, -373, -2427]
  a := ![2, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![910, 421, -2427]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![17, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![17, 1, 0]] 
 ![![149, 0, 0], ![17, 1, 0], ![65, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![17, 1, 0], ![1, 16, 5], ![-67, -24, 19]]]
  hmulB := by decide  
  f := ![![![-12347, -202446, -63270], ![-2682, 1885446, 0]], ![![-1409, -23086, -7215], ![-297, 215007, 0]], ![![-5397, -88316, -27601], ![-1076, 822510, 0]]]
  g := ![![![1, 0, 0], ![-17, 149, 0], ![-65, 0, 149]], ![![0, 1, 0], ![-4, 16, 5], ![-6, -24, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![55, 26, 1]] ![![149, 0, 0], ![17, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![2533, 149, 0]], ![![8195, 3874, 149], ![894, 447, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![17, 1, 0]]], ![![![55, 26, 1]], ![![6, 3, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [67, 30, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 102, 19], [93, 48, 132], [0, 1]]
 g := ![![[15, 120, 55], [12, 16, 138], [58, 101, 121], [144, 76], [9, 83, 36], [145, 1], []], ![[25, 141, 103, 19], [58, 97, 117, 68], [97, 36, 56, 95], [94, 90], [34, 118, 77, 64], [132, 39], [49, 59]], ![[34, 83, 10, 114], [24, 145, 143, 67], [136, 50, 69, 60], [10, 138], [91, 119, 131, 54], [105, 136], [87, 59]]]
 h' := ![![[52, 102, 19], [102, 17, 31], [40, 87, 17], [17, 134, 140], [1, 92, 128], [100, 113, 6], [0, 0, 1], [0, 1]], ![[93, 48, 132], [100, 144, 150], [6, 77, 53], [66, 121, 55], [133, 57, 40], [86, 54, 19], [25, 51, 48], [52, 102, 19]], ![[0, 1], [13, 141, 121], [50, 138, 81], [32, 47, 107], [20, 2, 134], [47, 135, 126], [102, 100, 102], [93, 48, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 49], []]
 b := ![[], [125, 23, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [67, 30, 6, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44613365401, -18711407204, -7559497598]
  a := ![-65, 2, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-295452751, -123916604, -50062898]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-26, -67, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-26, -67, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![131, 90, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-26, -67, 1], ![-134, 17, -333], ![4444, 1585, -183]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-131, -90, 157]], ![![-1, -1, 1], ![277, 191, -333], ![181, 115, -183]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [52, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 156], [0, 1]]
 g := ![![[136, 154], [10], [43, 42], [95, 4], [53, 17], [49], [1]], ![[0, 3], [10], [63, 115], [67, 153], [91, 140], [49], [1]]]
 h' := ![![[150, 156], [139, 132], [119, 18], [84, 102], [70, 2], [156, 71], [105, 150], [0, 1]], ![[0, 1], [0, 25], [150, 139], [155, 55], [56, 155], [130, 86], [154, 7], [150, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [82, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [52, 7, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![509, -675, -2912]
  a := ![-2, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2433, 1665, -2912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![19, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![19, 1, 0]] 
 ![![157, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![19, 1, 0], ![1, 18, 5], ![-67, -24, 21]]]
  hmulB := by decide  
  f := ![![![-4826, -89273, -24800], ![-1099, 778720, 0]], ![![-600, -10800, -3000], ![1, 94200, 0]], ![![-817, -14785, -4107], ![-35, 128960, 0]]]
  g := ![![![1, 0, 0], ![-19, 157, 0], ![-26, 0, 157]], ![![0, 1, 0], ![-3, 18, 5], ![-1, -24, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-26, -67, 1]] ![![157, 0, 0], ![19, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![2983, 157, 0]], ![![-4082, -10519, 157], ![-628, -1256, -314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![19, 1, 0]]], ![![![-26, -67, 1]], ![![-4, -8, -2]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![5, -10, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![5, -10, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![5, 153, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![5, -10, 1], ![-77, -9, -48], ![625, 217, -38]]]
  hmulB := by decide  
  f := ![![![-4, 10, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -153, 163]], ![![0, -1, 1], ![1, 45, -48], ![5, 37, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [146, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 162], [0, 1]]
 g := ![![[108, 115], [149, 133], [118], [97], [71], [121, 56], [1]], ![[0, 48], [0, 30], [118], [97], [71], [84, 107], [1]]]
 h' := ![![[43, 162], [88, 142], [90, 123], [23, 66], [161, 89], [101, 87], [17, 43], [0, 1]], ![[0, 1], [0, 21], [0, 40], [90, 97], [76, 74], [93, 76], [73, 120], [43, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [141, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [146, 120, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1098, -575, -1165]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 1090, -1165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![48, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![48, 1, 0]] 
 ![![163, 0, 0], ![48, 1, 0], ![38, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![48, 1, 0], ![1, 47, 5], ![-67, -24, 50]]]
  hmulB := by decide  
  f := ![![![1790, 99868, 10625], ![1141, -346375, 0]], ![![481, 29372, 3125], ![490, -101875, 0]], ![![412, 23282, 2477], ![284, -80750, 0]]]
  g := ![![![1, 0, 0], ![-48, 163, 0], ![-38, 0, 163]], ![![0, 1, 0], ![-15, 47, 5], ![-5, -24, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![5, -10, 1]] ![![163, 0, 0], ![48, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![7824, 163, 0]], ![![815, -1630, 163], ![163, -489, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![48, 1, 0]]], ![![![5, -10, 1]], ![![1, -3, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [144, 16, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 156, 64], [78, 10, 103], [0, 1]]
 g := ![![[139, 75, 122], [151, 148, 144], [148, 157, 127], [140, 32], [66, 150], [34, 102, 1], []], ![[3, 158, 69, 21], [97, 128, 156, 77], [130, 45, 60, 157], [32, 3], [150, 89], [48, 51, 17, 54], [53, 88]], ![[37, 40, 95, 138], [54, 108, 28, 73], [44, 116, 57, 51], [125, 137], [87, 36], [122, 114, 0, 105], [14, 88]]]
 h' := ![![[24, 156, 64], [133, 74, 150], [64, 77, 155], [105, 78, 131], [152, 92, 52], [114, 132, 22], [0, 0, 1], [0, 1]], ![[78, 10, 103], [118, 27, 57], [78, 61, 132], [149, 29, 123], [9, 119, 62], [20, 112, 151], [125, 147, 10], [24, 156, 64]], ![[0, 1], [42, 66, 127], [6, 29, 47], [21, 60, 80], [94, 123, 53], [40, 90, 161], [60, 20, 156], [78, 10, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 35], []]
 b := ![[], [75, 67, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [144, 16, 65, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3399285, 919836, -1339173]
  a := ![2, 18, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20355, 5508, -8019]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [9, 82, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 127, 94], [10, 45, 79], [0, 1]]
 g := ![![[12, 166, 31], [5, 10], [160, 147, 96], [20, 31, 137], [110, 89], [7, 75, 1], []], ![[112, 80, 105, 5], [150, 36], [102, 12, 106, 18], [85, 166, 85, 131], [146, 57], [39, 48, 145, 50], [112, 13]], ![[95, 120, 135, 71], [30, 116], [81, 108, 2, 28], [81, 21, 67, 8], [50, 6], [61, 131, 119, 46], [127, 13]]]
 h' := ![![[65, 127, 94], [150, 133, 107], [117, 138, 23], [166, 44, 142], [38, 157, 39], [110, 135, 75], [0, 0, 1], [0, 1]], ![[10, 45, 79], [94, 66, 17], [38, 126, 167], [6, 89, 146], [74, 70, 78], [2, 68, 149], [103, 116, 45], [65, 127, 94]], ![[0, 1], [80, 147, 49], [171, 82, 156], [69, 40, 58], [29, 119, 56], [47, 143, 122], [168, 57, 127], [10, 45, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158, 164], []]
 b := ![[], [50, 51, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [9, 82, 98, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-245487, -256213, -599964]
  a := ![-2, 4, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1419, -1481, -3468]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![67, -14, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![67, -14, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![67, 165, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![67, -14, 1], ![-81, 57, -68], ![893, 313, 16]]]
  hmulB := by decide  
  f := ![![![-66, 14, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -165, 179]], ![![0, -1, 1], ![25, 63, -68], ![-1, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [42, 158, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 178], [0, 1]]
 g := ![![[89, 81], [85, 13], [171], [153], [103, 46], [158, 83], [1]], ![[0, 98], [0, 166], [171], [153], [174, 133], [111, 96], [1]]]
 h' := ![![[21, 178], [10, 170], [149, 27], [23, 156], [149, 42], [166, 164], [137, 21], [0, 1]], ![[0, 1], [0, 9], [0, 152], [77, 23], [136, 137], [30, 15], [41, 158], [21, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [124, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [42, 158, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2797, -1983, -715]
  a := ![2, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, 648, -715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![68, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![68, 1, 0]] 
 ![![179, 0, 0], ![68, 1, 0], ![163, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![68, 1, 0], ![1, 67, 5], ![-67, -24, 70]]]
  hmulB := by decide  
  f := ![![![-2537, -224706, -16770], ![-2148, 600366, 0]], ![![-1002, -85354, -6370], ![-715, 228046, 0]], ![![-2341, -204621, -15271], ![-1875, 546702, 0]]]
  g := ![![![1, 0, 0], ![-68, 179, 0], ![-163, 0, 179]], ![![0, 1, 0], ![-30, 67, 5], ![-55, -24, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![67, -14, 1]] ![![179, 0, 0], ![68, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![12172, 179, 0]], ![![11993, -2506, 179], ![4475, -895, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![68, 1, 0]]], ![![![67, -14, 1]], ![![25, -5, 0]]]]
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


lemma PB181I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 180 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 180 (by omega)

def PB181I3 : PrimesBelowBoundCertificateInterval O 137 180 181 where
  m := 8
  g := ![2, 2, 1, 2, 2, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB181I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
  β := ![I139N1, I149N1, I157N1, I163N1, I179N1]
  Il := ![[I139N1], [I149N1], [], [I157N1], [I163N1], [], [], [I179N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
