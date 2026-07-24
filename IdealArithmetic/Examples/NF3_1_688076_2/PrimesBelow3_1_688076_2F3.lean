
import IdealArithmetic.Examples.NF3_1_688076_2.RI3_1_688076_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [26, 8, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 88, 83], [109, 50, 56], [0, 1]]
 g := ![![[109, 54, 36], [16, 61, 125], [51, 122], [126, 3, 86], [7, 13], [55, 1], []], ![[17, 5, 40, 28], [80, 64, 84, 83], [61, 83], [96, 24, 21, 30], [98, 1], [47, 137], [133, 78]], ![[37, 6, 9, 61], [100, 133, 50, 58], [127, 1], [28, 101, 20, 103], [82, 96], [9, 99], [21, 78]]]
 h' := ![![[85, 88, 83], [1, 91, 133], [50, 73, 79], [60, 115, 20], [28, 51, 124], [99, 90, 98], [0, 0, 1], [0, 1]], ![[109, 50, 56], [7, 45, 25], [133, 47, 1], [107, 60, 120], [122, 79, 8], [86, 48, 138], [14, 53, 50], [85, 88, 83]], ![[0, 1], [12, 3, 120], [111, 19, 59], [76, 103, 138], [138, 9, 7], [121, 1, 42], [76, 86, 88], [109, 50, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 94], []]
 b := ![[], [62, 68, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [26, 8, 84, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132050, 3336, 6672]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-950, 24, 48]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![26, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![26, 1, 0]] 
 ![![149, 0, 0], ![26, 1, 0], ![35, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![26, 1, 0], ![1, 26, 2], ![-174, 20, 27]]]
  hmulB := by decide  
  f := ![![![-6231, -172157, -13244], ![-2235, 986678, 0]], ![![-1103, -30028, -2310], ![-297, 172095, 0]], ![![-1475, -40440, -3111], ![-460, 231770, 0]]]
  g := ![![![1, 0, 0], ![-26, 149, 0], ![-35, 0, 149]], ![![0, 1, 0], ![-5, 26, 2], ![-11, 20, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![35, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![35, 1, 0]] 
 ![![149, 0, 0], ![35, 1, 0], ![133, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![35, 1, 0], ![1, 35, 2], ![-174, 20, 36]]]
  hmulB := by decide  
  f := ![![![-12556, -489679, -27984], ![-6109, 2084808, 0]], ![![-2971, -115001, -6572], ![-1340, 489614, 0]], ![![-11207, -437096, -24979], ![-5456, 1860936, 0]]]
  g := ![![![1, 0, 0], ![-35, 149, 0], ![-133, 0, 149]], ![![0, 1, 0], ![-10, 35, 2], ![-38, 20, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-62, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-62, 1, 0]] 
 ![![149, 0, 0], ![87, 1, 0], ![90, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-62, 1, 0], ![1, -62, 2], ![-174, 20, -61]]]
  hmulB := by decide  
  f := ![![![-1205, 109359, -3528], ![1341, 262836, 0]], ![![-718, 63793, -2058], ![746, 153321, 0]], ![![-742, 66056, -2131], ![776, 158760, 0]]]
  g := ![![![1, 0, 0], ![-87, 149, 0], ![-90, 0, 149]], ![![-1, 1, 0], ![35, -62, 2], ![24, 20, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![26, 1, 0]] ![![149, 0, 0], ![35, 1, 0]]
  ![![149, 0, 0], ![-66, -44, 1]] where
 M := ![![![22201, 0, 0], ![5215, 149, 0]], ![![3874, 149, 0], ![911, 61, 2]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![35, 1, 0], ![0, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-66, -44, 1]] ![![149, 0, 0], ![-62, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9238, 149, 0]], ![![-9834, -6556, 149], ![3874, 2682, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-62, 1, 0]]], ![![![-66, -44, 1]], ![![26, 18, -1]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [39, 108, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 115, 46], [100, 35, 105], [0, 1]]
 g := ![![[98, 71, 8], [113, 61, 76], [64], [19, 64], [55, 10, 138], [53, 1], []], ![[128, 109, 7, 28], [2, 92, 19, 102], [146, 145, 15, 150], [27, 11], [127, 19, 66, 77], [131, 17], [116, 2]], ![[81, 77, 144, 69], [8, 58, 92, 8], [50, 89, 54, 1], [134, 95], [48, 137, 138, 62], [97, 88], [57, 2]]]
 h' := ![![[104, 115, 46], [123, 122, 92], [71, 114, 23], [69, 143], [120, 107, 143], [47, 126, 134], [0, 0, 1], [0, 1]], ![[100, 35, 105], [57, 32, 74], [56, 22, 9], [143, 137, 85], [21, 11, 112], [109, 30, 67], [101, 140, 35], [104, 115, 46]], ![[0, 1], [138, 148, 136], [82, 15, 119], [24, 22, 66], [95, 33, 47], [30, 146, 101], [76, 11, 115], [100, 35, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 101], []]
 b := ![[], [98, 136, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [39, 108, 98, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2172135, -685842, 106606]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14385, -4542, 706]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![16, 4, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![16, 4, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![16, 4, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![16, 4, 1], ![-170, 36, 9], ![-773, 3, 40]]]
  hmulB := by decide  
  f := ![![![-15, -4, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -4, 157]], ![![0, 0, 1], ![-2, 0, 9], ![-9, -1, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [113, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 156], [0, 1]]
 g := ![![[4, 132], [12], [12, 44], [4, 46], [44, 140], [47], [1]], ![[0, 25], [12], [63, 113], [93, 111], [35, 17], [47], [1]]]
 h' := ![![[19, 156], [9, 140], [57, 13], [19, 94], [52, 49], [79, 53], [44, 19], [0, 1]], ![[0, 1], [0, 17], [147, 144], [78, 63], [41, 108], [144, 104], [91, 138], [19, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [55, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [113, 138, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-317075, -338044, 86462]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10831, -4356, 86462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-9, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-9, 1, 0]] 
 ![![157, 0, 0], ![148, 1, 0], ![117, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-9, 1, 0], ![1, -9, 2], ![-174, 20, -8]]]
  hmulB := by decide  
  f := ![![![-722, 6587, -1464], ![157, 114924, 0]], ![![-680, 6209, -1380], ![158, 108330, 0]], ![![-540, 4909, -1091], ![83, 85644, 0]]]
  g := ![![![1, 0, 0], ![-148, 157, 0], ![-117, 0, 157]], ![![-1, 1, 0], ![7, -9, 2], ![-14, 20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![16, 4, 1]] ![![157, 0, 0], ![-9, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-1413, 157, 0]], ![![2512, 628, 157], ![-314, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-9, 1, 0]]], ![![![16, 4, 1]], ![![-2, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![46, -6, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![46, -6, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![46, 157, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![46, -6, 1], ![-180, 66, -11], ![967, -197, 60]]]
  hmulB := by decide  
  f := ![![![-45, 6, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -157, 163]], ![![0, -1, 1], ![2, 11, -11], ![-11, -59, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [108, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 162], [0, 1]]
 g := ![![[162, 58], [90, 146], [41], [95], [53], [29, 91], [1]], ![[69, 105], [47, 17], [41], [95], [53], [77, 72], [1]]]
 h' := ![![[108, 162], [60, 104], [152, 31], [159, 81], [65, 101], [128, 78], [55, 108], [0, 1]], ![[0, 1], [45, 59], [77, 132], [105, 82], [52, 62], [76, 85], [146, 55], [108, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [58, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [108, 55, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-182, -2074, 237]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -241, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![11, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![11, 1, 0]] 
 ![![163, 0, 0], ![11, 1, 0], ![103, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![11, 1, 0], ![1, 11, 2], ![-174, 20, 12]]]
  hmulB := by decide  
  f := ![![![-2035, -22516, -4094], ![-163, 333661, 0]], ![![-138, -1518, -276], ![1, 22494, 0]], ![![-1287, -14228, -2587], ![-87, 210841, 0]]]
  g := ![![![1, 0, 0], ![-11, 163, 0], ![-103, 0, 163]], ![![0, 1, 0], ![-2, 11, 2], ![-10, 20, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![46, -6, 1]] ![![163, 0, 0], ![11, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![1793, 163, 0]], ![![7498, -978, 163], ![326, 0, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![11, 1, 0]]], ![![![46, -6, 1]], ![![2, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-27, 30, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-27, 30, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![140, 30, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-27, 30, 1], ![-144, -7, 61], ![-5297, 523, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -30, 167]], ![![-1, 0, 1], ![-52, -11, 61], ![-51, -1, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [91, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 166], [0, 1]]
 g := ![![[97, 93], [20, 31], [38, 147], [154], [130], [104, 75], [1]], ![[158, 74], [96, 136], [59, 20], [154], [130], [67, 92], [1]]]
 h' := ![![[24, 166], [17, 60], [49, 71], [126, 67], [46, 133], [55, 111], [76, 24], [0, 1]], ![[0, 1], [121, 107], [83, 96], [64, 100], [65, 34], [47, 56], [151, 143], [24, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [123, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [91, 143, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1054, -369, -196]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![158, 33, -196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-61, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-61, 1, 0]] 
 ![![167, 0, 0], ![106, 1, 0], ![144, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-61, 1, 0], ![1, -61, 2], ![-174, 20, -60]]]
  hmulB := by decide  
  f := ![![![-1340, 107841, -3536], ![1169, 295256, 0]], ![![-816, 68437, -2244], ![836, 187374, 0]], ![![-1116, 92988, -3049], ![1116, 254592, 0]]]
  g := ![![![1, 0, 0], ![-106, 167, 0], ![-144, 0, 167]], ![![-1, 1, 0], ![37, -61, 2], ![38, 20, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-27, 30, 1]] ![![167, 0, 0], ![-61, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-10187, 167, 0]], ![![-4509, 5010, 167], ![1503, -1837, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-61, 1, 0]]], ![![![-27, 30, 1]], ![![9, -11, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [86, 164, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 143, 134], [100, 29, 39], [0, 1]]
 g := ![![[90, 22, 31], [83, 29], [46, 67, 152], [101, 31, 29], [56, 109], [101, 145, 1], []], ![[167, 88, 127, 20], [20, 160], [23, 30, 137, 110], [160, 66, 17, 103], [48, 142], [67, 111, 114, 71], [61, 137]], ![[79, 68, 26, 70], [122, 9], [141, 73, 162, 110], [101, 147, 16, 94], [100, 60], [115, 147, 4, 154], [156, 137]]]
 h' := ![![[45, 143, 134], [138, 85, 107], [23, 100, 78], [137, 113, 124], [113, 42, 78], [137, 30, 121], [0, 0, 1], [0, 1]], ![[100, 29, 39], [126, 128, 134], [156, 126, 92], [85, 129, 54], [58, 136, 105], [131, 130, 90], [66, 80, 29], [45, 143, 134]], ![[0, 1], [25, 133, 105], [134, 120, 3], [112, 104, 168], [133, 168, 163], [157, 13, 135], [44, 93, 143], [100, 29, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 12], []]
 b := ![[], [86, 0, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [86, 164, 28, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5077031, -77158, 120235]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29347, -446, 695]
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


def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![24, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![24, 1, 0]] 
 ![![179, 0, 0], ![24, 1, 0], ![160, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![24, 1, 0], ![1, 24, 2], ![-174, 20, 25]]]
  hmulB := by decide  
  f := ![![![-9654, -239770, -19982], ![-2506, 1788389, 0]], ![![-1315, -32135, -2678], ![-178, 239681, 0]], ![![-8616, -214319, -17861], ![-2339, 1598560, 0]]]
  g := ![![![1, 0, 0], ![-24, 179, 0], ![-160, 0, 179]], ![![0, 1, 0], ![-5, 24, 2], ![-26, 20, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![77, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![77, 1, 0]] 
 ![![179, 0, 0], ![77, 1, 0], ![79, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![77, 1, 0], ![1, 77, 2], ![-174, 20, 78]]]
  hmulB := by decide  
  f := ![![![-3590, -400995, -10416], ![-3759, 932232, 0]], ![![-1547, -172471, -4480], ![-1610, 400960, 0]], ![![-1627, -176976, -4597], ![-1560, 411432, 0]]]
  g := ![![![1, 0, 0], ![-77, 179, 0], ![-79, 0, 179]], ![![0, 1, 0], ![-34, 77, 2], ![-44, 20, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![24, 1, 0]] ![![179, 0, 0], ![77, 1, 0]]
  ![![179, 0, 0], ![-60, -39, 1]] where
 M := ![![![32041, 0, 0], ![13783, 179, 0]], ![![4296, 179, 0], ![1849, 101, 2]]]
 hmul := by decide  
 g := ![![![![179, 0, 0], ![0, 0, 0]], ![![77, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![11, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-60, -39, 1]] ![![179, 0, 0], ![77, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![13783, 179, 0]], ![![-10740, -6981, 179], ![-4833, -3043, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![77, 1, 0]]], ![![![-60, -39, 1]], ![![-27, -17, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![65, 22, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![65, 22, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![65, 22, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![65, 22, 1], ![-152, 85, 45], ![-3905, 363, 107]]]
  hmulB := by decide  
  f := ![![![-64, -22, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -22, 181]], ![![0, 0, 1], ![-17, -5, 45], ![-60, -11, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [129, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 180], [0, 1]]
 g := ![![[137, 87], [46], [56, 67], [15], [25, 13], [111, 62], [1]], ![[0, 94], [46], [67, 114], [15], [146, 168], [159, 119], [1]]]
 h' := ![![[65, 180], [114, 79], [16, 107], [59, 51], [33, 167], [161, 111], [52, 65], [0, 1]], ![[0, 1], [0, 102], [93, 74], [116, 130], [28, 14], [136, 70], [114, 116], [65, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [17, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [129, 116, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2349, -717, -156]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![69, 15, -156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-45, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-45, 1, 0]] 
 ![![181, 0, 0], ![136, 1, 0], ![74, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-45, 1, 0], ![1, -45, 2], ![-174, 20, -44]]]
  hmulB := by decide  
  f := ![![![-441, 23938, -1064], ![362, 96292, 0]], ![![-308, 17953, -798], ![363, 72219, 0]], ![![-189, 9787, -435], ![113, 39368, 0]]]
  g := ![![![1, 0, 0], ![-136, 181, 0], ![-74, 0, 181]], ![![-1, 1, 0], ![33, -45, 2], ![2, 20, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![65, 22, 1]] ![![181, 0, 0], ![-45, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-8145, 181, 0]], ![![11765, 3982, 181], ![-3077, -905, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-45, 1, 0]]], ![![![65, 22, 1]], ![![-17, -5, 0]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [39, 27, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 49, 181], [144, 141, 10], [0, 1]]
 g := ![![[19, 175, 24], [51, 1, 135], [68, 27, 18], [17, 86, 17], [130, 143, 184], [167, 167, 1], []], ![[26, 86, 43, 61], [95, 59, 80, 171], [32, 5, 159, 47], [109, 42, 73, 146], [162, 56, 21, 159], [4, 94, 185, 21], [58, 100]], ![[49, 6, 171, 17], [141, 143, 46, 97], [22, 48, 42, 27], [1, 135, 120, 92], [149, 110, 166, 103], [86, 34, 176, 135], [38, 100]]]
 h' := ![![[23, 49, 181], [112, 23, 62], [22, 54, 53], [101, 127, 171], [87, 60, 141], [172, 56, 39], [0, 0, 1], [0, 1]], ![[144, 141, 10], [155, 50, 108], [140, 108, 57], [55, 175, 112], [66, 44, 181], [150, 98, 164], [177, 35, 141], [23, 49, 181]], ![[0, 1], [175, 118, 21], [107, 29, 81], [29, 80, 99], [72, 87, 60], [108, 37, 179], [154, 156, 49], [144, 141, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 63], []]
 b := ![[], [109, 42, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [39, 27, 24, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![507487, -215448, 20246]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2657, -1128, 106]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![21, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![21, 1, 0]] 
 ![![193, 0, 0], ![21, 1, 0], ![166, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![21, 1, 0], ![1, 21, 2], ![-174, 20, 22]]]
  hmulB := by decide  
  f := ![![![-6246, -134267, -12788], ![-1351, 1234042, 0]], ![![-695, -14595, -1390], ![1, 134135, 0]], ![![-5382, -115484, -10999], ![-1072, 1061404, 0]]]
  g := ![![![1, 0, 0], ![-21, 193, 0], ![-166, 0, 193]], ![![0, 1, 0], ![-4, 21, 2], ![-22, 20, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![36, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![36, 1, 0]] 
 ![![193, 0, 0], ![36, 1, 0], ![28, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![36, 1, 0], ![1, 36, 2], ![-174, 20, 37]]]
  hmulB := by decide  
  f := ![![![-2333, -89204, -4956], ![-772, 478254, 0]], ![![-462, -16632, -924], ![1, 89166, 0]], ![![-356, -12942, -719], ![-18, 69384, 0]]]
  g := ![![![1, 0, 0], ![-36, 193, 0], ![-28, 0, 193]], ![![0, 1, 0], ![-7, 36, 2], ![-10, 20, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-58, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-58, 1, 0]] 
 ![![193, 0, 0], ![135, 1, 0], ![152, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-58, 1, 0], ![1, -58, 2], ![-174, 20, -57]]]
  hmulB := by decide  
  f := ![![![617, -42454, 1464], ![-386, -141276, 0]], ![![455, -29695, 1024], ![-192, -98816, 0]], ![![528, -33436, 1153], ![-164, -111264, 0]]]
  g := ![![![1, 0, 0], ![-135, 193, 0], ![-152, 0, 193]], ![![-1, 1, 0], ![39, -58, 2], ![30, 20, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![21, 1, 0]] ![![193, 0, 0], ![36, 1, 0]]
  ![![193, 0, 0], ![-104, -68, 1]] where
 M := ![![![37249, 0, 0], ![6948, 193, 0]], ![![4053, 193, 0], ![757, 57, 2]]]
 hmul := by decide  
 g := ![![![![193, 0, 0], ![0, 0, 0]], ![![36, 1, 0], ![0, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-104, -68, 1]] ![![193, 0, 0], ![-58, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-11194, 193, 0]], ![![-20072, -13124, 193], ![5790, 3860, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-58, 1, 0]]], ![![![-104, -68, 1]], ![![30, 20, -1]]]]
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


lemma PB235I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB235I3 : PrimesBelowBoundCertificateInterval O 137 193 235 where
  m := 11
  g := ![1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB235I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N1]
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
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
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
  β := ![I149N0, I149N1, I149N2, I157N1, I163N1, I167N1, I179N0, I179N1, I181N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N0, I149N1, I149N2], [], [I157N1], [I163N1], [I167N1], [], [I179N0, I179N1, I179N1], [I181N1], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
