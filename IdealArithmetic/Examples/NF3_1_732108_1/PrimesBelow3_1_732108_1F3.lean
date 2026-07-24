
import IdealArithmetic.Examples.NF3_1_732108_1.RI3_1_732108_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [110, 91, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 131, 11], [13, 7, 128], [0, 1]]
 g := ![![[54, 43, 118], [109, 4, 47], [21, 125], [58, 32, 41], [116, 31], [50, 1], []], ![[44, 39, 7, 117], [49, 11, 122, 30], [106, 44], [19, 79, 68, 55], [102, 65], [65, 49], [36, 121]], ![[133, 133, 126, 87], [16, 79, 64, 27], [130, 120], [92, 31, 85, 85], [29, 46], [97, 64], [58, 121]]]
 h' := ![![[37, 131, 11], [103, 73, 37], [110, 77, 66], [14, 16, 79], [14, 70, 67], [60, 66, 46], [0, 0, 1], [0, 1]], ![[13, 7, 128], [67, 33, 89], [4, 15, 58], [108, 6, 34], [116, 129, 127], [76, 55, 75], [50, 58, 7], [37, 131, 11]], ![[0, 1], [39, 33, 13], [123, 47, 15], [84, 117, 26], [119, 79, 84], [23, 18, 18], [44, 81, 131], [13, 7, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 77], []]
 b := ![[], [57, 54, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [110, 91, 89, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246169, -184731, -202940]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1771, -1329, -1460]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![21, 27, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![21, 27, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![21, 27, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![21, 27, 1], ![-17, 42, 134], ![990, -877, -38]]]
  hmulB := by decide  
  f := ![![![-20, -27, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -27, 149]], ![![0, 0, 1], ![-19, -24, 134], ![12, 1, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [38, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 148], [0, 1]]
 g := ![![[55, 143], [119], [85, 88], [31], [126, 86], [16], [1]], ![[79, 6], [119], [31, 61], [31], [80, 63], [16], [1]]]
 h' := ![![[145, 148], [17, 128], [48, 87], [116, 104], [129, 39], [91, 91], [111, 145], [0, 1]], ![[0, 1], [101, 21], [147, 62], [147, 45], [122, 110], [25, 58], [127, 4], [145, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [57, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [38, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![515, 428, -4708]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![667, 856, -4708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![15, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![15, 1, 0]] 
 ![![149, 0, 0], ![15, 1, 0], ![38, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![15, 1, 0], ![-2, 17, 5], ![37, -33, 14]]]
  hmulB := by decide  
  f := ![![![-2899, 24650, 7250], ![0, -216050, 0]], ![![-290, 2465, 725], ![1, -21605, 0]], ![![-748, 6286, 1849], ![86, -55100, 0]]]
  g := ![![![1, 0, 0], ![-15, 149, 0], ![-38, 0, 149]], ![![0, 1, 0], ![-3, 17, 5], ![0, -33, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![21, 27, 1]] ![![149, 0, 0], ![15, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![2235, 149, 0]], ![![3129, 4023, 149], ![298, 447, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![15, 1, 0]]], ![![![21, 27, 1]], ![![2, 3, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10992788, 142079, 336954]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![10992788, 142079, 336954]] 
 ![![151, 0, 0], ![58, 1, 0], ![119, 0, 1]] where
  M :=![![![10992788, 142079, 336954], ![12183140, 157464, 373441], ![2224337, 28749, 68181]]]
  hmulB := by decide  
  f := ![![![-2325, 2247, -817]], ![![-1123, 1056, -234]], ![![-1233, 1204, -501]]]
  g := ![![![-247320, 142079, 336954], ![-274101, 157464, 373441], ![-50044, 28749, 68181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-234, 200, 61]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-234, 200, 61]] 
 ![![151, 0, 0], ![94, 1, 0], ![37, 0, 1]] where
  M :=![![![-234, 200, 61], ![1857, -1847, 939], ![6851, -5746, -2386]]]
  hmulB := by decide  
  f := ![![![9802436, 126694, 300467]], ![![6174125, 79799, 189251]], ![![2415057, 31214, 74027]]]
  g := ![![![-141, 200, 61], ![932, -1847, 939], ![4207, -5746, -2386]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![151, 0, 0], ![149, 1, 0], ![60, 0, 1]] where
  M :=![![![-2, 1, 0], ![-2, 0, 5], ![37, -33, -3]]]
  hmulB := by decide  
  f := ![![![-165, -3, -5]], ![![-164, -3, -5]], ![![-66, -1, -2]]]
  g := ![![![-1, 1, 0], ![-2, 0, 5], ![34, -33, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![10992788, 142079, 336954]] ![![-234, 200, 61]]
  ![![165, 3, 5]] where
 M := ![![![165, 3, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![165, 3, 5]] ![![-2, 1, 0]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [145, 112, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 154, 124], [109, 2, 33], [0, 1]]
 g := ![![[4, 66, 120], [128, 143], [149, 53, 120], [77, 5, 35], [52, 138, 141], [0, 1], []], ![[114, 116, 72, 4], [91, 141], [107, 128, 1, 113], [34, 60, 125, 105], [36, 33, 117, 86], [96, 4], [41, 147]], ![[86, 133, 49, 46], [113, 86], [21, 98, 92, 121], [44, 80, 143, 68], [148, 5, 115, 67], [144, 9], [132, 147]]]
 h' := ![![[48, 154, 124], [76, 135, 77], [61, 129, 65], [139, 87, 77], [153, 71, 52], [0, 12, 45], [0, 0, 1], [0, 1]], ![[109, 2, 33], [7, 30, 95], [64, 74, 112], [121, 17, 109], [117, 93, 116], [11, 102, 8], [127, 24, 2], [48, 154, 124]], ![[0, 1], [10, 149, 142], [99, 111, 137], [22, 53, 128], [2, 150, 146], [114, 43, 104], [120, 133, 154], [109, 2, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 53], []]
 b := ![[], [77, 108, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [145, 112, 0, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11664095985, -9097282732, -7824865242]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![74293605, -57944476, -49839906]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [7, 86, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 152, 96], [83, 10, 67], [0, 1]]
 g := ![![[85, 49, 88], [25, 148, 150], [139, 34], [144, 84], [80, 60], [117, 140, 1], []], ![[90, 157, 20, 6], [25, 93, 110, 88], [62, 85], [81, 115], [151, 151], [149, 130, 5, 146], [102, 88]], ![[73, 11, 36, 66], [82, 157, 20, 125], [66, 54], [134, 33], [32, 87], [13, 86, 77, 120], [131, 88]]]
 h' := ![![[57, 152, 96], [151, 114, 67], [140, 133, 65], [61, 89, 94], [108, 25, 35], [159, 42, 95], [0, 0, 1], [0, 1]], ![[83, 10, 67], [128, 161, 41], [42, 46, 52], [65, 145, 30], [119, 36, 142], [19, 126, 92], [90, 116, 10], [57, 152, 96]], ![[0, 1], [118, 51, 55], [9, 147, 46], [109, 92, 39], [118, 102, 149], [159, 158, 139], [104, 47, 152], [83, 10, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 142], []]
 b := ![[], [92, 154, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [7, 86, 23, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216138, 168216, -1989741]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1326, 1032, -12207]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-50, -72, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-50, -72, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![117, 95, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-50, -72, 1], ![181, -227, -361], ![-2673, 2390, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-117, -95, 167]], ![![-1, -1, 1], ![254, 204, -361], ![-9, 20, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [37, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 166], [0, 1]]
 g := ![![[85, 137], [131, 76], [39, 18], [127], [19], [7, 116], [1]], ![[80, 30], [88, 91], [42, 149], [127], [19], [82, 51], [1]]]
 h' := ![![[28, 166], [163, 114], [60, 110], [39, 39], [79, 131], [75, 112], [130, 28], [0, 1]], ![[0, 1], [15, 53], [134, 57], [129, 128], [73, 36], [38, 55], [79, 139], [28, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [20, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [37, 139, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1186, -1051, -1500]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1058, 847, -1500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![27, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![27, 1, 0]] 
 ![![167, 0, 0], ![27, 1, 0], ![10, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![27, 1, 0], ![-2, 29, 5], ![37, -33, 26]]]
  hmulB := by decide  
  f := ![![![12511, -183750, -31680], ![1002, 1058112, 0]], ![![2021, -29697, -5120], ![168, 171008, 0]], ![![749, -11003, -1897], ![61, 63360, 0]]]
  g := ![![![1, 0, 0], ![-27, 167, 0], ![-10, 0, 167]], ![![0, 1, 0], ![-5, 29, 5], ![4, -33, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-50, -72, 1]] ![![167, 0, 0], ![27, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![4509, 167, 0]], ![![-8350, -12024, 167], ![-1169, -2171, -334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![27, 1, 0]]], ![![![-50, -72, 1]], ![![-7, -13, -2]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-60, 68, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-60, 68, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![113, 68, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-60, 68, 1], ![-99, 43, 339], ![2507, -2230, -160]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -68, 173]], ![![-1, 0, 1], ![-222, -133, 339], ![119, 50, -160]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [33, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 172], [0, 1]]
 g := ![![[24, 21], [77], [46, 157], [111, 164], [89], [139, 139], [1]], ![[0, 152], [77], [89, 16], [146, 9], [89], [79, 34], [1]]]
 h' := ![![[73, 172], [18, 59], [39, 115], [143, 147], [140, 67], [84, 75], [140, 73], [0, 1]], ![[0, 1], [0, 114], [130, 58], [148, 26], [14, 106], [23, 98], [106, 100], [73, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [134, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [33, 100, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11724, -8028, 981]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-573, -432, 981]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![7, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![7, 1, 0]] 
 ![![173, 0, 0], ![7, 1, 0], ![160, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![7, 1, 0], ![-2, 9, 5], ![37, -33, 6]]]
  hmulB := by decide  
  f := ![![![23153, -104249, -57915], ![346, 2003859, 0]], ![![929, -4213, -2340], ![174, 80964, 0]], ![![21408, -96416, -53563], ![448, 1853280, 0]]]
  g := ![![![1, 0, 0], ![-7, 173, 0], ![-160, 0, 173]], ![![0, 1, 0], ![-5, 9, 5], ![-4, -33, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-60, 68, 1]] ![![173, 0, 0], ![7, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![1211, 173, 0]], ![![-10380, 11764, 173], ![-519, 519, 346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![7, 1, 0]]], ![![![-60, 68, 1]], ![![-3, 3, 2]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![97, -17, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![97, -17, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![97, 162, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![97, -17, 1], ![71, 30, -86], ![-638, 575, 82]]]
  hmulB := by decide  
  f := ![![![-96, 17, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -162, 179]], ![![0, -1, 1], ![47, 78, -86], ![-48, -71, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [86, 158, 1] where
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
 g := ![![[6, 19], [155, 61], [64], [121], [174, 66], [100, 83], [1]], ![[47, 160], [4, 118], [64], [121], [128, 113], [53, 96], [1]]]
 h' := ![![[21, 178], [95, 127], [111, 132], [148, 8], [72, 11], [171, 31], [93, 21], [0, 1]], ![[0, 1], [77, 52], [19, 47], [137, 171], [124, 168], [106, 148], [176, 158], [21, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [146, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [86, 158, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![583, 206, -3371]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1830, 3052, -3371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![86, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![86, 1, 0]] 
 ![![179, 0, 0], ![86, 1, 0], ![97, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![86, 1, 0], ![-2, 88, 5], ![37, -33, 85]]]
  hmulB := by decide  
  f := ![![![3447, -170549, -9690], ![895, 346902, 0]], ![![1690, -81930, -4655], ![359, 166649, 0]], ![![1903, -92420, -5251], ![412, 187986, 0]]]
  g := ![![![1, 0, 0], ![-86, 179, 0], ![-97, 0, 179]], ![![0, 1, 0], ![-45, 88, 5], ![-30, -33, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![97, -17, 1]] ![![179, 0, 0], ![86, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15394, 179, 0]], ![![17363, -3043, 179], ![8413, -1432, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![86, 1, 0]]], ![![![97, -17, 1]], ![![47, -8, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-74, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-74, 1, 0]] 
 ![![181, 0, 0], ![107, 1, 0], ![20, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-74, 1, 0], ![-2, -72, 5], ![37, -33, -75]]]
  hmulB := by decide  
  f := ![![![3973, 153652, -10670], ![-724, 386254, 0]], ![![2375, 90794, -6305], ![-361, 228241, 0]], ![![448, 16978, -1179], ![-58, 42680, 0]]]
  g := ![![![1, 0, 0], ![-107, 181, 0], ![-20, 0, 181]], ![![-1, 1, 0], ![42, -72, 5], ![28, -33, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-62, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-62, 1, 0]] 
 ![![181, 0, 0], ![119, 1, 0], ![52, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-62, 1, 0], ![-2, -60, 5], ![37, -33, -63]]]
  hmulB := by decide  
  f := ![![![-31033, -984989, 82080], ![5249, -2971296, 0]], ![![-20405, -647539, 53960], ![3440, -1953352, 0]], ![![-8870, -282981, 23581], ![1641, -853632, 0]]]
  g := ![![![1, 0, 0], ![-119, 181, 0], ![-52, 0, 181]], ![![-1, 1, 0], ![38, -60, 5], ![40, -33, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-46, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-46, 1, 0]] 
 ![![181, 0, 0], ![135, 1, 0], ![174, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-46, 1, 0], ![-2, -44, 5], ![37, -33, -47]]]
  hmulB := by decide  
  f := ![![![-18163, -412777, 46905], ![2353, -1697961, 0]], ![![-13531, -307834, 34980], ![1811, -1266276, 0]], ![![-17426, -396814, 45091], ![2398, -1632294, 0]]]
  g := ![![![1, 0, 0], ![-135, 181, 0], ![-174, 0, 181]], ![![-1, 1, 0], ![28, -44, 5], ![70, -33, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-74, 1, 0]] ![![181, 0, 0], ![-62, 1, 0]]
  ![![181, 0, 0], ![-24, -63, 1]] where
 M := ![![![32761, 0, 0], ![-11222, 181, 0]], ![![-13394, 181, 0], ![4586, -134, 5]]]
 hmul := by decide  
 g := ![![![![181, 0, 0], ![0, 0, 0]], ![![-38, 64, -1], ![181, 0, 0]]], ![![![-50, 64, -1], ![181, 0, 0]], ![![26, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-24, -63, 1]] ![![181, 0, 0], ![-46, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-8326, 181, 0]], ![![-4344, -11403, 181], ![1267, 2715, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-46, 1, 0]]], ![![![-24, -63, 1]], ![![7, 15, -2]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![91, 45, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![91, 45, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![91, 45, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![91, 45, 1], ![-53, 148, 224], ![1656, -1471, 14]]]
  hmulB := by decide  
  f := ![![![-90, -45, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -45, 191]], ![![0, 0, 1], ![-107, -52, 224], ![2, -11, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [12, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [188, 190], [0, 1]]
 g := ![![[48, 16], [190, 147], [121, 34], [123, 128], [162, 60], [45, 9], [1]], ![[0, 175], [131, 44], [19, 157], [121, 63], [173, 131], [18, 182], [1]]]
 h' := ![![[188, 190], [12, 4], [76, 23], [52, 15], [157, 74], [33, 92], [179, 188], [0, 1]], ![[0, 1], [0, 187], [7, 168], [7, 176], [126, 117], [139, 99], [188, 3], [188, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [147, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [12, 3, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2766, -1875, -3225]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1551, 750, -3225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-33, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-33, 1, 0]] 
 ![![191, 0, 0], ![158, 1, 0], ![177, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-33, 1, 0], ![-2, -31, 5], ![37, -33, -34]]]
  hmulB := by decide  
  f := ![![![-5570, -87888, 14175], ![573, -541485, 0]], ![![-4590, -72698, 11725], ![574, -447895, 0]], ![![-5160, -81446, 13136], ![541, -501795, 0]]]
  g := ![![![1, 0, 0], ![-158, 191, 0], ![-177, 0, 191]], ![![-1, 1, 0], ![21, -31, 5], ![59, -33, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![91, 45, 1]] ![![191, 0, 0], ![-33, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-6303, 191, 0]], ![![17381, 8595, 191], ![-3056, -1337, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-33, 1, 0]]], ![![![91, 45, 1]], ![![-16, -7, 1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![5, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![5, 1, 0]] 
 ![![193, 0, 0], ![5, 1, 0], ![147, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![5, 1, 0], ![-2, 7, 5], ![37, -33, 4]]]
  hmulB := by decide  
  f := ![![![39895, -139666, -99760], ![386, 3850736, 0]], ![![1027, -3613, -2580], ![194, 99588, 0]], ![![30385, -106378, -75983], ![346, 2932944, 0]]]
  g := ![![![1, 0, 0], ![-5, 193, 0], ![-147, 0, 193]], ![![0, 1, 0], ![-4, 7, 5], ![-2, -33, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![56, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![56, 1, 0]] 
 ![![193, 0, 0], ![56, 1, 0], ![122, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![56, 1, 0], ![-2, 58, 5], ![37, -33, 55]]]
  hmulB := by decide  
  f := ![![![45189, -1362452, -117450], ![6176, 4533570, 0]], ![![13070, -395280, -34075], ![1931, 1315295, 0]], ![![28570, -861239, -74243], ![3887, 2865780, 0]]]
  g := ![![![1, 0, 0], ![-56, 193, 0], ![-122, 0, 193]], ![![0, 1, 0], ![-20, 58, 5], ![-25, -33, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-62, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-62, 1, 0]] 
 ![![193, 0, 0], ![131, 1, 0], ![182, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-62, 1, 0], ![-2, -60, 5], ![37, -33, -63]]]
  hmulB := by decide  
  f := ![![![7749, 243606, -20300], ![-1158, 783580, 0]], ![![5263, 165304, -13775], ![-771, 531715, 0]], ![![7290, 229722, -19143], ![-1146, 738920, 0]]]
  g := ![![![1, 0, 0], ![-131, 193, 0], ![-182, 0, 193]], ![![-1, 1, 0], ![36, -60, 5], ![82, -33, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![5, 1, 0]] ![![193, 0, 0], ![56, 1, 0]]
  ![![193, 0, 0], ![17, -26, 1]] where
 M := ![![![37249, 0, 0], ![10808, 193, 0]], ![![965, 193, 0], ![278, 63, 5]]]
 hmul := by decide  
 g := ![![![![176, 26, -1], ![193, 0, 0]], ![![39, 27, -1], ![193, 0, 0]]], ![![![-12, 27, -1], ![193, 0, 0]], ![![1, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![17, -26, 1]] ![![193, 0, 0], ![-62, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-11966, 193, 0]], ![![3281, -5018, 193], ![-965, 1544, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-62, 1, 0]]], ![![![17, -26, 1]], ![![-5, 8, -1]]]]
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


lemma PB243I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB243I3 : PrimesBelowBoundCertificateInterval O 137 193 243 where
  m := 11
  g := ![1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB243I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
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
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![36481, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
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
      exact NI193N2
  β := ![I149N1, I151N0, I151N1, I151N2, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N1], [I151N0, I151N1, I151N2], [], [], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
