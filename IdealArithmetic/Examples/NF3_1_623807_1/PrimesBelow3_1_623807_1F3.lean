
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [101, 13, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 134, 85], [31, 4, 54], [0, 1]]
 g := ![![[43, 92, 11], [85, 42, 6], [128, 57], [11, 50, 49], [31, 16], [136, 1], []], ![[68, 36, 84, 130], [13, 22, 96, 48], [104, 136], [24, 71, 48, 101], [110, 16], [125, 16], [132, 136]], ![[132, 41, 54, 31], [132, 91, 122, 129], [132, 71], [79, 58, 11, 118], [4, 64], [37, 25], [24, 136]]]
 h' := ![![[105, 134, 85], [33, 74, 122], [0, 17, 59], [1, 105, 14], [135, 24, 7], [25, 77, 135], [0, 0, 1], [0, 1]], ![[31, 4, 54], [40, 79, 106], [85, 131, 13], [134, 21, 85], [128, 14, 122], [102, 15, 135], [56, 39, 4], [105, 134, 85]], ![[0, 1], [93, 125, 50], [112, 130, 67], [10, 13, 40], [90, 101, 10], [63, 47, 8], [66, 100, 134], [31, 4, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 17], []]
 b := ![[], [36, 84, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [101, 13, 3, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311499, -1390, -2085]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2241, -10, -15]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-73, -73, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-73, -73, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![76, 76, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-73, -73, 1], ![152, -146, -147], ![-11248, 76, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -76, 149]], ![![-1, -1, 1], ![76, 74, -147], ![-76, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [54, 4, 1] where
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
 g := ![![[127, 69], [68], [15, 63], [26], [76, 132], [16], [1]], ![[0, 80], [68], [61, 86], [26], [144, 17], [16], [1]]]
 h' := ![![[145, 148], [106, 101], [84, 51], [91, 130], [68, 131], [115, 70], [95, 145], [0, 1]], ![[0, 1], [0, 48], [29, 98], [18, 19], [140, 18], [133, 79], [111, 4], [145, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [54, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1165, 1219, 18]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -1, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-2, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-2, 1, 0]] 
 ![![149, 0, 0], ![147, 1, 0], ![148, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-2, 1, 0], ![0, -1, 2], ![152, 0, -3]]]
  hmulB := by decide  
  f := ![![![3, 73, -148], ![149, 11026, 0]], ![![1, 73, -146], ![1, 10877, 0]], ![![2, 73, -147], ![75, 10952, 0]]]
  g := ![![![1, 0, 0], ![-147, 149, 0], ![-148, 0, 149]], ![![-1, 1, 0], ![-1, -1, 2], ![4, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-73, -73, 1]] ![![149, 0, 0], ![-2, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-298, 149, 0]], ![![-10877, -10877, 149], ![298, 0, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-2, 1, 0]]], ![![![-73, -73, 1]], ![![2, 0, -1]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [48, 111, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 58, 45], [93, 92, 106], [0, 1]]
 g := ![![[50, 24, 105], [127, 22, 21], [77, 122, 44], [7, 80], [83, 45, 64], [109, 1], []], ![[144, 88, 56, 36], [118, 121, 110, 103], [110, 45, 120, 21], [97, 31], [32, 46, 112, 99], [53, 8], [49, 62]], ![[80, 34, 19, 41], [68, 121, 39, 54], [29, 87, 126, 24], [145, 95], [94, 99, 70, 107], [3, 42], [139, 62]]]
 h' := ![![[16, 58, 45], [95, 148, 16], [79, 6, 25], [8, 59, 73], [93, 43, 69], [53, 84, 143], [0, 0, 1], [0, 1]], ![[93, 92, 106], [33, 129, 129], [21, 57, 3], [1, 114, 9], [60, 54, 129], [45, 115, 24], [18, 85, 92], [16, 58, 45]], ![[0, 1], [40, 25, 6], [81, 88, 123], [24, 129, 69], [75, 54, 104], [52, 103, 135], [14, 66, 58], [93, 92, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 91], []]
 b := ![[], [137, 67, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [48, 111, 42, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85768, -11476, -6946]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-568, -76, -46]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [155, 40, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 14, 87], [88, 142, 70], [0, 1]]
 g := ![![[112, 4, 52], [156, 12], [145, 82, 148], [121, 103, 124], [110, 139, 40], [155, 1], []], ![[26, 145, 107, 85], [91, 141], [108, 130, 124, 74], [20, 28, 145, 149], [31, 75, 121, 7], [110, 68], [15, 33]], ![[147, 152, 2, 63], [119, 67], [110, 32, 140, 70], [93, 85, 32, 151], [38, 99, 115, 114], [26, 39], [32, 33]]]
 h' := ![![[67, 14, 87], [103, 94, 44], [133, 19, 13], [85, 120, 84], [63, 133, 81], [153, 82, 121], [0, 0, 1], [0, 1]], ![[88, 142, 70], [38, 76, 139], [22, 128, 45], [88, 112, 74], [97, 36, 151], [120, 93, 138], [123, 86, 142], [67, 14, 87]], ![[0, 1], [90, 144, 131], [3, 10, 99], [52, 82, 156], [44, 145, 82], [89, 139, 55], [115, 71, 14], [88, 142, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 106], []]
 b := ![[], [121, 154, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [155, 40, 2, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1444714, 2198, 5495]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9202, 14, 35]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43699187463475, 7568893423446, 1947351927150]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![43699187463475, 7568893423446, 1947351927150]] 
 ![![163, 0, 0], ![0, 163, 0], ![86, 117, 1]] where
  M :=![![![43699187463475, 7568893423446, 1947351927150], ![295997492926800, 51268080886921, 13190434919742], ![854474307436992, 147998746463400, 38077645967179]]]
  hmulB := by decide  
  f := ![![![-1006607, -759318, 314514]], ![![47806128, -1765925, -1833150]], ![![32782370, -1521543, -1149467]]]
  g := ![![![-759344038475, -1351357558608, 1947351927150], ![-5143435031724, -9153452789711, 13190434919742], ![-14847872673254, -26423839458261, 38077645967179]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [38, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 162], [0, 1]]
 g := ![![[106, 133], [161, 9], [150], [93], [21], [6, 90], [1]], ![[0, 30], [95, 154], [150], [93], [21], [161, 73], [1]]]
 h' := ![![[47, 162], [76, 40], [65, 3], [68, 98], [4, 16], [98, 99], [125, 47], [0, 1]], ![[0, 1], [0, 123], [43, 160], [110, 65], [104, 147], [24, 64], [52, 116], [47, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [86, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [38, 116, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![494, 456, -343]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![184, 249, -343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1006607, 759318, -314514]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![1006607, 759318, -314514]] 
 ![![163, 0, 0], ![93, 1, 0], ![30, 0, 1]] where
  M :=![![![1006607, 759318, -314514], ![-47806128, 1765925, 1833150], ![163222464, -23903064, -67225]]]
  hmulB := by decide  
  f := ![![![-43699187463475, -7568893423446, -1947351927150]], ![![-26748600779325, -4632976498573, -1191988737084]], ![![-13284968903934, -2301015639060, -592013520133]]]
  g := ![![![-369169, 759318, -314514], ![-1638231, 1765925, 1833150], ![14651682, -23903064, -67225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![43699187463475, 7568893423446, 1947351927150]] ![![1006607, 759318, -314514]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541395, -93772, -24126]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-541395, -93772, -24126]] 
 ![![167, 0, 0], ![0, 167, 0], ![49, 106, 1]] where
  M :=![![![-541395, -93772, -24126], ![-3667152, -635167, -163418], ![-10586192, -1833576, -471749]]]
  hmulB := by decide  
  f := ![![![-445, -44, 38]], ![![5776, -489, -126]], ![![3461, -306, -71]]]
  g := ![![![3837, 14752, -24126], ![25990, 99923, -163418], ![75027, 288454, -471749]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [25, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 166], [0, 1]]
 g := ![![[34, 147], [107, 93], [139, 47], [84], [61], [47, 58], [1]], ![[0, 20], [48, 74], [102, 120], [84], [61], [12, 109], [1]]]
 h' := ![![[152, 166], [164, 100], [32, 60], [100, 61], [14, 77], [161, 140], [142, 152], [0, 1]], ![[0, 1], [0, 67], [134, 107], [20, 106], [28, 90], [65, 27], [33, 15], [152, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [60, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [25, 15, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60689, 34256, 758]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![141, -276, 758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![445, 44, -38]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![445, 44, -38]] 
 ![![167, 0, 0], ![123, 1, 0], ![56, 0, 1]] where
  M :=![![![445, 44, -38], ![-5776, 489, 126], ![12464, -2888, 363]]]
  hmulB := by decide  
  f := ![![![541395, 93772, 24126]], ![![420711, 72869, 18748]], ![![244936, 42424, 10915]]]
  g := ![![![-17, 44, -38], ![-437, 489, 126], ![2080, -2888, 363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-541395, -93772, -24126]] ![![445, 44, -38]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [171, 7, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 165, 58], [99, 7, 115], [0, 1]]
 g := ![![[36, 110, 130], [7, 54], [12, 18, 37], [157, 121, 151], [126, 138], [170, 171, 1], []], ![[12, 132, 71, 145], [104, 16], [32, 59, 128, 8], [130, 100, 67, 165], [41, 24], [145, 123, 46, 74], [129, 77]], ![[13, 172, 18, 125], [148, 57], [38, 55, 69, 162], [104, 138, 18, 71], [126, 152], [134, 141, 134, 94], [72, 77]]]
 h' := ![![[72, 165, 58], [71, 24, 87], [24, 111, 20], [141, 85, 27], [115, 55, 18], [167, 17, 22], [0, 0, 1], [0, 1]], ![[99, 7, 115], [22, 155, 98], [81, 17, 4], [90, 66, 102], [134, 115, 29], [15, 81, 102], [79, 2, 7], [72, 165, 58]], ![[0, 1], [67, 167, 161], [64, 45, 149], [98, 22, 44], [152, 3, 126], [65, 75, 49], [84, 171, 165], [99, 7, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 91], []]
 b := ![[], [118, 14, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [171, 7, 2, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12629, 1384, 692]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 8, 4]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1966800159, -340658526, -87645842]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-1966800159, -340658526, -87645842]] 
 ![![179, 0, 0], ![0, 179, 0], ![25, 136, 1]] where
  M :=![![![-1966800159, -340658526, -87645842], ![-13322167984, -2307458685, -593671210], ![-38457927968, -6661083992, -1713787475]]]
  hmulB := by decide  
  f := ![![![51955, -4466, -1110]], ![![-168720, 47489, -7822]], ![![-123783, 34986, -5789]]]
  g := ![![![1253329, 64688134, -87645842], ![8489454, 438166625, -593671210], ![24507033, 1264882752, -1713787475]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [132, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 178], [0, 1]]
 g := ![![[124, 51], [39, 5], [14], [47], [156, 85], [19, 155], [1]], ![[33, 128], [2, 174], [14], [47], [64, 94], [125, 24], [1]]]
 h' := ![![[100, 178], [43, 92], [49, 30], [110, 67], [172, 88], [177, 117], [47, 100], [0, 1]], ![[0, 1], [114, 87], [6, 149], [8, 112], [22, 91], [63, 62], [23, 79], [100, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [53, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [132, 79, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![892, 2146, 408]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -298, 408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51955, 4466, 1110]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-51955, 4466, 1110]] 
 ![![179, 0, 0], ![87, 1, 0], ![110, 0, 1]] where
  M :=![![![-51955, 4466, 1110], ![168720, -47489, 7822], ![510112, 84360, -55311]]]
  hmulB := by decide  
  f := ![![![1966800159, 340658526, 87645842]], ![![1030356323, 178462293, 45915416]], ![![1423496902, 246555988, 63434805]]]
  g := ![![![-3143, 4466, 1110], ![19217, -47489, 7822], ![-4162, 84360, -55311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-1966800159, -340658526, -87645842]] ![![-51955, 4466, 1110]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [109, 48, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 23], [169, 174, 158], [0, 1]]
 g := ![![[151, 6, 81], [32, 145], [8, 114, 82], [30, 45], [177, 3, 116], [133, 0, 1], []], ![[52, 23, 179, 32], [91, 142], [29, 180, 42, 107], [118, 20], [139, 143, 179, 92], [138, 107, 172, 41], [95, 167]], ![[78, 78, 118, 17], [76, 79], [146, 140, 75, 124], [164, 125], [127, 104, 33, 63], [73, 77, 137, 77], [141, 167]]]
 h' := ![![[12, 6, 23], [135, 121, 9], [33, 111, 67], [34, 157, 156], [74, 154, 100], [164, 132, 72], [0, 0, 1], [0, 1]], ![[169, 174, 158], [7, 56, 5], [141, 163, 93], [173, 68, 166], [33, 76, 127], [149, 138, 179], [106, 6, 174], [12, 6, 23]], ![[0, 1], [123, 4, 167], [9, 88, 21], [123, 137, 40], [108, 132, 135], [145, 92, 111], [160, 175, 6], [169, 174, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 47], []]
 b := ![[], [24, 65, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [109, 48, 0, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2519339, -110048, -82536]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13919, -608, -456]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-79, 8, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-79, 8, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![112, 8, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-79, 8, 1], ![152, -71, 15], ![1064, 76, -86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -8, 191]], ![![-1, 0, 1], ![-8, -1, 15], ![56, 4, -86]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [33, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 190], [0, 1]]
 g := ![![[176, 67], [27, 160], [99, 125], [3, 51], [118, 92], [74, 163], [1]], ![[107, 124], [153, 31], [90, 66], [36, 140], [9, 99], [157, 28], [1]]]
 h' := ![![[113, 190], [64, 81], [171, 55], [92, 121], [117, 137], [41, 61], [158, 113], [0, 1]], ![[0, 1], [49, 110], [83, 136], [13, 70], [127, 54], [58, 130], [130, 78], [113, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [170, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [33, 78, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1064, 76, 105]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -4, 105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-15, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-15, 1, 0]] 
 ![![191, 0, 0], ![176, 1, 0], ![86, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-15, 1, 0], ![0, -14, 2], ![152, 0, -16]]]
  hmulB := by decide  
  f := ![![![856, -57, 0], ![10887, 0, 0]], ![![796, -53, 0], ![10124, 0, 0]], ![![376, -18, -1], ![4782, 96, 0]]]
  g := ![![![1, 0, 0], ![-176, 191, 0], ![-86, 0, 191]], ![![-1, 1, 0], ![12, -14, 2], ![8, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-79, 8, 1]] ![![191, 0, 0], ![-15, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2865, 191, 0]], ![![-15089, 1528, 191], ![1337, -191, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-15, 1, 0]]], ![![![-79, 8, 1]], ![![7, -1, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [51, 121, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 153, 77], [105, 39, 116], [0, 1]]
 g := ![![[127, 128, 185], [94, 8], [89, 121], [113, 124], [131, 144], [120, 9], [1]], ![[190, 84, 183, 88], [90, 16], [21, 192], [91, 95], [86, 147], [111, 143], [105, 171, 40, 88]], ![[172, 191, 104, 152], [78, 84], [56, 165], [44, 144], [164, 62], [186, 14], [111, 129, 122, 105]]]
 h' := ![![[85, 153, 77], [25, 56, 125], [90, 188, 104], [24, 3, 11], [169, 98, 33], [148, 65, 181], [142, 72, 190], [0, 1]], ![[105, 39, 116], [128, 86, 116], [146, 162, 4], [161, 43, 81], [39, 43, 148], [117, 47, 98], [48, 146, 23], [85, 153, 77]], ![[0, 1], [158, 51, 145], [135, 36, 85], [17, 147, 101], [36, 52, 12], [78, 81, 107], [140, 168, 173], [105, 39, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 186], []]
 b := ![[], [99, 141, 158], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [51, 121, 3, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2492016, -27985, -33582]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12912, -145, -174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB224I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB224I3 : PrimesBelowBoundCertificateInterval O 137 193 224 where
  m := 11
  g := ![1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB224I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
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
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![7189057]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I163N1, I167N1, I179N1, I191N1]
  Il := ![[], [I149N1], [], [], [I163N1], [I167N1], [], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
