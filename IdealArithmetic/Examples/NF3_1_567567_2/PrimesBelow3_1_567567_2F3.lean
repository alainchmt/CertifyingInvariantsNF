
import IdealArithmetic.Examples.NF3_1_567567_2.RI3_1_567567_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![49, 28, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![49, 28, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![49, 28, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![49, 28, 1], ![157, 50, 111], ![2764, -724, -6]]]
  hmulB := by decide  
  f := ![![![-48, -28, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -28, 139]], ![![0, 0, 1], ![-38, -22, 111], ![22, -4, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [52, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 138], [0, 1]]
 g := ![![[1, 131], [39, 79], [100], [13, 7], [124], [63], [1]], ![[0, 8], [101, 60], [100], [66, 132], [124], [63], [1]]]
 h' := ![![[87, 138], [57, 100], [26, 45], [19, 10], [63, 110], [123, 47], [87, 87], [0, 1]], ![[0, 1], [0, 39], [49, 94], [55, 129], [42, 29], [42, 92], [11, 52], [87, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [55, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [52, 52, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33, 416, -1256]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![443, 256, -1256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![28, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![28, 1, 0]] 
 ![![139, 0, 0], ![28, 1, 0], ![6, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![28, 1, 0], ![2, 29, 4], ![101, -27, 27]]]
  hmulB := by decide  
  f := ![![![193, 3189, 440], ![139, -15290, 0]], ![![16, 637, 88], ![140, -3058, 0]], ![![-10, 137, 19], ![97, -660, 0]]]
  g := ![![![1, 0, 0], ![-28, 139, 0], ![-6, 0, 139]], ![![0, 1, 0], ![-6, 29, 4], ![5, -27, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![49, 28, 1]] ![![139, 0, 0], ![28, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3892, 139, 0]], ![![6811, 3892, 139], ![1529, 834, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![28, 1, 0]]], ![![![49, 28, 1]], ![![11, 6, 1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [90, 38, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 130, 98], [122, 18, 51], [0, 1]]
 g := ![![[97, 97, 54], [142, 67], [80, 85, 107], [116, 69], [114, 42, 112], [34, 1], []], ![[33, 6, 95, 77], [136, 7], [31, 91, 75, 32], [49, 39], [46, 21, 143, 136], [13, 26], [78, 68]], ![[64, 115], [55, 119], [146, 133, 62, 57], [63, 102], [122, 130, 89, 32], [72, 63], [125, 68]]]
 h' := ![![[61, 130, 98], [103, 133, 59], [101, 145, 118], [133, 24, 16], [21, 76, 101], [69, 108, 75], [0, 0, 1], [0, 1]], ![[122, 18, 51], [123, 23, 90], [61, 110, 93], [69, 84, 107], [3, 65, 28], [16, 144, 14], [128, 71, 18], [61, 130, 98]], ![[0, 1], [83, 142], [50, 43, 87], [115, 41, 26], [102, 8, 20], [13, 46, 60], [58, 78, 130], [122, 18, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 108], []]
 b := ![[], [1, 128, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [90, 38, 115, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![427034, -119200, 0]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2866, -800, 0]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [5, 31, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 50, 123], [24, 100, 28], [0, 1]]
 g := ![![[101, 37, 44], [76, 116, 78], [59, 20, 49], [65, 95], [89, 60, 4], [123, 1], []], ![[39, 82, 33, 123], [93, 47, 75, 103], [141, 28, 16, 17], [116, 144], [105, 150, 71, 19], [77, 34], [12, 29]], ![[92, 41, 51, 63], [99, 95, 48, 117], [119, 52, 57, 129], [11, 17], [33, 66, 65, 140], [78, 84], [107, 29]]]
 h' := ![![[99, 50, 123], [73, 133, 78], [7, 54, 94], [41, 30, 144], [8, 82, 47], [140, 108, 149], [0, 0, 1], [0, 1]], ![[24, 100, 28], [69, 134, 150], [58, 144, 36], [56, 145, 121], [118, 104, 139], [108, 73, 98], [77, 21, 100], [99, 50, 123]], ![[0, 1], [121, 35, 74], [23, 104, 21], [21, 127, 37], [128, 116, 116], [83, 121, 55], [41, 130, 50], [24, 100, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 19], []]
 b := ![[], [43, 3, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [5, 31, 28, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16748943103, 7171074560, -5127200168]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110920153, 47490560, -33954968]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [112, 151, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 41, 156], [90, 115, 1], [0, 1]]
 g := ![![[69, 34, 36], [119, 90], [81, 36, 145], [73, 122, 93], [149, 68, 106], [55, 1], []], ![[68, 57, 148, 46], [141, 10], [87, 136, 101, 144], [111, 126, 110, 56], [134, 96, 53, 117], [16, 37], [130, 1]], ![[98, 95, 97, 11], [59, 40], [101, 9, 45, 156], [113, 18, 52, 44], [76, 103, 34, 144], [153, 111], [128, 1]]]
 h' := ![![[122, 41, 156], [74, 136, 151], [34, 52, 103], [145, 37, 107], [111, 142, 67], [120, 61, 48], [0, 0, 1], [0, 1]], ![[90, 115, 1], [121, 105, 116], [29, 150, 18], [77, 147, 22], [50, 59, 27], [35, 111, 121], [10, 153, 115], [122, 41, 156]], ![[0, 1], [118, 73, 47], [140, 112, 36], [19, 130, 28], [139, 113, 63], [29, 142, 145], [44, 4, 41], [90, 115, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 29], []]
 b := ![[], [104, 140, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [112, 151, 102, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1466380, 599426, -358588]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9340, 3818, -2284]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-17, 64, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-17, 64, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![146, 64, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-17, 64, 1], ![229, 20, 255], ![6400, -1696, -108]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -64, 163]], ![![-1, 0, 1], ![-227, -100, 255], ![136, 32, -108]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [108, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 162], [0, 1]]
 g := ![![[107, 15], [56, 38], [74], [9], [41], [100, 126], [1]], ![[36, 148], [50, 125], [74], [9], [41], [123, 37], [1]]]
 h' := ![![[17, 162], [146, 129], [64, 110], [45, 143], [107, 3], [121, 82], [55, 17], [0, 1]], ![[0, 1], [57, 34], [141, 53], [31, 20], [158, 160], [48, 81], [18, 146], [17, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [9, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [108, 146, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-193, 228, -1820]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1629, 716, -1820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![71, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![71, 1, 0]] 
 ![![163, 0, 0], ![71, 1, 0], ![108, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![71, 1, 0], ![2, 72, 4], ![101, -27, 70]]]
  hmulB := by decide  
  f := ![![![-10975, -517776, -28768], ![-7824, 1172296, 0]], ![![-4773, -225483, -12528], ![-3422, 510516, 0]], ![![-7250, -343066, -19061], ![-5234, 776736, 0]]]
  g := ![![![1, 0, 0], ![-71, 163, 0], ![-108, 0, 163]], ![![0, 1, 0], ![-34, 72, 4], ![-34, -27, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-17, 64, 1]] ![![163, 0, 0], ![71, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![11573, 163, 0]], ![![-2771, 10432, 163], ![-978, 4564, 326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![71, 1, 0]]], ![![![-17, 64, 1]], ![![-6, 28, 2]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [10, 5, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 36, 99], [80, 130, 68], [0, 1]]
 g := ![![[27, 88, 50], [16, 44, 108], [165, 117, 27], [7, 152], [80, 84], [23, 144, 1], []], ![[115, 109, 73, 115], [39, 116, 7, 18], [124, 57, 135, 66], [4, 154], [86, 27], [133, 122, 140, 94], [141, 115]], ![[0, 50, 24, 95], [29, 102, 66, 134], [162, 127, 5, 140], [48, 18], [65, 31], [102, 97, 128, 119], [5, 115]]]
 h' := ![![[64, 36, 99], [7, 47, 102], [20, 86, 38], [113, 37, 19], [163, 135, 94], [104, 115, 77], [0, 0, 1], [0, 1]], ![[80, 130, 68], [101, 101, 44], [44, 162, 94], [75, 32, 121], [99, 116, 34], [25, 23, 19], [14, 81, 130], [64, 36, 99]], ![[0, 1], [0, 19, 21], [38, 86, 35], [143, 98, 27], [150, 83, 39], [93, 29, 71], [4, 86, 36], [80, 130, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 82], []]
 b := ![[], [146, 26, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [10, 5, 23, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112524099, -62140533, 66163563]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![673797, -372099, 396189]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-48, -19, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-48, -19, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![125, 154, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-48, -19, 1], ![63, -94, -77], ![-1983, 545, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -154, 173]], ![![-1, -1, 1], ![56, 68, -77], ![29, 53, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [20, 100, 1] where
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
 g := ![![[5, 29], [78], [83, 92], [90, 25], [158], [134, 139], [1]], ![[46, 144], [78], [52, 81], [12, 148], [158], [74, 34], [1]]]
 h' := ![![[73, 172], [53, 78], [70, 123], [103, 145], [86, 5], [88, 136], [153, 73], [0, 1]], ![[0, 1], [38, 95], [53, 50], [135, 28], [105, 168], [155, 37], [119, 100], [73, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [98, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [20, 100, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-343, 185, -119]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 107, -119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![77, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![77, 1, 0]] 
 ![![173, 0, 0], ![77, 1, 0], ![56, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![77, 1, 0], ![2, 78, 4], ![101, -27, 76]]]
  hmulB := by decide  
  f := ![![![1617, 87040, 4464], ![1384, -193068, 0]], ![![684, 38684, 1984], ![693, -85808, 0]], ![![539, 28175, 1445], ![413, -62496, 0]]]
  g := ![![![1, 0, 0], ![-77, 173, 0], ![-56, 0, 173]], ![![0, 1, 0], ![-36, 78, 4], ![-12, -27, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-48, -19, 1]] ![![173, 0, 0], ![77, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![13321, 173, 0]], ![![-8304, -3287, 173], ![-3633, -1557, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![77, 1, 0]]], ![![![-48, -19, 1]], ![![-21, -9, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![55, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![55, 1, 0]] 
 ![![179, 0, 0], ![55, 1, 0], ![36, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![55, 1, 0], ![2, 56, 4], ![101, -27, 54]]]
  hmulB := by decide  
  f := ![![![44751, 1440758, 102920], ![21838, -4605670, 0]], ![![13720, 442642, 31620], ![6803, -1414995, 0]], ![![8979, 289761, 20699], ![4461, -926280, 0]]]
  g := ![![![1, 0, 0], ![-55, 179, 0], ![-36, 0, 179]], ![![0, 1, 0], ![-18, 56, 4], ![-2, -27, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-39, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-39, 1, 0]] 
 ![![179, 0, 0], ![140, 1, 0], ![167, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-39, 1, 0], ![2, -38, 4], ![101, -27, -40]]]
  hmulB := by decide  
  f := ![![![24298, -494943, 52104], ![-8055, -2331654, 0]], ![![19010, -387071, 40748], ![-6264, -1823473, 0]], ![![22690, -461763, 48611], ![-7419, -2175342, 0]]]
  g := ![![![1, 0, 0], ![-140, 179, 0], ![-167, 0, 179]], ![![-1, 1, 0], ![26, -38, 4], ![59, -27, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-16, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-16, 1, 0]] 
 ![![179, 0, 0], ![163, 1, 0], ![30, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-16, 1, 0], ![2, -15, 4], ![101, -27, -17]]]
  hmulB := by decide  
  f := ![![![5841, -44276, 11808], ![-716, -528408, 0]], ![![5329, -40317, 10752], ![-536, -481152, 0]], ![![986, -7421, 1979], ![-41, -88560, 0]]]
  g := ![![![1, 0, 0], ![-163, 179, 0], ![-30, 0, 179]], ![![-1, 1, 0], ![13, -15, 4], ![28, -27, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![55, 1, 0]] ![![179, 0, 0], ![-39, 1, 0]]
  ![![179, 0, 0], ![46, 49, 1]] where
 M := ![![![32041, 0, 0], ![-6981, 179, 0]], ![![9845, 179, 0], ![-2143, 17, 4]]]
 hmul := by decide  
 g := ![![![![133, -49, -1], ![179, 0, 0]], ![![-39, 1, 0], ![0, 0, 0]]], ![![![9, -48, -1], ![179, 0, 0]], ![![-13, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![46, 49, 1]] ![![179, 0, 0], ![-16, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-2864, 179, 0]], ![![8234, 8771, 179], ![-537, -716, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-16, 1, 0]]], ![![![46, 49, 1]], ![![-3, -4, 1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [14, 78, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 87, 67], [123, 93, 114], [0, 1]]
 g := ![![[98, 130, 87], [37, 172], [38, 146, 161], [160, 3], [2, 84, 145], [65, 18, 1], []], ![[48, 86, 50, 49], [44, 70], [87, 5, 141, 148], [46, 39], [32, 177, 137, 119], [67, 146, 159, 102], [150, 145]], ![[77, 148, 80, 161], [84, 136], [16, 110, 24, 44], [14, 100], [170, 19, 37, 161], [19, 35, 9, 39], [103, 145]]]
 h' := ![![[76, 87, 67], [146, 149, 79], [11, 124, 57], [173, 35, 121], [153, 141, 148], [176, 108, 114], [0, 0, 1], [0, 1]], ![[123, 93, 114], [147, 139, 135], [138, 46, 34], [16, 101, 23], [152, 5, 43], [107, 39, 100], [56, 37, 93], [76, 87, 67]], ![[0, 1], [171, 74, 148], [108, 11, 90], [111, 45, 37], [44, 35, 171], [164, 34, 148], [112, 144, 87], [123, 93, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 53], []]
 b := ![[], [56, 35, 164], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [14, 78, 163, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2479700, -788074, 276568]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13700, -4354, 1528]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![60, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![60, 1, 0]] 
 ![![191, 0, 0], ![60, 1, 0], ![136, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![60, 1, 0], ![2, 61, 4], ![101, -27, 59]]]
  hmulB := by decide  
  f := ![![![9421, 333035, 21840], ![4775, -1042860, 0]], ![![2950, 104607, 6860], ![1529, -327565, 0]], ![![6716, 237135, 15551], ![3375, -742560, 0]]]
  g := ![![![1, 0, 0], ![-60, 191, 0], ![-136, 0, 191]], ![![0, 1, 0], ![-22, 61, 4], ![-33, -27, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![62, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![62, 1, 0]] 
 ![![191, 0, 0], ![62, 1, 0], ![170, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![62, 1, 0], ![2, 63, 4], ![101, -27, 61]]]
  hmulB := by decide  
  f := ![![![-4333, -157993, -10032], ![-2101, 479028, 0]], ![![-1442, -51279, -3256], ![-572, 155474, 0]], ![![-3854, -140622, -8929], ![-1878, 426360, 0]]]
  g := ![![![1, 0, 0], ![-62, 191, 0], ![-170, 0, 191]], ![![0, 1, 0], ![-24, 63, 4], ![-45, -27, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![69, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![69, 1, 0]] 
 ![![191, 0, 0], ![69, 1, 0], ![130, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![69, 1, 0], ![2, 70, 4], ![101, -27, 68]]]
  hmulB := by decide  
  f := ![![![-5738, -241903, -13824], ![-3247, 660096, 0]], ![![-2082, -87354, -4992], ![-1145, 238368, 0]], ![![-3904, -164646, -9409], ![-2214, 449280, 0]]]
  g := ![![![1, 0, 0], ![-69, 191, 0], ![-130, 0, 191]], ![![0, 1, 0], ![-28, 70, 4], ![-36, -27, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![60, 1, 0]] ![![191, 0, 0], ![62, 1, 0]]
  ![![191, 0, 0], ![71, -17, 1]] where
 M := ![![![36481, 0, 0], ![11842, 191, 0]], ![![11460, 191, 0], ![3722, 123, 4]]]
 hmul := by decide  
 g := ![![![![120, 17, -1], ![191, 0, 0]], ![![-9, 18, -1], ![191, 0, 0]]], ![![![-11, 18, -1], ![191, 0, 0]], ![![-53, 18, -1], ![195, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![71, -17, 1]] ![![191, 0, 0], ![69, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![13179, 191, 0]], ![![13561, -3247, 191], ![4966, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![69, 1, 0]]], ![![![71, -17, 1]], ![![26, -6, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [152, 53, 185, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 40, 144], [26, 152, 49], [0, 1]]
 g := ![![[89, 163, 23], [127, 161], [103, 96], [66, 31], [28, 42], [50, 64], [1]], ![[111, 154, 80, 14], [107, 97], [148, 56], [16, 86], [126, 147], [162, 86], [87, 189, 40, 81]], ![[32, 92, 135, 36], [131, 134], [101, 161], [136, 124], [22, 64], [19, 170], [109, 138, 91, 112]]]
 h' := ![![[175, 40, 144], [2, 45, 122], [149, 66, 57], [128, 111, 17], [33, 129, 113], [64, 67, 87], [41, 140, 8], [0, 1]], ![[26, 152, 49], [43, 80, 127], [148, 169, 26], [177, 141, 40], [10, 153, 47], [172, 36, 98], [51, 137, 146], [175, 40, 144]], ![[0, 1], [22, 68, 137], [21, 151, 110], [60, 134, 136], [9, 104, 33], [119, 90, 8], [43, 109, 39], [26, 152, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 137], []]
 b := ![[], [29, 134, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [152, 53, 185, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7487628, 3887985, -3438295]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38796, 20145, -17815]
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



lemma PB214I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB214I3 : PrimesBelowBoundCertificateInterval O 137 193 214 where
  m := 11
  g := ![2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB214I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![191, 191, 191]
    · exact ![7189057]
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I163N1, I173N1, I179N0, I179N1, I179N2, I191N0, I191N1, I191N2]
  Il := ![[I139N1], [], [], [], [I163N1], [], [I173N1], [I179N0, I179N1, I179N2], [], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
