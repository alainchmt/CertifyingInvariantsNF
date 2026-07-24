
import IdealArithmetic.Examples.NF3_3_815925_1.RI3_3_815925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-71, -51, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-71, -51, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![68, 88, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-71, -51, 1], ![-114, 16, -202], ![621, -1821, -136]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -88, 139]], ![![-1, -1, 1], ![98, 128, -202], ![71, 73, -136]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [36, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 138], [0, 1]]
 g := ![![[95, 112], [39, 65], [47], [113, 24], [77], [106], [1]], ![[0, 27], [0, 74], [47], [43, 115], [77], [106], [1]]]
 h' := ![![[55, 138], [125, 23], [94, 64], [102, 66], [54, 21], [121, 63], [103, 55], [0, 1]], ![[0, 1], [0, 116], [0, 75], [118, 73], [97, 118], [111, 76], [70, 84], [55, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [90, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [36, 84, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![263, 185, 844]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, -533, 844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![63, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![63, 1, 0]] 
 ![![139, 0, 0], ![63, 1, 0], ![136, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![63, 1, 0], ![2, 62, 4], ![-12, 36, 65]]]
  hmulB := by decide  
  f := ![![![-9458, -392781, -25344], ![-7089, 880704, 0]], ![![-4293, -177979, -11484], ![-3196, 399069, 0]], ![![-9272, -384304, -24797], ![-6896, 861696, 0]]]
  g := ![![![1, 0, 0], ![-63, 139, 0], ![-136, 0, 139]], ![![0, 1, 0], ![-32, 62, 4], ![-80, 36, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-71, -51, 1]] ![![139, 0, 0], ![63, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![8757, 139, 0]], ![![-9869, -7089, 139], ![-4587, -3197, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![63, 1, 0]]], ![![![-71, -51, 1]], ![![-33, -23, -1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [31, 30, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 4, 11], [106, 144, 138], [0, 1]]
 g := ![![[30, 145, 125], [49, 28], [12, 140, 80], [127, 31], [5, 26, 123], [70, 1], []], ![[87, 85, 78, 135], [147, 144], [85, 143, 29, 77], [128, 16], [1, 135, 82, 90], [103, 25], [65, 121]], ![[48, 34, 44, 15], [46, 29], [53, 140, 77, 89], [133, 61], [128, 105, 139, 3], [11, 16], [87, 121]]]
 h' := ![![[113, 4, 11], [83, 98, 42], [75, 52, 112], [122, 105, 123], [143, 140, 39], [65, 104, 102], [0, 0, 1], [0, 1]], ![[106, 144, 138], [31, 68, 123], [72, 89, 12], [136, 131, 93], [140, 25, 4], [16, 140, 38], [26, 120, 144], [113, 4, 11]], ![[0, 1], [36, 132, 133], [11, 8, 25], [73, 62, 82], [89, 133, 106], [136, 54, 9], [46, 29, 4], [106, 144, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 58], []]
 b := ![[], [68, 138, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [31, 30, 79, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331078, -279375, 610751]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2222, -1875, 4099]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [104, 1, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 78, 24], [100, 72, 127], [0, 1]]
 g := ![![[84, 33, 11], [109, 113, 137], [78, 83, 100], [30, 1], [72, 148, 128], [122, 1], []], ![[147, 149, 100, 111], [33, 101, 119, 3], [131, 129, 0, 57], [142, 21], [137, 22, 143, 41], [77, 50], [26, 123]], ![[149, 8, 87, 4], [18, 27, 86, 45], [118, 96, 4, 19], [70, 72], [64, 46, 20, 84], [52, 44], [74, 123]]]
 h' := ![![[22, 78, 24], [140, 20, 39], [42, 103, 99], [120, 51, 10], [62, 105, 1], [147, 76, 85], [0, 0, 1], [0, 1]], ![[100, 72, 127], [70, 20, 117], [119, 71, 87], [31, 114, 132], [1, 12, 25], [57, 113, 92], [45, 127, 72], [22, 78, 24]], ![[0, 1], [37, 111, 146], [9, 128, 116], [23, 137, 9], [31, 34, 125], [39, 113, 125], [39, 24, 78], [100, 72, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 65], []]
 b := ![[], [28, 87, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [104, 1, 29, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56329795, -307533093, -430371744]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-373045, -2036643, -2850144]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [51, 124, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 129, 129], [52, 27, 28], [0, 1]]
 g := ![![[11, 93, 57], [68, 64], [66, 89, 130], [76, 2, 57], [14, 104, 14], [119, 1], []], ![[51, 17, 11, 131], [32, 120], [112, 0, 8, 23], [153, 120, 146, 5], [128, 1, 137, 102], [33, 101], [36, 156]], ![[82, 66, 143, 104], [61, 51], [99, 46, 104, 7], [23, 120, 10, 139], [119, 133, 23, 114], [139, 156], [137, 156]]]
 h' := ![![[67, 129, 129], [37, 54, 34], [88, 40, 149], [49, 68, 82], [71, 115, 34], [54, 108, 64], [0, 0, 1], [0, 1]], ![[52, 27, 28], [128, 24, 34], [70, 144, 77], [153, 55, 153], [10, 43, 53], [143, 52, 117], [141, 156, 27], [67, 129, 129]], ![[0, 1], [93, 79, 89], [8, 130, 88], [134, 34, 79], [2, 156, 70], [28, 154, 133], [113, 1, 129], [52, 27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 35], []]
 b := ![[], [21, 32, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [51, 124, 38, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-389988, 146952, -887364]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2484, 936, -5652]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, 496, 189]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-105, 496, 189]] 
 ![![163, 0, 0], ![0, 163, 0], ![90, 157, 1]] where
  M :=![![![-105, 496, 189], ![-1276, 6203, 2362], ![-4251, 20691, 7880]]]
  hmulB := by decide  
  f := ![![![-46, -13, 5]], ![![-86, 147, -42]], ![![-107, 132, -37]]]
  g := ![![![-105, -179, 189], ![-1312, -2237, 2362], ![-4377, -7463, 7880]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [93, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 162], [0, 1]]
 g := ![![[90, 156], [137, 26], [62], [90], [14], [145, 152], [1]], ![[0, 7], [122, 137], [62], [90], [14], [120, 11], [1]]]
 h' := ![![[106, 162], [136, 51], [160, 29], [104, 148], [145, 116], [44, 103], [70, 106], [0, 1]], ![[0, 1], [0, 112], [137, 134], [144, 15], [53, 47], [41, 60], [59, 57], [106, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [1, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [93, 57, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![401, 158, 1006]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-553, -968, 1006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46, 13, -5]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![46, 13, -5]] 
 ![![163, 0, 0], ![22, 1, 0], ![48, 0, 1]] where
  M :=![![![46, 13, -5], ![86, -147, 42], ![-201, 393, -113]]]
  hmulB := by decide  
  f := ![![![105, -496, -189]], ![![22, -105, -40]], ![![57, -273, -104]]]
  g := ![![![0, 13, -5], ![8, -147, 42], ![-21, 393, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-105, 496, 189]] ![![46, 13, -5]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-63, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-63, 1, 0]] 
 ![![167, 0, 0], ![104, 1, 0], ![78, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-63, 1, 0], ![2, -64, 4], ![-12, 36, -61]]]
  hmulB := by decide  
  f := ![![![9562, -376477, 23532], ![-5845, -982461, 0]], ![![6004, -234411, 14652], ![-3506, -611721, 0]], ![![4494, -175840, 10991], ![-2656, -458874, 0]]]
  g := ![![![1, 0, 0], ![-104, 167, 0], ![-78, 0, 167]], ![![-1, 1, 0], ![38, -64, 4], ![6, 36, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -90, 26]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![41, -90, 26]] 
 ![![167, 0, 0], ![114, 1, 0], ![120, 0, 1]] where
  M :=![![![41, -90, 26], ![-492, 1067, -308], ![1314, -2850, 823]]]
  hmulB := by decide  
  f := ![![![-341, 30, 22]], ![![-234, 23, 16]], ![![-246, 30, 19]]]
  g := ![![![43, -90, 26], ![-510, 1067, -308], ![1362, -2850, 823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-52, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-52, 1, 0]] 
 ![![167, 0, 0], ![115, 1, 0], ![63, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-52, 1, 0], ![2, -53, 4], ![-12, 36, -50]]]
  hmulB := by decide  
  f := ![![![15473, -471973, 35624], ![-7515, -1487302, 0]], ![![10653, -324965, 24528], ![-5176, -1024044, 0]], ![![5853, -178050, 13439], ![-2784, -561078, 0]]]
  g := ![![![1, 0, 0], ![-115, 167, 0], ![-63, 0, 167]], ![![-1, 1, 0], ![35, -53, 4], ![-6, 36, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-63, 1, 0]] ![![41, -90, 26]]
  ![![167, 0, 0], ![42, -71, 1]] where
 M := ![![![6847, -15030, 4342]], ![![-3075, 6737, -1946]]]
 hmul := by decide  
 g := ![![![![-1, -19, 25], ![167, 0, 0]]], ![![![-33, 65, -12], ![58, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![42, -71, 1]] ![![167, 0, 0], ![-52, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-8684, 167, 0]], ![![7014, -11857, 167], ![-2338, 3841, -334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-52, 1, 0]]], ![![![42, -71, 1]], ![![-14, 23, -2]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [39, 33, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 128, 72], [15, 44, 101], [0, 1]]
 g := ![![[38, 103, 88], [163, 137], [105, 122, 164], [16, 3, 4], [44, 148], [109, 90, 1], []], ![[99, 98, 61, 45], [68, 43], [27, 23, 30, 91], [89, 7, 135, 145], [81, 83], [168, 163, 140, 127], [73, 167]], ![[170, 149, 100, 12], [37, 1], [168, 146, 24, 28], [61, 53, 150, 107], [22, 60], [168, 22, 155, 39], [44, 167]]]
 h' := ![![[75, 128, 72], [6, 74, 112], [57, 34, 134], [68, 87, 67], [127, 46, 171], [74, 159, 54], [0, 0, 1], [0, 1]], ![[15, 44, 101], [102, 124, 49], [141, 26, 40], [170, 150, 43], [97, 37, 110], [83, 139, 157], [10, 71, 44], [75, 128, 72]], ![[0, 1], [31, 148, 12], [69, 113, 172], [86, 109, 63], [166, 90, 65], [141, 48, 135], [66, 102, 128], [15, 44, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 33], []]
 b := ![[], [131, 116, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [39, 33, 83, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17152431, 83373717, 121611042]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99147, 481929, 702954]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [33, 177, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 176, 30], [61, 2, 149], [0, 1]]
 g := ![![[43, 157, 66], [85, 100, 173], [10, 147], [26, 156], [33, 96, 19], [108, 74, 1], []], ![[172, 56, 26, 84], [55, 40, 21, 73], [103, 144], [16, 135], [137, 64, 120, 157], [72, 100, 69, 120], [11, 5]], ![[122, 36, 171, 47], [30, 17, 19, 76], [10, 82], [1, 129], [154, 70, 41, 142], [32, 37, 128, 88], [71, 5]]]
 h' := ![![[13, 176, 30], [59, 71, 31], [115, 59, 129], [83, 92, 46], [164, 18, 48], [16, 101, 52], [0, 0, 1], [0, 1]], ![[61, 2, 149], [159, 96, 44], [21, 133, 59], [52, 119, 167], [36, 78, 99], [12, 19, 91], [164, 137, 2], [13, 176, 30]], ![[0, 1], [31, 12, 104], [149, 166, 170], [168, 147, 145], [102, 83, 32], [147, 59, 36], [125, 42, 176], [61, 2, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 30], []]
 b := ![[], [84, 167, 178], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [33, 177, 105, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2327, 14499, 7160]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 81, 40]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4492, -51, 123]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-4492, -51, 123]] 
 ![![181, 0, 0], ![0, 181, 0], ![40, 4, 1]] where
  M :=![![![-4492, -51, 123], ![-1578, -13, 42], ![1719, 9, -43]]]
  hmulB := by decide  
  f := ![![![-1, 6, 3]], ![![-24, 101, 30]], ![![-1, 5, 2]]]
  g := ![![![-52, -3, 123], ![-18, -1, 42], ![19, 1, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [124, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 180], [0, 1]]
 g := ![![[59, 168], [45], [106, 143], [168], [86, 34], [154, 165], [1]], ![[142, 13], [45], [98, 38], [168], [36, 147], [103, 16], [1]]]
 h' := ![![[105, 180], [86, 63], [69, 100], [27, 163], [15, 63], [90, 45], [57, 105], [0, 1]], ![[0, 1], [4, 118], [71, 81], [128, 18], [114, 118], [109, 136], [41, 76], [105, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [126, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [124, 76, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1917, -116, 4496]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-983, -100, 4496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -6, -3]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![1, -6, -3]] 
 ![![181, 0, 0], ![163, 1, 0], ![96, 0, 1]] where
  M :=![![![1, -6, -3], ![24, -101, -30], ![45, -261, -122]]]
  hmulB := by decide  
  f := ![![![4492, 51, -123]], ![![4054, 46, -111]], ![![2373, 27, -65]]]
  g := ![![![7, -6, -3], ![107, -101, -30], ![300, -261, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-4492, -51, 123]] ![![1, -6, -3]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-84, 73, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-84, 73, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![107, 73, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-84, 73, 1], ![134, -121, 294], ![-867, 2643, 99]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -73, 191]], ![![-1, 0, 1], ![-164, -113, 294], ![-60, -24, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [168, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 190], [0, 1]]
 g := ![![[163, 51], [155, 90], [27, 78], [99, 180], [111, 162], [4, 75], [1]], ![[171, 140], [68, 101], [28, 113], [116, 11], [69, 29], [27, 116], [1]]]
 h' := ![![[120, 190], [127, 54], [48, 102], [176, 101], [70, 107], [92, 60], [23, 120], [0, 1]], ![[0, 1], [113, 137], [64, 89], [72, 90], [113, 84], [34, 131], [98, 71], [120, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [186, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [168, 71, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63, 375, 620]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-347, -235, 620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![88, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![88, 1, 0]] 
 ![![191, 0, 0], ![88, 1, 0], ![92, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![88, 1, 0], ![2, 87, 4], ![-12, 36, 90]]]
  hmulB := by decide  
  f := ![![![-2769, -162592, -7476], ![-2101, 356979, 0]], ![![-1282, -74902, -3444], ![-954, 164451, 0]], ![![-1372, -78317, -3601], ![-929, 171948, 0]]]
  g := ![![![1, 0, 0], ![-88, 191, 0], ![-92, 0, 191]], ![![0, 1, 0], ![-42, 87, 4], ![-60, 36, 90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-84, 73, 1]] ![![191, 0, 0], ![88, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![16808, 191, 0]], ![![-16044, 13943, 191], ![-7258, 6303, 382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![88, 1, 0]]], ![![![-84, 73, 1]], ![![-38, 33, 2]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![24, 24, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![24, 24, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![24, 24, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![24, 24, 1], ![36, 36, 98], ![-279, 879, 109]]]
  hmulB := by decide  
  f := ![![![-23, -24, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -24, 193]], ![![0, 0, 1], ![-12, -12, 98], ![-15, -9, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [65, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [160, 192], [0, 1]]
 g := ![![[146, 98], [6], [9], [18], [85], [7], [160, 1]], ![[0, 95], [6], [9], [18], [85], [7], [127, 192]]]
 h' := ![![[160, 192], [147, 22], [94, 149], [183, 190], [141, 37], [29, 49], [22, 59], [0, 1]], ![[0, 1], [0, 171], [2, 44], [89, 3], [78, 156], [149, 144], [5, 134], [160, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176]]
 b := ![[], [101, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [65, 33, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, 2886, 3546]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-439, -426, 3546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![95, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![95, 1, 0]] 
 ![![193, 0, 0], ![95, 1, 0], ![84, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![95, 1, 0], ![2, 94, 4], ![-12, 36, 97]]]
  hmulB := by decide  
  f := ![![![-10250, -673749, -28672], ![-8299, 1383424, 0]], ![![-5061, -331611, -14112], ![-4052, 680904, 0]], ![![-4470, -293238, -12479], ![-3594, 602112, 0]]]
  g := ![![![1, 0, 0], ![-95, 193, 0], ![-84, 0, 193]], ![![0, 1, 0], ![-48, 94, 4], ![-60, 36, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![24, 24, 1]] ![![193, 0, 0], ![95, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![18335, 193, 0]], ![![4632, 4632, 193], ![2316, 2316, 193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![95, 1, 0]]], ![![![24, 24, 1]], ![![12, 12, 1]]]]
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


lemma PB201I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB201I3 : PrimesBelowBoundCertificateInterval O 137 193 201 where
  m := 11
  g := ![2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB201I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
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
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
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
      exact NI167N2
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
  β := ![I139N1, I163N1, I167N0, I167N1, I167N2, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [], [], [], [I163N1], [I167N0, I167N1, I167N2], [], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
