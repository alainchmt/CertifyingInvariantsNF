
import IdealArithmetic.Examples.NF3_1_592328_1.RI3_1_592328_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-8, 53, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-8, 53, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![131, 53, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-8, 53, 1], ![-34, 121, 317], ![-10121, 1183, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-131, -53, 139]], ![![-1, 0, 1], ![-299, -120, 317], ![-37, 23, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [105, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 138], [0, 1]]
 g := ![![[106, 127], [55, 96], [13], [91, 1], [5], [100], [1]], ![[87, 12], [68, 43], [13], [81, 138], [5], [100], [1]]]
 h' := ![![[129, 138], [63, 108], [70, 42], [36, 41], [19, 138], [108, 127], [34, 129], [0, 1]], ![[0, 1], [95, 31], [67, 97], [43, 98], [29, 1], [89, 12], [134, 10], [129, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [126, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [105, 10, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2244, -1188, 1462]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1394, -566, 1462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-39, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-39, 1, 0]] 
 ![![139, 0, 0], ![100, 1, 0], ![38, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-39, 1, 0], ![3, -37, 6], ![-193, 23, -40]]]
  hmulB := by decide  
  f := ![![![343, -4218, 684], ![0, -15846, 0]], ![![247, -3034, 492], ![1, -11398, 0]], ![![89, -1153, 187], ![-17, -4332, 0]]]
  g := ![![![1, 0, 0], ![-100, 139, 0], ![-38, 0, 139]], ![![-1, 1, 0], ![25, -37, 6], ![-7, 23, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-8, 53, 1]] ![![139, 0, 0], ![-39, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-5421, 139, 0]], ![![-1112, 7367, 139], ![278, -1946, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-39, 1, 0]]], ![![![-8, 53, 1]], ![![2, -14, 2]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [143, 29, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 0, 74], [91, 148, 75], [0, 1]]
 g := ![![[97, 126, 30], [78, 95], [148, 7, 68], [126, 39], [86, 143, 24], [77, 1], []], ![[83, 68, 92, 92], [41, 45], [50, 35, 68, 65], [87, 49], [61, 10, 118, 71], [73, 1], [131, 112]], ![[126, 112, 77, 141], [59, 67], [37, 53, 6, 128], [71, 33], [137, 138, 5, 8], [], [130, 112]]]
 h' := ![![[135, 0, 74], [57, 95, 103], [143, 87, 86], [4, 32, 51], [69, 79, 28], [15, 8, 89], [0, 0, 1], [0, 1]], ![[91, 148, 75], [43, 57, 73], [86, 23, 94], [21, 102, 82], [86, 56, 7], [136, 29, 56], [88, 2, 148], [135, 0, 74]], ![[0, 1], [7, 146, 122], [139, 39, 118], [147, 15, 16], [67, 14, 114], [39, 112, 4], [121, 147], [91, 148, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 15], []]
 b := ![[], [11, 12, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [143, 29, 72, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7682291, -1878294, 927078]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51559, -12606, 6222]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [65, 24, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 129, 145], [63, 21, 6], [0, 1]]
 g := ![![[149, 90, 32], [52, 116, 125], [90, 102, 10], [92, 21], [22, 25, 50], [42, 1], []], ![[38, 126, 114, 84], [86, 56, 26, 91], [94, 45, 101, 137], [29, 2], [21, 78, 57, 136], [19, 139], [115, 36]], ![[118, 7, 26, 13], [128, 58, 5, 147], [102, 119, 106, 150], [11, 58], [111, 29, 104, 35], [117, 31], [103, 36]]]
 h' := ![![[130, 129, 145], [93, 132, 33], [39, 0, 27], [118, 90, 114], [80, 105, 25], [139, 135, 79], [0, 0, 1], [0, 1]], ![[63, 21, 6], [4, 20, 52], [79, 45, 114], [125, 22, 42], [54, 47, 46], [16, 81, 94], [63, 52, 21], [130, 129, 145]], ![[0, 1], [142, 150, 66], [125, 106, 10], [44, 39, 146], [2, 150, 80], [9, 86, 129], [143, 99, 129], [63, 21, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 20], []]
 b := ![[], [23, 96, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [65, 24, 109, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37078891070, 8839048797, -3876598840]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245555570, 58536747, -25672840]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [153, 28, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 93, 5], [5, 63, 152], [0, 1]]
 g := ![![[40, 149, 145], [27, 40], [132, 145, 82], [40, 75, 56], [156, 23, 40], [8, 1], []], ![[152, 103, 5, 32], [97, 118], [85, 72, 81, 8], [67, 39, 124, 134], [45, 62, 154, 98], [111, 44], [31, 25]], ![[102, 36, 83, 50], [28, 122], [100, 28, 69, 104], [50, 29, 39, 7], [63, 106, 58, 139], [79, 14], [41, 25]]]
 h' := ![![[3, 93, 5], [60, 26, 50], [57, 33, 36], [3, 138, 125], [153, 45, 29], [32, 94, 36], [0, 0, 1], [0, 1]], ![[5, 63, 152], [37, 82, 140], [77, 62, 78], [86, 86, 87], [63, 136, 11], [78, 83, 69], [133, 104, 63], [3, 93, 5]], ![[0, 1], [63, 49, 124], [118, 62, 43], [140, 90, 102], [50, 133, 117], [84, 137, 52], [32, 53, 93], [5, 63, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 140], []]
 b := ![[], [11, 141, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [153, 28, 149, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11817547, 2116360, -551384]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75271, 13480, -3512]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [121, 30, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 152, 29], [28, 10, 134], [0, 1]]
 g := ![![[95, 136, 1], [134, 0, 160], [83, 1], [108, 39], [83, 33], [122, 106, 1], []], ![[14, 73, 67, 72], [2, 26, 36, 86], [118, 47], [44, 64], [78, 140], [29, 122, 85, 129], [162, 26]], ![[44, 78, 111, 6], [133, 9, 97, 156], [146, 53], [108, 22], [119, 87], [52, 26, 78, 77], [57, 26]]]
 h' := ![![[78, 152, 29], [86, 148, 162], [147, 7, 46], [128, 93, 162], [51, 31, 56], [71, 140, 14], [0, 0, 1], [0, 1]], ![[28, 10, 134], [46, 107, 44], [58, 146, 11], [36, 60, 79], [151, 136, 155], [61, 87, 125], [11, 58, 10], [78, 152, 29]], ![[0, 1], [74, 71, 120], [157, 10, 106], [43, 10, 85], [76, 159, 115], [72, 99, 24], [81, 105, 152], [28, 10, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 51], []]
 b := ![[], [75, 95, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [121, 30, 57, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2339376, 503181, -167564]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14352, 3087, -1028]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![39, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![39, 1, 0]] 
 ![![167, 0, 0], ![39, 1, 0], ![68, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![39, 1, 0], ![3, 41, 6], ![-193, 23, 38]]]
  hmulB := by decide  
  f := ![![![-6281, -92238, -13500], ![-2004, 375750, 0]], ![![-1497, -21523, -3150], ![-333, 87675, 0]], ![![-2558, -37558, -5497], ![-814, 153000, 0]]]
  g := ![![![1, 0, 0], ![-39, 167, 0], ![-68, 0, 167]], ![![0, 1, 0], ![-12, 41, 6], ![-22, 23, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![53, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![53, 1, 0]] 
 ![![167, 0, 0], ![53, 1, 0], ![127, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![53, 1, 0], ![3, 55, 6], ![-193, 23, 52]]]
  hmulB := by decide  
  f := ![![![42113, 880768, 96096], ![18704, -2674672, 0]], ![![13338, 279474, 30492], ![6013, -848694, 0]], ![![31994, 669805, 73079], ![14325, -2034032, 0]]]
  g := ![![![1, 0, 0], ![-53, 167, 0], ![-127, 0, 167]], ![![0, 1, 0], ![-22, 55, 6], ![-48, 23, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![74, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![74, 1, 0]] 
 ![![167, 0, 0], ![74, 1, 0], ![93, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![74, 1, 0], ![3, 76, 6], ![-193, 23, 73]]]
  hmulB := by decide  
  f := ![![![-25690, -834458, -65886], ![-16366, 1833827, 0]], ![![-11413, -369697, -29190], ![-7180, 812455, 0]], ![![-14368, -464699, -36691], ![-8975, 1021233, 0]]]
  g := ![![![1, 0, 0], ![-74, 167, 0], ![-93, 0, 167]], ![![0, 1, 0], ![-37, 76, 6], ![-52, 23, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![39, 1, 0]] ![![167, 0, 0], ![53, 1, 0]]
  ![![167, 0, 0], ![11, -40, 1]] where
 M := ![![![27889, 0, 0], ![8851, 167, 0]], ![![6513, 167, 0], ![2070, 94, 6]]]
 hmul := by decide  
 g := ![![![![156, 40, -1], ![167, 0, 0]], ![![42, 41, -1], ![167, 0, 0]]], ![![![28, 41, -1], ![167, 0, 0]], ![![12, 2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![11, -40, 1]] ![![167, 0, 0], ![74, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![12358, 167, 0]], ![![1837, -6680, 167], ![501, -3006, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![74, 1, 0]]], ![![![11, -40, 1]], ![![3, -18, -1]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [58, 153, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 40, 13], [80, 132, 160], [0, 1]]
 g := ![![[46, 156, 60], [93, 157], [167, 15, 95], [54, 137, 37], [101, 40], [69, 7, 1], []], ![[151, 57, 136, 21], [85, 54], [165, 6, 61, 124], [27, 83, 16, 73], [60, 78], [144, 162, 123, 55], [147, 169]], ![[163, 71, 86, 169], [149, 36], [112, 21, 1, 85], [95, 150, 146, 167], [159, 47], [64, 36, 60, 133], [0, 169]]]
 h' := ![![[100, 40, 13], [146, 124, 38], [2, 26, 147], [155, 172, 152], [34, 49, 27], [150, 109, 46], [0, 0, 1], [0, 1]], ![[80, 132, 160], [50, 110, 54], [89, 170, 20], [68, 109, 156], [98, 162, 49], [139, 137, 50], [90, 100, 132], [100, 40, 13]], ![[0, 1], [167, 112, 81], [32, 150, 6], [96, 65, 38], [121, 135, 97], [1, 100, 77], [172, 73, 40], [80, 132, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141, 127], []]
 b := ![[], [3, 7, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [58, 153, 166, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284194020, -106774216, 57331854]
  a := ![24, 22, 47]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1642740, -617192, 331398]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![37, 14, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![37, 14, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![37, 14, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![37, 14, 1], ![-151, 88, 83], ![-2594, 286, 46]]]
  hmulB := by decide  
  f := ![![![-36, -14, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -14, 179]], ![![0, 0, 1], ![-18, -6, 83], ![-24, -2, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [68, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [175, 178], [0, 1]]
 g := ![![[158, 129], [44, 100], [56], [144], [175, 25], [122, 16], [1]], ![[0, 50], [2, 79], [56], [144], [75, 154], [58, 163], [1]]]
 h' := ![![[175, 178], [51, 147], [58, 10], [110, 45], [93, 12], [117, 5], [111, 175], [0, 1]], ![[0, 1], [0, 32], [18, 169], [109, 134], [45, 167], [97, 174], [127, 4], [175, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [68, 4, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1036, -324, 207]
  a := ![-2, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -18, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-83, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-83, 1, 0]] 
 ![![179, 0, 0], ![96, 1, 0], ![133, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-83, 1, 0], ![3, -81, 6], ![-193, 23, -84]]]
  hmulB := by decide  
  f := ![![![24740, -871793, 64584], ![-16289, -1926756, 0]], ![![13333, -467484, 34632], ![-8591, -1033188, 0]], ![![18398, -647757, 47987], ![-12069, -1431612, 0]]]
  g := ![![![1, 0, 0], ![-96, 179, 0], ![-133, 0, 179]], ![![-1, 1, 0], ![39, -81, 6], ![49, 23, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![37, 14, 1]] ![![179, 0, 0], ![-83, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-14857, 179, 0]], ![![6623, 2506, 179], ![-3222, -1074, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-83, 1, 0]]], ![![![37, 14, 1]], ![![-18, -6, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-16, -18, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-16, -18, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![165, 163, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-16, -18, 1], ![-247, -29, -109], ![3582, -450, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-165, -163, 181]], ![![-1, -1, 1], ![98, 98, -109], ![-3, -25, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [173, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 180], [0, 1]]
 g := ![![[62, 16], [20], [14, 176], [39], [84, 119], [43, 37], [1]], ![[34, 165], [20], [68, 5], [39], [102, 62], [114, 144], [1]]]
 h' := ![![[134, 180], [34, 177], [112, 127], [120, 30], [129, 43], [163, 149], [8, 134], [0, 1]], ![[0, 1], [41, 4], [116, 54], [158, 151], [99, 138], [38, 32], [45, 47], [134, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [99, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [173, 47, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5226, -3481, 5372]
  a := ![7, 5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4926, -4857, 5372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-72, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-72, 1, 0]] 
 ![![181, 0, 0], ![109, 1, 0], ![156, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-72, 1, 0], ![3, -70, 6], ![-193, 23, -73]]]
  hmulB := by decide  
  f := ![![![3259, -91131, 7812], ![-1629, -235662, 0]], ![![1993, -54875, 4704], ![-904, -141904, 0]], ![![2820, -78544, 6733], ![-1376, -203112, 0]]]
  g := ![![![1, 0, 0], ![-109, 181, 0], ![-156, 0, 181]], ![![-1, 1, 0], ![37, -70, 6], ![48, 23, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-16, -18, 1]] ![![181, 0, 0], ![-72, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-13032, 181, 0]], ![![-2896, -3258, 181], ![905, 1267, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-72, 1, 0]]], ![![![-16, -18, 1]], ![![5, 7, -1]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [3, 117, 152, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 35, 4], [96, 155, 187], [0, 1]]
 g := ![![[19, 160, 8], [61, 7, 27], [169, 155, 13], [168, 68, 150], [179, 158, 130], [67, 39, 1], []], ![[17, 90, 93, 85], [151, 132, 189, 59], [135, 128, 63, 17], [147, 4, 56, 160], [30, 20, 127, 25], [56, 103, 67, 27], [140, 16]], ![[16, 173, 187, 35], [183, 122, 116, 88], [6, 117, 171, 139], [21, 165, 108, 106], [99, 52, 189, 123], [79, 14, 84, 66], [148, 16]]]
 h' := ![![[134, 35, 4], [8, 63, 114], [66, 185, 119], [69, 154, 108], [36, 75, 155], [181, 66, 148], [0, 0, 1], [0, 1]], ![[96, 155, 187], [144, 169, 159], [135, 141, 85], [9, 184, 166], [113, 31, 68], [68, 156, 93], [155, 19, 155], [134, 35, 4]], ![[0, 1], [67, 150, 109], [116, 56, 178], [162, 44, 108], [100, 85, 159], [52, 160, 141], [177, 172, 35], [96, 155, 187]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141, 87], []]
 b := ![[], [185, 19, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [3, 117, 152, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17182742, 3307165, -951180]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-89962, 17315, -4980]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![57, 7, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![57, 7, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![57, 7, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![57, 7, 1], ![-172, 94, 41], ![-1243, 125, 73]]]
  hmulB := by decide  
  f := ![![![-56, -7, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -7, 193]], ![![0, 0, 1], ![-13, -1, 41], ![-28, -2, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [138, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 192], [0, 1]]
 g := ![![[46, 7], [121], [84], [16], [189], [134], [21, 1]], ![[0, 186], [121], [84], [16], [189], [134], [42, 192]]]
 h' := ![![[21, 192], [81, 134], [145, 11], [100, 108], [68, 4], [45, 31], [190, 110], [0, 1]], ![[0, 1], [0, 59], [183, 182], [52, 85], [152, 189], [117, 162], [184, 83], [21, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [125, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [138, 172, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2470, -432, -172]
  a := ![0, -4, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 4, -172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-41, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-41, 1, 0]] 
 ![![193, 0, 0], ![152, 1, 0], ![120, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-41, 1, 0], ![3, -39, 6], ![-193, 23, -42]]]
  hmulB := by decide  
  f := ![![![20851, -287010, 44160], ![-5790, -1420480, 0]], ![![16405, -226020, 34776], ![-4631, -1118628, 0]], ![![12972, -178452, 27457], ![-3564, -883200, 0]]]
  g := ![![![1, 0, 0], ![-152, 193, 0], ![-120, 0, 193]], ![![-1, 1, 0], ![27, -39, 6], ![7, 23, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![57, 7, 1]] ![![193, 0, 0], ![-41, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-7913, 193, 0]], ![![11001, 1351, 193], ![-2509, -193, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-41, 1, 0]]], ![![![57, 7, 1]], ![![-13, -1, 0]]]]
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


lemma PB218I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB218I3 : PrimesBelowBoundCertificateInterval O 137 193 218 where
  m := 11
  g := ![2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB218I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
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
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I167N0, I167N1, I167N2, I179N1, I181N1, I193N1]
  Il := ![[I139N1], [], [], [], [], [I167N0, I167N1, I167N2], [], [I179N1], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
