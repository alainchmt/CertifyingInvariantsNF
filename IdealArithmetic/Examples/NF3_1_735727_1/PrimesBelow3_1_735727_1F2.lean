
import IdealArithmetic.Examples.NF3_1_735727_1.RI3_1_735727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [62, 22, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 13, 39], [76, 69, 44], [0, 1]]
 g := ![![[53, 35, 75], [76, 63, 7], [49, 69], [1, 49], [43, 27, 1], []], ![[37, 73, 69, 34], [65, 17, 44, 74], [12, 61], [76, 69], [41, 39, 3, 8], [0, 27]], ![[17, 47, 16, 37], [26, 44, 68, 75], [72, 77], [68, 59], [34, 37, 9, 49], [78, 27]]]
 h' := ![![[34, 13, 39], [19, 23, 65], [66, 22, 16], [38, 38, 22], [73, 36, 7], [0, 0, 1], [0, 1]], ![[76, 69, 44], [79, 77, 70], [54, 13, 53], [36, 46, 12], [10, 1, 61], [77, 40, 69], [34, 13, 39]], ![[0, 1], [36, 66, 31], [12, 48, 14], [34, 82, 49], [10, 46, 15], [27, 43, 13], [76, 69, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 19], []]
 b := ![[], [1, 70, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [62, 22, 56, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11537, -6889, -6059]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, -83, -73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [20, 12, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 7, 13], [62, 81, 76], [0, 1]]
 g := ![![[42, 12, 18], [11, 84], [10, 49], [11, 62, 2], [72, 23, 1], []], ![[61, 61, 77, 82], [49, 57], [70, 45], [58, 61, 73, 51], [76, 52, 26, 31], [64, 80]], ![[13, 2, 2, 77], [85, 79], [56, 8], [20, 5, 63, 38], [74, 8, 1, 75], [1, 80]]]
 h' := ![![[50, 7, 13], [67, 81, 14], [51, 84, 23], [47, 41, 7], [73, 11, 25], [0, 0, 1], [0, 1]], ![[62, 81, 76], [15, 88, 51], [4, 49, 18], [46, 3, 32], [62, 29, 32], [63, 23, 81], [50, 7, 13]], ![[0, 1], [63, 9, 24], [28, 45, 48], [76, 45, 50], [57, 49, 32], [86, 66, 7], [62, 81, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 23], []]
 b := ![[], [80, 21, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [20, 12, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182806, -241813, 45657]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2054, -2717, 513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373510667058676394320, 6110413083367800438, 6689623903922901515]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![373510667058676394320, 6110413083367800438, 6689623903922901515]] 
 ![![97, 0, 0], ![23, 1, 0], ![53, 0, 1]] where
  M :=![![![373510667058676394320, 6110413083367800438, 6689623903922901515], ![341170819100067977265, 5581352342916810995, 6110413083367800438], ![311631067251757822338, 5098099514838953175, 5581352342916810995]]]
  hmulB := by decide  
  f := ![![![-21673600625, 24697344315, -1061165581]], ![![-5697033598, 6234323975, 2995216]], ![![1142925020, -1067156013, -201559479]]]
  g := ![![![-1253390729553575217, 6110413083367800438, 6689623903922901515], ![-1144867816551671122, 5581352342916810995, 6110413083367800438], ![-1045741193444629726, 5098099514838953175, 5581352342916810995]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1225834698724, -20053928955, -21954856517]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-1225834698724, -20053928955, -21954856517]] 
 ![![97, 0, 0], ![34, 1, 0], ![8, 0, 1]] where
  M :=![![![-1225834698724, -20053928955, -21954856517], ![-1119697682367, -18317590289, -20053928955], ![-1022750376705, -16731589842, -18317590289]]]
  hmulB := by decide  
  f := ![![![571589, -782319, 171388]], ![![290462, -365501, 52009]], ![![-364181, 469173, -77151]]]
  g := ![![![-3797549094, -20053928955, -21954856517], ![-3468744133, -18317590289, -20053928955], ![-3168408245, -16731589842, -18317590289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46126527467, 754602644, 826132017]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![46126527467, 754602644, 826132017]] 
 ![![97, 0, 0], ![40, 1, 0], ![49, 0, 1]] where
  M :=![![![46126527467, 754602644, 826132017], ![42132732867, 689266532, 754602644], ![38484734844, 629587447, 689266532]]]
  hmulB := by decide  
  f := ![![![-102844, 79991, 35692]], ![![-23644, 11688, 15543]], ![![-9895, 13818, -3268]]]
  g := ![![![-252969558, 754602644, 826132017], ![-231066577, 689266532, 754602644], ![-211060032, 629587447, 689266532]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![373510667058676394320, 6110413083367800438, 6689623903922901515]] ![![-1225834698724, -20053928955, -21954856517]]
  ![![-471545966759576689818673857532501, -7714212467844708599686784692812, -8445448682561319429144651053565]] where
 M := ![![![-471545966759576689818673857532501, -7714212467844708599686784692812, -8445448682561319429144651053565]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-471545966759576689818673857532501, -7714212467844708599686784692812, -8445448682561319429144651053565]] ![![46126527467, 754602644, 826132017]]
  ![![97, 0, 0]] where
 M := ![![![-22400819694062646607885477219837499138675831, -366464130233958460789342538089669631699183, -401201550876530436437088336847591250966025]]]
 hmul := by decide  
 g := ![![![![-230936285505800480493664713606572156068823, -3777980724061427430817964310202779708239, -4136098462644643674609158111830837638825]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [61, 27, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 39, 6], [32, 61, 95], [0, 1]]
 g := ![![[83, 86, 58], [25, 5], [46, 89, 76], [99, 36], [76, 58], [1]], ![[96, 58, 92, 79], [91, 88], [32, 48, 63, 9], [15, 24], [70, 68], [68, 83, 34, 14]], ![[82, 9, 48, 56], [27, 81], [57, 28, 44, 56], [100, 33], [15, 36], [88, 10, 60, 87]]]
 h' := ![![[88, 39, 6], [70, 53, 19], [22, 12, 56], [57, 59, 51], [95, 27, 6], [40, 74, 19], [0, 1]], ![[32, 61, 95], [18, 36, 63], [69, 5, 54], [43, 92, 31], [94, 98, 23], [18, 47, 88], [88, 39, 6]], ![[0, 1], [94, 12, 19], [23, 84, 92], [83, 51, 19], [27, 77, 72], [29, 81, 95], [32, 61, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 66], []]
 b := ![[], [3, 60, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [61, 27, 82, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72316, -1414, 1414]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![716, -14, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [72, 77, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 23, 36], [11, 79, 67], [0, 1]]
 g := ![![[27, 71, 93], [20, 53, 98], [90, 70, 2], [65, 23], [34, 61], [1]], ![[26, 48, 10, 76], [67, 69, 2, 92], [25, 53, 56, 83], [30, 33], [17, 26], [73, 54, 51, 100]], ![[5, 85, 64, 85], [23, 81, 77, 20], [8, 96, 88, 24], [81, 63], [54, 63], [69, 20, 78, 3]]]
 h' := ![![[13, 23, 36], [2, 81, 14], [9, 95, 60], [23, 3, 38], [58, 61, 34], [31, 26, 24], [0, 1]], ![[11, 79, 67], [51, 40, 5], [90, 96, 23], [59, 6, 20], [46, 51, 41], [31, 92, 51], [13, 23, 36]], ![[0, 1], [80, 85, 84], [27, 15, 20], [27, 94, 45], [20, 94, 28], [71, 88, 28], [11, 79, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 8], []]
 b := ![[], [44, 98, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [72, 77, 79, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170774, 297567, -121025]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1658, 2889, -1175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, -1, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![56, -1, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![56, 106, 1]] where
  M :=![![![56, -1, 1], ![51, 1, -1], ![-51, 106, 1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0]], ![![0, 1, 1]], ![![1, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 1, -1], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [38, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 106], [0, 1]]
 g := ![![[14, 19], [56, 92], [105], [71, 102], [92], [3, 1]], ![[71, 88], [11, 15], [105], [56, 5], [92], [6, 106]]]
 h' := ![![[3, 106], [12, 74], [70, 29], [84, 76], [84, 40], [100, 78], [0, 1]], ![[0, 1], [20, 33], [50, 78], [98, 31], [97, 67], [13, 29], [3, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [98, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [38, 104, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![140, -163, -158]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 155, -158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![107, 0, 0], ![1, 1, 0], ![106, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![51, -55, 1]]]
  hmulB := by decide  
  f := ![![![56, -1, 1]], ![![1, 0, 0]], ![![55, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, -55, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![56, -1, 1]] ![![1, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2530597, 3386845, -674797]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2530597, 3386845, -674797]] 
 ![![109, 0, 0], ![0, 109, 0], ![62, 94, 1]] where
  M :=![![![-2530597, 3386845, -674797], ![-34414647, 34583238, 3386845], ![172729095, -220691122, 34583238]]]
  hmulB := by decide  
  f := ![![![-17829788749126, -291684773836, -319333800979]], ![![-16286023849929, -266429695281, -291684773836]], ![![-24323018970686, -397910170855, -435628386207]]]
  g := ![![![360613, 613007, -674797], ![-2242193, -2603488, 3386845], ![-18086529, -31848766, 34583238]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [29, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 108], [0, 1]]
 g := ![![[43, 94], [61], [78, 26], [74, 35], [87], [61, 1]], ![[0, 15], [61], [29, 83], [29, 74], [87], [13, 108]]]
 h' := ![![[61, 108], [50, 51], [27, 37], [34, 74], [64, 12], [84, 95], [0, 1]], ![[0, 1], [0, 58], [104, 72], [79, 35], [33, 97], [102, 14], [61, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [103, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [29, 48, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2016, -1089, 356]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-184, -317, 356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17829788749126, -291684773836, -319333800979]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-17829788749126, -291684773836, -319333800979]] 
 ![![109, 0, 0], ![15, 1, 0], ![102, 0, 1]] where
  M :=![![![-17829788749126, -291684773836, -319333800979], ![-16286023849929, -266429695281, -291684773836], ![-14875923465636, -243361288949, -266429695281]]]
  hmulB := by decide  
  f := ![![![-2530597, 3386845, -674797]], ![![-663978, 783357, -61790]], ![![-783411, 1144652, -314184]]]
  g := ![![![175390188608, -291684773836, -319333800979], ![160204298262, -266429695281, -291684773836], ![146333254929, -243361288949, -266429695281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2530597, 3386845, -674797]] ![![-17829788749126, -291684773836, -319333800979]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [69, 33, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 41, 89], [41, 71, 24], [0, 1]]
 g := ![![[58, 16, 32], [34, 85], [107, 28], [7, 15], [101, 67, 36], [1]], ![[66, 72, 100, 110], [6, 57], [79, 53], [20, 111], [25, 70, 42, 19], [112, 39, 112, 75]], ![[15, 24, 4, 76], [74, 60], [39, 56], [112, 41], [92, 96, 6, 75], [96, 61, 81, 38]]]
 h' := ![![[66, 41, 89], [11, 98, 91], [60, 92, 57], [95, 56, 64], [37, 82, 44], [44, 80, 107], [0, 1]], ![[41, 71, 24], [30, 75, 41], [61, 53, 31], [75, 73, 36], [41, 61, 26], [93, 109, 27], [66, 41, 89]], ![[0, 1], [64, 53, 94], [57, 81, 25], [6, 97, 13], [29, 83, 43], [34, 37, 92], [41, 71, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 52], []]
 b := ![[], [2, 5, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [69, 33, 6, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27346, 31188, -1243]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-242, 276, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2215583, 3738690, -1437559]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-2215583, 3738690, -1437559]] 
 ![![127, 0, 0], ![0, 127, 0], ![7, 98, 1]] where
  M :=![![![-2215583, 3738690, -1437559], ![-73315509, 76850162, 3738690], ![190673190, -278943459, 76850162]]]
  hmulB := by decide  
  f := ![![![54715200946102, 895108250463, 979956259454]], ![![49977769232154, 817606676132, 895108250463]], ![![41940774111397, 686126200558, 751164638092]]]
  g := ![![![61790, 1138736, -1437559], ![-783357, -2279854, 3738690], ![-2734472, -61498105, 76850162]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [101, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 126], [0, 1]]
 g := ![![[11, 15], [118, 73], [3, 88], [12, 104], [96, 13], [32, 1]], ![[110, 112], [41, 54], [25, 39], [38, 23], [4, 114], [64, 126]]]
 h' := ![![[32, 126], [20, 74], [78, 33], [58, 71], [83, 55], [70, 34], [0, 1]], ![[0, 1], [102, 53], [118, 94], [44, 56], [65, 72], [15, 93], [32, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [91, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [101, 95, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305, 79, -29]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 23, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54715200946102, -895108250463, -979956259454]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-54715200946102, -895108250463, -979956259454]] 
 ![![127, 0, 0], ![29, 1, 0], ![48, 0, 1]] where
  M :=![![![-54715200946102, -895108250463, -979956259454], ![-49977769232154, -817606676132, -895108250463], ![-45650520773613, -746815456689, -817606676132]]]
  hmulB := by decide  
  f := ![![![2215583, -3738690, 1437559]], ![![1083208, -1458836, 298823]], ![![-663978, 783357, -61790]]]
  g := ![![![143943612371, -895108250463, -979956259454], ![131480475574, -817606676132, -895108250463], ![120096440352, -746815456689, -817606676132]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-2215583, 3738690, -1437559]] ![![-54715200946102, -895108250463, -979956259454]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [26, 11, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 24, 27], [125, 106, 104], [0, 1]]
 g := ![![[8, 23, 129], [14, 118, 12], [42, 7], [119, 9], [113, 33], [48, 1], []], ![[4, 77, 104, 39], [67, 22, 57, 46], [20, 11], [40, 5], [107, 55], [32, 101], [1, 74]], ![[8, 56, 6, 37], [37, 11, 124, 73], [80, 114], [95, 21], [70, 117], [42, 52], [55, 74]]]
 h' := ![![[54, 24, 27], [29, 47, 103], [115, 78, 76], [40, 104, 20], [120, 74, 128], [62, 101, 66], [0, 0, 1], [0, 1]], ![[125, 106, 104], [116, 24, 4], [88, 59, 75], [52, 47, 81], [31, 67, 108], [18, 67, 29], [8, 2, 106], [54, 24, 27]], ![[0, 1], [3, 60, 24], [75, 125, 111], [94, 111, 30], [59, 121, 26], [69, 94, 36], [47, 129, 24], [125, 106, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 74], []]
 b := ![[], [113, 97, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [26, 11, 83, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125236, -111874, -24890]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![956, -854, -190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [101, 58, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 58, 66], [70, 78, 71], [0, 1]]
 g := ![![[76, 50, 32], [62, 88], [101, 61], [71, 126, 109], [109, 135], [66, 1], []], ![[77, 111, 47, 91], [79, 50], [52, 15], [6, 57, 4, 79], [4, 65], [64, 56], [54, 109]], ![[75, 56, 100, 80], [51, 9], [27, 19], [6, 54, 23, 89], [37, 39], [122, 76], [49, 109]]]
 h' := ![![[133, 58, 66], [101, 132, 124], [91, 119, 15], [90, 72, 46], [105, 71, 66], [47, 44, 51], [0, 0, 1], [0, 1]], ![[70, 78, 71], [123, 104, 26], [108, 40, 119], [90, 84, 120], [127, 10, 107], [95, 100, 32], [42, 54, 78], [133, 58, 66]], ![[0, 1], [114, 38, 124], [14, 115, 3], [136, 118, 108], [60, 56, 101], [80, 130, 54], [88, 83, 58], [70, 78, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 15], []]
 b := ![[], [69, 65, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [101, 58, 71, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14796, 822, -822]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108, 6, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB243I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB243I2 : PrimesBelowBoundCertificateInterval O 79 137 243 where
  m := 11
  g := ![1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB243I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I97N0, I97N1, I97N2, I107N1, I109N1, I127N1]
  Il := ![[], [], [I97N0, I97N1, I97N2], [], [], [I107N1], [I109N1], [], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
