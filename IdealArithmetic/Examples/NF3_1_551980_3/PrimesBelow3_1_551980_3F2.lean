
import IdealArithmetic.Examples.NF3_1_551980_3.RI3_1_551980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1664589682429, -490676116961, 67420089667]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![1664589682429, -490676116961, 67420089667]] 
 ![![83, 0, 0], ![0, 83, 0], ![7, 48, 1]] where
  M :=![![![1664589682429, -490676116961, 67420089667], ![-10450113898385, 3080411565436, -423256027294], ![65604684230570, -19338490471559, 2657155538142]]]
  hmulB := by decide  
  f := ![![![2314802, -56077, -67666]], ![![10488230, 893816, -123743]], ![![6491793, 607232, -67991]]]
  g := ![![![14369265720, -44901691819, 67420089667], ![-90208695269, 281887962356, -423256027294], ![566320427272, -1769662124125, 2657155538142]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [52, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 82], [0, 1]]
 g := ![![[8, 16], [59, 40], [21], [78], [20, 1], [1]], ![[75, 67], [19, 43], [21], [78], [19, 82], [1]]]
 h' := ![![[82, 82], [3, 4], [20, 17], [38, 42], [39, 59], [31, 82], [0, 1]], ![[0, 1], [82, 79], [3, 66], [79, 41], [63, 24], [32, 1], [82, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [81, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [52, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-413, -93, 24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -15, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2314802, -56077, -67666]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![2314802, -56077, -67666]] 
 ![![83, 0, 0], ![34, 1, 0], ![6, 0, 1]] where
  M :=![![![2314802, -56077, -67666], ![10488230, 893816, -123743], ![19180165, 7889627, 770073]]]
  hmulB := by decide  
  f := ![![![1664589682429, -490676116961, 67420089667]], ![![555975124147, -163886462786, 22518397848]], ![![910749666568, -268464423775, 36887663568]]]
  g := ![![![55752, -56077, -67666], ![-230832, 893816, -123743], ![-3056477, 7889627, 770073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![1664589682429, -490676116961, 67420089667]] ![![2314802, -56077, -67666]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [40, 22, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 54, 36], [81, 34, 53], [0, 1]]
 g := ![![[59, 56, 88], [87, 39], [44, 73], [76, 53, 1], [46, 35, 1], []], ![[12, 27, 4, 34], [44, 53], [31, 88], [87, 46, 77, 55], [68, 79, 23, 53], [31, 50]], ![[50, 13, 3, 36], [75, 79], [29, 80], [85, 42, 86, 32], [10, 22, 2, 44], [14, 50]]]
 h' := ![![[43, 54, 36], [11, 55, 34], [38, 64, 22], [75, 75, 42], [29, 80, 88], [0, 0, 1], [0, 1]], ![[81, 34, 53], [31, 80, 21], [79, 73, 26], [42, 35, 34], [12, 44, 87], [75, 4, 34], [43, 54, 36]], ![[0, 1], [62, 43, 34], [6, 41, 41], [3, 68, 13], [63, 54, 3], [38, 85, 54], [81, 34, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 33], []]
 b := ![[], [21, 69, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [40, 22, 54, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![672306, -251336, 21538]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7554, -2824, 242]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [84, 5, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 45, 59], [56, 51, 38], [0, 1]]
 g := ![![[15, 75, 4], [3, 85], [70, 12], [76, 72], [32, 48], [1]], ![[5, 22, 11, 68], [70, 85], [21, 35], [64, 88], [88, 49], [74, 42, 31, 30]], ![[33, 78, 65, 34], [], [18, 62], [53, 33], [52, 75], [84, 50, 2, 67]]]
 h' := ![![[1, 45, 59], [42, 14, 95], [87, 15, 52], [27, 38, 20], [3, 43, 84], [13, 92, 57], [0, 1]], ![[56, 51, 38], [31, 36, 45], [73, 17, 45], [24, 84, 61], [29, 14, 31], [90, 20, 90], [1, 45, 59]], ![[0, 1], [96, 47, 54], [22, 65], [46, 72, 16], [91, 40, 79], [71, 82, 47], [56, 51, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 41], []]
 b := ![[], [94, 92, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [84, 5, 40, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149380, 41031, -10961]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1540, 423, -113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2574966124, -319578223, 14429354]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-2574966124, -319578223, 14429354]] 
 ![![101, 0, 0], ![0, 101, 0], ![56, 81, 1]] where
  M :=![![![-2574966124, -319578223, 14429354], ![-2236549870, -2271949690, -305148869], ![47298074695, -8644676119, -2577098559]]]
  hmulB := by decide  
  f := ![![![-31852724075597399, 9389323464529483, -1290115838145347]], ![![199967954912528785, -58945156676649686, 8099207626384136]], ![![130279946708830061, -38403012492360177, 5276667146046634]]]
  g := ![![![-33495148, -14736197, 14429354], ![147047394, 222228799, -305148869], ![1897184099, 1981191160, -2577098559]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [39, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 100], [0, 1]]
 g := ![![[19, 97], [58], [59, 4], [31], [36], [67, 1]], ![[54, 4], [58], [24, 97], [31], [36], [33, 100]]]
 h' := ![![[67, 100], [40, 20], [22, 82], [27, 99], [78, 43], [13, 6], [0, 1]], ![[0, 1], [67, 81], [62, 19], [95, 2], [30, 58], [11, 95], [67, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [64, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [39, 34, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-391, -1296, 85]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -81, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29367754, 1198650, -554217]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![29367754, 1198650, -554217]] 
 ![![101, 0, 0], ![19, 1, 0], ![43, 0, 1]] where
  M :=![![![29367754, 1198650, -554217], ![85903635, 17729197, 644433], ![-99887115, 99436728, 18373630]]]
  hmulB := by decide  
  f := ![![![-261669396939886, 77133076681476, -10598271989199]], ![![-32960261223089, 9715795527079, -1334973892104]], ![![-213511671244733, 62937478754130, -8647762371845]]]
  g := ![![![301235, 1198650, -554217], ![-2759027, 17729197, 644433], ![-27517337, 99436728, 18373630]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-2574966124, -319578223, 14429354]] ![![29367754, 1198650, -554217]]
  ![![101, 0, 0]] where
 M := ![![![-104515209252879811, -7317540668095819, 1486262858897369]]]
 hmul := by decide  
 g := ![![![![-1034804052008711, -72450897703919, 14715473850469]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [87, 41, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 65, 49], [13, 37, 54], [0, 1]]
 g := ![![[93, 39, 8], [50, 9, 14], [7, 6, 2], [59, 1], [0, 82], [1]], ![[81, 62, 37, 59], [42, 43, 37, 61], [38, 76, 62, 23], [13, 30], [75, 97], [25, 26, 78, 23]], ![[44, 81, 74, 53], [34, 97, 77, 74], [84, 95, 70, 22], [84, 2], [88, 8], [94, 81, 32, 80]]]
 h' := ![![[46, 65, 49], [79, 29, 76], [9, 83, 23], [45, 69, 38], [50, 0, 1], [16, 62, 59], [0, 1]], ![[13, 37, 54], [56, 100, 10], [100, 26, 77], [17, 39, 49], [85, 89, 37], [92, 11, 71], [46, 65, 49]], ![[0, 1], [62, 77, 17], [77, 97, 3], [24, 98, 16], [15, 14, 65], [96, 30, 76], [13, 37, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 68], []]
 b := ![[], [7, 25, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [87, 41, 44, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26883, 1133, 1133]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-261, 11, 11]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [81, 21, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 8, 42], [0, 98, 65], [0, 1]]
 g := ![![[56, 4, 9], [23, 84, 69], [58, 14], [46, 4, 23], [8, 52], [1]], ![[2, 99, 44, 79], [4, 19, 53, 44], [1, 19], [43, 82, 36, 19], [79, 105], [55, 1, 42, 44]], ![[0, 14, 67, 72], [19, 39, 95, 88], [63, 56], [25, 46, 37, 96], [38, 14], [57, 104, 16, 63]]]
 h' := ![![[65, 8, 42], [63, 28, 3], [50, 34, 47], [19, 29, 96], [28, 92, 39], [26, 86, 65], [0, 1]], ![[0, 98, 65], [91, 43, 79], [8, 40, 42], [93, 4, 33], [46, 95, 89], [102, 12, 31], [65, 8, 42]], ![[0, 1], [66, 36, 25], [97, 33, 18], [8, 74, 85], [67, 27, 86], [91, 9, 11], [0, 98, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 28], []]
 b := ![[], [43, 71, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [81, 21, 42, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1679900, 42586, 43549]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15700, 398, 407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [80, 76, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 97, 102], [35, 11, 7], [0, 1]]
 g := ![![[80, 24, 9], [79, 46], [46, 17, 71], [102, 56, 46], [59, 105], [1]], ![[98, 72, 40, 73], [15, 78], [97, 31, 101, 3], [87, 40, 20, 35], [66, 102], [53, 76, 14, 93]], ![[83, 101, 31, 94], [38, 35], [82, 19, 58, 82], [102, 31, 73, 28], [64, 38], [65, 95, 57, 16]]]
 h' := ![![[31, 97, 102], [24, 95, 106], [26, 56, 68], [15, 39, 17], [45, 39, 68], [29, 33, 66], [0, 1]], ![[35, 11, 7], [47, 2, 65], [87, 75, 29], [15, 73, 23], [15, 61, 39], [45, 95, 59], [31, 97, 102]], ![[0, 1], [90, 12, 47], [29, 87, 12], [46, 106, 69], [107, 9, 2], [70, 90, 93], [35, 11, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 90], []]
 b := ![[], [43, 46, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [80, 76, 43, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17004, 2289, -763]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-156, 21, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [1, 29, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 71, 54], [20, 41, 59], [0, 1]]
 g := ![![[46, 50, 22], [27, 36], [19, 52], [32, 106], [54, 91, 111], [1]], ![[19, 92, 79, 19], [15, 9], [55, 100], [47, 91], [78, 80, 107, 46], [86, 101, 99, 55]], ![[3, 76, 44, 37], [29, 81], [92, 28], [82, 111], [64, 93, 97, 58], [22, 11, 80, 58]]]
 h' := ![![[67, 71, 54], [72, 55, 94], [72, 61, 107], [59, 65, 74], [59, 39, 85], [112, 84, 87], [0, 1]], ![[20, 41, 59], [107, 31, 44], [110, 15, 110], [74, 65, 103], [11, 105, 54], [97, 68, 80], [67, 71, 54]], ![[0, 1], [86, 27, 88], [51, 37, 9], [16, 96, 49], [95, 82, 87], [68, 74, 59], [20, 41, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 34], []]
 b := ![[], [83, 2, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [1, 29, 26, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64636, -54918, 2825]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![572, -486, 25]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![46, 26, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![46, 26, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![46, 26, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![46, 26, 1], ![-155, 67, 27], ![-4185, 412, 94]]]
  hmulB := by decide  
  f := ![![![-45, -26, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -26, 127]], ![![0, 0, 1], ![-11, -5, 27], ![-67, -16, 94]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [93, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 126], [0, 1]]
 g := ![![[72, 70], [2, 88], [112, 115], [50, 36], [26, 121], [35, 1]], ![[109, 57], [34, 39], [73, 12], [40, 91], [70, 6], [70, 126]]]
 h' := ![![[35, 126], [68, 18], [125, 71], [49, 78], [122, 121], [47, 116], [0, 1]], ![[0, 1], [63, 109], [70, 56], [112, 49], [39, 6], [43, 11], [35, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [59, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [93, 92, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5861, -2336, 340]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -88, 340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-27, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-27, 1, 0]] 
 ![![127, 0, 0], ![100, 1, 0], ![33, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-27, 1, 0], ![0, -27, 1], ![-155, 21, -26]]]
  hmulB := by decide  
  f := ![![![2539, -94, 0], ![11938, 0, 0]], ![![1972, -73, 0], ![9272, 0, 0]], ![![681, -25, 0], ![3202, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 127, 0], ![-33, 0, 127]], ![![-1, 1, 0], ![21, -27, 1], ![-11, 21, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![46, 26, 1]] ![![127, 0, 0], ![-27, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3429, 127, 0]], ![![5842, 3302, 127], ![-1397, -635, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-27, 1, 0]]], ![![![46, 26, 1]], ![![-11, -5, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![579, 42, -8]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![579, 42, -8]] 
 ![![131, 0, 0], ![0, 131, 0], ![75, 93, 1]] where
  M :=![![![579, 42, -8], ![1240, 411, 34], ![-5270, 1954, 445]]]
  hmulB := by decide  
  f := ![![![889, -262, 36]], ![![-5580, 1645, -226]], ![![-3185, 939, -129]]]
  g := ![![![9, 6, -8], ![-10, -21, 34], ![-295, -301, 445]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [90, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 130], [0, 1]]
 g := ![![[76, 94], [119, 64], [36], [39], [38], [129], [1]], ![[64, 37], [30, 67], [36], [39], [38], [129], [1]]]
 h' := ![![[103, 130], [32, 116], [13, 8], [90, 125], [60, 68], [27, 118], [41, 103], [0, 1]], ![[0, 1], [59, 15], [51, 123], [127, 6], [121, 63], [129, 13], [39, 28], [103, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [16, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [90, 28, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![778, -230, 75]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -55, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-889, 262, -36]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-889, 262, -36]] 
 ![![131, 0, 0], ![37, 1, 0], ![72, 0, 1]] where
  M :=![![![-889, 262, -36], ![5580, -1645, 226], ![-35030, 10326, -1419]]]
  hmulB := by decide  
  f := ![![![-579, -42, 8]], ![![-173, -15, 2]], ![![-278, -38, 1]]]
  g := ![![![-61, 262, -36], ![383, -1645, 226], ![-2404, 10326, -1419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![579, 42, -8]] ![![-889, 262, -36]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [32, 45, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 62], [86, 127, 75], [0, 1]]
 g := ![![[64, 55, 115], [130, 59], [25, 128], [94, 104, 19], [6, 44], [93, 1], []], ![[55, 20, 101, 51], [93, 60], [67, 81], [101, 27, 68, 20], [25, 8], [115, 100], [79, 8]], ![[125, 3, 76, 106], [105, 126], [77, 129], [0, 132, 27, 46], [51, 112], [20, 81], [66, 8]]]
 h' := ![![[7, 9, 62], [26, 13, 65], [58, 68, 14], [6, 64, 26], [19, 54, 29], [38, 30, 110], [0, 0, 1], [0, 1]], ![[86, 127, 75], [94, 68, 19], [78, 123, 103], [116, 118, 9], [20, 70, 44], [51, 29, 75], [124, 14, 127], [7, 9, 62]], ![[0, 1], [49, 56, 53], [11, 83, 20], [3, 92, 102], [75, 13, 64], [101, 78, 89], [78, 123, 9], [86, 127, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 130], []]
 b := ![[], [74, 36, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [32, 45, 44, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24523, 8220, 2055]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-179, 60, 15]
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



lemma PB211I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB211I2 : PrimesBelowBoundCertificateInterval O 79 137 211 where
  m := 11
  g := ![2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB211I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I101N1, I127N1, I131N1]
  Il := ![[I83N1], [], [], [I101N1], [], [], [], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
