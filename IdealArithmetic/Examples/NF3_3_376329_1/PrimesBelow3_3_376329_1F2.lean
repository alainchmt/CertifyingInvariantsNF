
import IdealArithmetic.Examples.NF3_3_376329_1.RI3_3_376329_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [26, 67, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 71, 8], [38, 11, 75], [0, 1]]
 g := ![![[28, 10, 4], [29, 7, 68], [30, 38], [23, 64], [28, 57, 1], []], ![[39, 58, 1, 8], [51, 44, 5, 39], [54, 41], [60, 31], [30, 24, 2, 55], [53, 64]], ![[65, 65, 23, 11], [72, 11, 71, 9], [17, 12], [56, 59], [28, 35, 34, 10], [69, 64]]]
 h' := ![![[19, 71, 8], [76, 70, 2], [28, 49, 63], [12, 82, 72], [19, 45, 75], [0, 0, 1], [0, 1]], ![[38, 11, 75], [36, 19, 1], [51, 35, 6], [58, 60, 37], [46, 8, 23], [62, 56, 11], [19, 71, 8]], ![[0, 1], [44, 77, 80], [9, 82, 14], [6, 24, 57], [47, 30, 68], [65, 27, 71], [38, 11, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 38], []]
 b := ![[], [17, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [26, 67, 26, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1282018, 648064, -171810]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15446, 7808, -2070]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79873, 7896, 1378]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-79873, 7896, 1378]] 
 ![![89, 0, 0], ![0, 89, 0], ![86, 76, 1]] where
  M :=![![![-79873, 7896, 1378], ![-628368, 47909, 15792], ![-3286392, 372768, 40013]]]
  hmulB := by decide  
  f := ![![![44604151, -2221704, -659270]], ![![300627120, -14974043, -4443408]], ![![309510130, -15416500, -4574703]]]
  g := ![![![-2229, -1088, 1378], ![-22320, -12947, 15792], ![-75590, -29980, 40013]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [76, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 88], [0, 1]]
 g := ![![[57, 72], [40], [67], [49, 50], [45, 40], [1]], ![[9, 17], [40], [67], [75, 39], [48, 49], [1]]]
 h' := ![![[29, 88], [76, 61], [88, 60], [14, 44], [51, 36], [13, 29], [0, 1]], ![[0, 1], [65, 28], [48, 29], [44, 45], [27, 53], [53, 60], [29, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [69, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [76, 60, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17, -2893, 1626]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1571, -1421, 1626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44604151, -2221704, -659270]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![44604151, -2221704, -659270]] 
 ![![89, 0, 0], ![26, 1, 0], ![5, 0, 1]] where
  M :=![![![44604151, -2221704, -659270], ![300627120, -14974043, -4443408], ![862783464, -42974688, -12752339]]]
  hmulB := by decide  
  f := ![![![-79873, 7896, 1378]], ![![-30394, 2845, 580]], ![![-41413, 4632, 527]]]
  g := ![![![1187245, -2221704, -659270], ![8001902, -14974043, -4443408], ![22965023, -42974688, -12752339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-79873, 7896, 1378]] ![![44604151, -2221704, -659270]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3483923, 173532, 51494]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-3483923, 173532, 51494]] 
 ![![97, 0, 0], ![10, 1, 0], ![42, 0, 1]] where
  M :=![![![-3483923, 173532, 51494], ![-23481264, 1169587, 347064], ![-67389960, 3356652, 996055]]]
  hmulB := by decide  
  f := ![![![-90443, 21828, -2930]], ![![4450, -1085, 148]], ![![-148662, 35916, -4829]]]
  g := ![![![-76103, 173532, 51494], ![-512926, 1169587, 347064], ![-1472070, 3356652, 996055]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![473, -30, -14]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![473, -30, -14]] 
 ![![97, 0, 0], ![24, 1, 0], ![88, 0, 1]] where
  M :=![![![473, -30, -14], ![6384, -775, -60], ![10488, 582, -745]]]
  hmulB := by decide  
  f := ![![![-612295, 30498, 9050]], ![![-194040, 9665, 2868]], ![![-677584, 33750, 10015]]]
  g := ![![![25, -30, -14], ![312, -775, -60], ![640, 582, -745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, 30, -4]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-125, 30, -4]] 
 ![![97, 0, 0], ![62, 1, 0], ![84, 0, 1]] where
  M :=![![![-125, 30, -4], ![1824, -443, 60], ![-14592, 3522, -473]]]
  hmulB := by decide  
  f := ![![![-1781, 102, 28]], ![![-1270, 73, 20]], ![![-1956, 114, 31]]]
  g := ![![![-17, 30, -4], ![250, -443, 60], ![-1992, 3522, -473]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-3483923, 173532, 51494]] ![![473, -30, -14]]
  ![![1781, -102, -28]] where
 M := ![![![1781, -102, -28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1781, -102, -28]] ![![-125, 30, -4]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![154391, -7690, -2282]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![154391, -7690, -2282]] 
 ![![101, 0, 0], ![0, 101, 0], ![4, 44, 1]] where
  M :=![![![154391, -7690, -2282], ![1040592, -51833, -15380], ![2986344, -148734, -44143]]]
  hmulB := by decide  
  f := ![![![5299, -482, -106]], ![![48336, -4405, -964]], ![![23204, -2114, -463]]]
  g := ![![![1619, 918, -2282], ![10912, 6187, -15380], ![31316, 17758, -44143]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [5, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 100], [0, 1]]
 g := ![![[22, 81], [45], [38, 23], [9], [19], [92, 1]], ![[0, 20], [45], [33, 78], [9], [19], [83, 100]]]
 h' := ![![[92, 100], [20, 92], [12, 67], [76, 86], [11, 3], [45, 76], [0, 1]], ![[0, 1], [0, 9], [15, 34], [9, 15], [85, 98], [68, 25], [92, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [28, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [5, 9, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3753, -228, 206]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -92, 206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5299, 482, 106]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-5299, 482, 106]] 
 ![![101, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![-5299, 482, 106], ![-48336, 4405, 964], ![-195624, 17766, 3923]]]
  hmulB := by decide  
  f := ![![![-154391, 7690, 2282]], ![![-30175, 1503, 446]], ![![-44854, 2234, 663]]]
  g := ![![![-125, 482, 106], ![-1141, 4405, 964], ![-4612, 17766, 3923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![154391, -7690, -2282]] ![![-5299, 482, 106]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2598887207, 129448896, 38412756]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-2598887207, 129448896, 38412756]] 
 ![![103, 0, 0], ![0, 103, 0], ![67, 75, 1]] where
  M :=![![![-2598887207, 129448896, 38412756], ![-17516216736, 872471461, 258897792], ![-50270588208, 2503945584, 743022565]]]
  hmulB := by decide  
  f := ![![![-1400321, 127488, 27972]], ![![-12755232, 1160731, 254976]], ![![-10701173, 973887, 213889]]]
  g := ![![![-50218853, -26713668, 38412756], ![-338469600, -180047213, 258897792], ![-971389321, -516725697, 743022565]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [13, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 102], [0, 1]]
 g := ![![[48, 8], [43, 93], [54, 9], [4], [14], [97, 1]], ![[0, 95], [0, 10], [0, 94], [4], [14], [91, 102]]]
 h' := ![![[97, 102], [59, 27], [19, 89], [85, 100], [31, 2], [78, 23], [0, 1]], ![[0, 1], [0, 76], [0, 14], [0, 3], [19, 101], [43, 80], [97, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [39, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [13, 6, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3400, -3972, 2143]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1427, -1599, 2143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1400321, 127488, 27972]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1400321, 127488, 27972]] 
 ![![103, 0, 0], ![56, 1, 0], ![52, 0, 1]] where
  M :=![![![-1400321, 127488, 27972], ![-12755232, 1160731, 254976], ![-51756912, 4713840, 1033243]]]
  hmulB := by decide  
  f := ![![![-2598887207, 129448896, 38412756]], ![![-1583047576, 78850579, 23398176]], ![![-1800123524, 89662992, 26606659]]]
  g := ![![![-97031, 127488, 27972], ![-883640, 1160731, 254976], ![-3586996, 4713840, 1033243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-2598887207, 129448896, 38412756]] ![![-1400321, 127488, 27972]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64861, 5904, 1296]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-64861, 5904, 1296]] 
 ![![107, 0, 0], ![21, 1, 0], ![90, 0, 1]] where
  M :=![![![-64861, 5904, 1296], ![-590976, 53795, 11808], ![-2396736, 218160, 47891]]]
  hmulB := by decide  
  f := ![![![263065, -13104, -3888]], ![![68199, -3397, -1008]], ![![268830, -13392, -3973]]]
  g := ![![![-2855, 5904, 1296], ![-26013, 53795, 11808], ![-105498, 218160, 47891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![548291, -27310, -8104]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![548291, -27310, -8104]] 
 ![![107, 0, 0], ![38, 1, 0], ![8, 0, 1]] where
  M :=![![![548291, -27310, -8104], ![3695424, -184067, -54620], ![10605648, -528258, -156757]]]
  hmulB := by decide  
  f := ![![![-338759, 30838, 6768]], ![![-149150, 13577, 2980]], ![![-142328, 12958, 2843]]]
  g := ![![![15429, -27310, -8104], ![103990, -184067, -54620], ![298444, -528258, -156757]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -2, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![13, -2, 0]] 
 ![![107, 0, 0], ![47, 1, 0], ![49, 0, 1]] where
  M :=![![![13, -2, 0], ![0, 11, -4], ![912, -174, 13]]]
  hmulB := by decide  
  f := ![![![-553, 26, 8]], ![![-277, 13, 4]], ![![-347, 16, 5]]]
  g := ![![![1, -2, 0], ![-3, 11, -4], ![79, -174, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-64861, 5904, 1296]] ![![548291, -27310, -8104]]
  ![![553, -26, -8]] where
 M := ![![![553, -26, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![553, -26, -8]] ![![13, -2, 0]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [21, 92, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 104, 22], [47, 4, 87], [0, 1]]
 g := ![![[22, 8, 84], [43, 49], [85, 108, 81], [55, 101, 87], [56, 5], [1]], ![[23, 50, 90, 15], [95, 12], [47, 90, 7, 106], [67, 89, 52, 108], [92, 48], [67, 23, 92, 75]], ![[39, 98, 50, 61], [85, 16], [94, 92, 57, 43], [47, 30, 90, 5], [93, 105], [62, 26, 91, 34]]]
 h' := ![![[83, 104, 22], [15, 105, 56], [68, 23, 7], [44, 34, 100], [28, 24, 14], [88, 17, 21], [0, 1]], ![[47, 4, 87], [73, 26, 27], [91, 22, 98], [90, 12, 58], [101, 45, 39], [92, 108, 22], [83, 104, 22]], ![[0, 1], [95, 87, 26], [38, 64, 4], [34, 63, 60], [24, 40, 56], [61, 93, 66], [47, 4, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 94], []]
 b := ![[], [85, 24, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [21, 92, 88, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1494063, 585766, -122843]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13707, 5374, -1127]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319985, 15942, 4730]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-319985, 15942, 4730]] 
 ![![113, 0, 0], ![0, 113, 0], ![104, 63, 1]] where
  M :=![![![-319985, 15942, 4730], ![-2156880, 107467, 31884], ![-6191112, 308514, 91525]]]
  hmulB := by decide  
  f := ![![![-6577, 1590, -214]], ![![97584, -23605, 3180]], ![![41504, -10041, 1353]]]
  g := ![![![-7185, -2496, 4730], ![-48432, -16825, 31884], ![-139024, -48297, 91525]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [72, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 112], [0, 1]]
 g := ![![[104, 11], [28], [82], [18], [7, 13], [83, 1]], ![[0, 102], [28], [82], [18], [69, 100], [53, 112]]]
 h' := ![![[83, 112], [71, 89], [77, 64], [52, 46], [61, 40], [13, 37], [0, 1]], ![[0, 1], [0, 24], [78, 49], [28, 67], [104, 73], [33, 76], [83, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [21, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [72, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-282389, -26428, 39839]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39165, -22445, 39839]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6577, -1590, 214]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![6577, -1590, 214]] 
 ![![113, 0, 0], ![100, 1, 0], ![35, 0, 1]] where
  M :=![![![6577, -1590, 214], ![-97584, 23605, -3180], ![773832, -187122, 25195]]]
  hmulB := by decide  
  f := ![![![319985, -15942, -4730]], ![![302260, -15059, -4468]], ![![153899, -7668, -2275]]]
  g := ![![![1399, -1590, 214], ![-20768, 23605, -3180], ![164639, -187122, 25195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-319985, 15942, 4730]] ![![6577, -1590, 214]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3974435, 197964, 58744]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-3974435, 197964, 58744]] 
 ![![127, 0, 0], ![0, 127, 0], ![73, 103, 1]] where
  M :=![![![-3974435, 197964, 58744], ![-26787264, 1334257, 395928], ![-76877952, 3829236, 1136293]]]
  hmulB := by decide  
  f := ![![![40459, -3684, -808]], ![![368448, -33521, -7368]], ![![333853, -30377, -6675]]]
  g := ![![![-65061, -46084, 58744], ![-438504, -310601, 395928], ![-1258483, -891409, 1136293]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [117, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 126], [0, 1]]
 g := ![![[11, 38], [91, 2], [50, 49], [107, 69], [59, 120], [110, 1]], ![[0, 89], [57, 125], [106, 78], [77, 58], [51, 7], [93, 126]]]
 h' := ![![[110, 126], [21, 61], [119, 16], [54, 7], [82, 14], [84, 45], [0, 1]], ![[0, 1], [0, 66], [101, 111], [62, 120], [98, 113], [81, 82], [110, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [120, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [117, 17, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1495, 154, 110]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -88, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40459, 3684, 808]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-40459, 3684, 808]] 
 ![![127, 0, 0], ![48, 1, 0], ![94, 0, 1]] where
  M :=![![![-40459, 3684, 808], ![-368448, 33521, 7368], ![-1495680, 136284, 29837]]]
  hmulB := by decide  
  f := ![![![3974435, -197964, -58744]], ![![1713072, -85327, -25320]], ![![3547046, -176676, -52427]]]
  g := ![![![-2309, 3684, 808], ![-21024, 33521, 7368], ![-85370, 136284, 29837]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-3974435, 197964, 58744]] ![![-40459, 3684, 808]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142349639, -12956280, -2844718]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![142349639, -12956280, -2844718]] 
 ![![131, 0, 0], ![0, 131, 0], ![73, 22, 1]] where
  M :=![![![142349639, -12956280, -2844718], ![1297191408, -118097107, -25912560], ![5259467976, -478600656, -105140827]]]
  hmulB := by decide  
  f := ![![![-114956348459, 5725901592, 1699108046]], ![![-774793268976, 38591953135, 11451803184]], ![![-211151754553, 10517332742, 3120920679]]]
  g := ![![![2671863, 378836, -2844718], ![24342048, 3450223, -25912560], ![98738537, 14003798, -105140827]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [47, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 130], [0, 1]]
 g := ![![[57, 34], [130, 3], [46], [114], [89], [75], [1]], ![[16, 97], [84, 128], [46], [114], [89], [75], [1]]]
 h' := ![![[72, 130], [47, 54], [23, 38], [73, 35], [45, 30], [125, 73], [84, 72], [0, 1]], ![[0, 1], [5, 77], [8, 93], [104, 96], [109, 101], [10, 58], [28, 59], [72, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [4, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [47, 59, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7933, -2904, 2488]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1447, -440, 2488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-114956348459, 5725901592, 1699108046]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-114956348459, 5725901592, 1699108046]] 
 ![![131, 0, 0], ![87, 1, 0], ![102, 0, 1]] where
  M :=![![![-114956348459, 5725901592, 1699108046], ![-774793268976, 38591953135, 11451803184], ![-2223614491464, 110756804016, 32866051543]]]
  hmulB := by decide  
  f := ![![![142349639, -12956280, -2844718]], ![![104439771, -9506057, -2087046]], ![![150985734, -13741536, -3017573]]]
  g := ![![![-6003197005, 5725901592, 1699108046], ![-40460894019, 38591953135, 11451803184], ![-116120562582, 110756804016, 32866051543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![142349639, -12956280, -2844718]] ![![-114956348459, 5725901592, 1699108046]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB137I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 136 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 136 (by omega)

def PB137I2 : PrimesBelowBoundCertificateInterval O 79 136 137 where
  m := 10
  g := ![1, 2, 3, 2, 2, 3, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB137I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
  β := ![I89N1, I97N0, I97N1, I97N2, I101N1, I103N1, I107N0, I107N1, I107N2, I113N1, I127N1, I131N1]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [], [I113N1], [I127N1], [I131N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
