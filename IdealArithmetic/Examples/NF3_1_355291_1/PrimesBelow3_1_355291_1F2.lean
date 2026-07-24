
import IdealArithmetic.Examples.NF3_1_355291_1.RI3_1_355291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18037485, 4004259, -1725484]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-18037485, 4004259, -1725484]] 
 ![![83, 0, 0], ![0, 83, 0], ![25, 30, 1]] where
  M :=![![![-18037485, 4004259, -1725484], ![220861952, -49030586, 21127877], ![-291683200, 64752657, -27902709]]]
  hmulB := by decide  
  f := ![![![-8895, -321, 307]], ![![-39296, -4555, -1019]], ![![-16861, -1830, -343]]]
  g := ![![![302405, 671913, -1725484], ![-3702831, -8227312, 21127877], ![4890175, 10865469, -27902709]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [33, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 82], [0, 1]]
 g := ![![[59, 78], [78, 37], [75], [17], [9, 33], [1]], ![[0, 5], [0, 46], [75], [17], [0, 50], [1]]]
 h' := ![![[45, 82], [82, 24], [15, 55], [0, 65], [35, 73], [50, 45], [0, 1]], ![[0, 1], [0, 59], [0, 28], [20, 18], [0, 10], [0, 38], [45, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [75, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [33, 38, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3039, -2933, 1399]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-458, -541, 1399]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8895, -321, 307]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-8895, -321, 307]] 
 ![![83, 0, 0], ![35, 1, 0], ![6, 0, 1]] where
  M :=![![![-8895, -321, 307], ![-39296, -4555, -1019], ![1792, -7215, -5574]]]
  hmulB := by decide  
  f := ![![![-18037485, 4004259, -1725484]], ![![-4945181, 1097813, -473061]], ![![-4818170, 1069617, -460911]]]
  g := ![![![6, -321, 307], ![1521, -4555, -1019], ![3467, -7215, -5574]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-18037485, 4004259, -1725484]] ![![-8895, -321, 307]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149425863851057355, 33172022619012518, -14294228787861652]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-149425863851057355, 33172022619012518, -14294228787861652]] 
 ![![89, 0, 0], ![0, 89, 0], ![82, 42, 1]] where
  M :=![![![-149425863851057355, 33172022619012518, -14294228787861652], ![1829661284846291456, -406178448374573081, 175027243181641018], ![-2416357610387310848, 536422994263477522, -231151205192932063]]]
  hmulB := by decide  
  f := ![![![865782037, 18283390, -39695208]], ![![5080986624, 374284579, -30797102]], ![![3226250314, 201085956, -47247167]]]
  g := ![![![11491021311838181, 7118310468642718, -14294228787861652], ![-140703063551104180, -87160928786556133, 175027243181641018], ![185820687813855262, 115109815869287912, -231151205192932063]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [2, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 88], [0, 1]]
 g := ![![[39, 45], [22], [9], [81, 68], [41, 32], [1]], ![[0, 44], [22], [9], [28, 21], [37, 57], [1]]]
 h' := ![![[11, 88], [85, 57], [60, 17], [16, 3], [7, 35], [87, 11], [0, 1]], ![[0, 1], [0, 32], [69, 72], [49, 86], [36, 54], [30, 78], [11, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [19, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [2, 78, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1483, -3117, 2386]
  a := ![-1, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2215, -1161, 2386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![865782037, 18283390, -39695208]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![865782037, 18283390, -39695208]] 
 ![![89, 0, 0], ![58, 1, 0], ![2, 0, 1]] where
  M :=![![![865782037, 18283390, -39695208], ![5080986624, 374284579, -30797102], ![2740712704, 677459786, 343487477]]]
  hmulB := by decide  
  f := ![![![-149425863851057355, 33172022619012518, -14294228787861652]], ![![-76820660882191406, 17053919814923067, -7348741870947582]], ![![-30507970090892422, 6772663365185422, -2918423177175903]]]
  g := ![![![-1295103, 18283390, -39695208], ![-186133986, 374284579, -30797102], ![-418414942, 677459786, 343487477]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-149425863851057355, 33172022619012518, -14294228787861652]] ![![865782037, 18283390, -39695208]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10354710406084095, 2298709734389234, -990542037114484]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-10354710406084095, 2298709734389234, -990542037114484]] 
 ![![97, 0, 0], ![0, 97, 0], ![67, 49, 1]] where
  M :=![![![-10354710406084095, 2298709734389234, -990542037114484], ![126789380750653952, -28146802017511121, 12128799992266702], ![-167445465251168000, 37172311523655382, -16018002025244419]]]
  hmulB := by decide  
  f := ![![![8309345, -12736414, -10157832]], ![![1300202496, -65217565, -129786226]], ![![692753731, -41929969, -74588697]]]
  g := ![![![577439237944189, 524074943845350, -990542037114484], ![-7070517718878506, -6417092800397727, 12128799992266702], ![9337738870517609, 8474787739800329, -16018002025244419]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [46, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 96], [0, 1]]
 g := ![![[12, 6], [88], [89], [94], [70], [30, 1]], ![[95, 91], [88], [89], [94], [70], [60, 96]]]
 h' := ![![[30, 96], [20, 54], [73, 66], [53, 34], [77, 26], [75, 78], [0, 1]], ![[0, 1], [88, 43], [16, 31], [6, 63], [81, 71], [87, 19], [30, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [48, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [46, 67, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146, -156, 173]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -89, 173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8309345, -12736414, -10157832]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![8309345, -12736414, -10157832]] 
 ![![97, 0, 0], ![41, 1, 0], ![13, 0, 1]] where
  M :=![![![8309345, -12736414, -10157832], ![1300202496, -65217565, -129786226], ![2930463488, -18206570, -195003791]]]
  hmulB := by decide  
  f := ![![![-10354710406084095, 2298709734389234, -990542037114484]], ![![-3069626246379319, 681446361777809, -293643541540486]], ![![-3113986603404755, 691294206914592, -297887098017863]]]
  g := ![![![6830455, -12736414, -10157832], ![58364367, -65217565, -129786226], ![64041053, -18206570, -195003791]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-10354710406084095, 2298709734389234, -990542037114484]] ![![8309345, -12736414, -10157832]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3955661067539910322969, 878143013691217820440, -378402525837246045658]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-3955661067539910322969, 878143013691217820440, -378402525837246045658]] 
 ![![101, 0, 0], ![0, 101, 0], ![48, 76, 1]] where
  M :=![![![-3955661067539910322969, 878143013691217820440, -378402525837246045658], ![48435523307167493844224, -10752517892823270286527, 4633390992489540560448], ![-63966782445308387172096, 14200403460650348572736, -6119126900333729726079]]]
  hmulB := by decide  
  f := ![![![-38586351405, -8162547272, -3794511954]], ![![485697530112, -55838341083, -72315878720]], ![![362290802000, -46334357108, -57488094815]]]
  g := ![![![140669902699484157115, 293433019577444725648, -378402525837246045658], ![-1722447963686440129280, -3592972607148795573075, 4633390992489540560448], ![2274765433373372670096, 4745089583029839680740, -6119126900333729726079]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 100], [0, 1]]
 g := ![![[2, 1], [23], [47, 31], [96], [95], [97, 1]], ![[99, 100], [23], [24, 70], [96], [95], [93, 100]]]
 h' := ![![[97, 100], [3, 1], [7, 86], [29, 43], [76, 46], [8, 14], [0, 1]], ![[0, 1], [100, 100], [67, 15], [59, 58], [94, 55], [53, 87], [97, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [50, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4089, -5641, 3191]
  a := ![1, 7, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1557, -2457, 3191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38586351405, -8162547272, -3794511954]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-38586351405, -8162547272, -3794511954]] 
 ![![101, 0, 0], ![70, 1, 0], ![37, 0, 1]] where
  M :=![![![-38586351405, -8162547272, -3794511954], ![485697530112, -55838341083, -72315878720], ![1530503580928, -44253876544, -128154219803]]]
  hmulB := by decide  
  f := ![![![-3955661067539910322969, 878143013691217820440, -378402525837246045658]], ![![-2261987637827982463006, 502153396688732446973, -216384017981363194412]], ![![-2082438039052327417049, 462294009576489187416, -199208122339721122925]]]
  g := ![![![6665236633, -8162547272, -3794511954], ![70000682362, -55838341083, -72315878720], ![92772089819, -44253876544, -128154219803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-3955661067539910322969, 878143013691217820440, -378402525837246045658]] ![![-38586351405, -8162547272, -3794511954]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [79, 30, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 55, 84], [15, 47, 19], [0, 1]]
 g := ![![[81, 71, 4], [50, 40, 46], [78, 31, 68], [41, 23], [94, 4], [1]], ![[24, 57, 62, 73], [68, 78, 95, 24], [42, 58, 42, 95], [57, 2], [36, 56], [52, 29, 12, 42]], ![[97, 16, 45, 60], [43, 12, 1, 14], [22, 4, 72, 76], [86, 16], [41, 38], [74, 15, 38, 61]]]
 h' := ![![[90, 55, 84], [67, 93, 2], [18, 40, 56], [83, 87, 58], [51, 59, 34], [24, 73, 2], [0, 1]], ![[15, 47, 19], [70, 2, 78], [62, 43, 18], [7, 90, 43], [9, 63, 65], [81, 35, 46], [90, 55, 84]], ![[0, 1], [35, 8, 23], [8, 20, 29], [72, 29, 2], [58, 84, 4], [1, 98, 55], [15, 47, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 42], []]
 b := ![[], [31, 52, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [79, 30, 101, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3445041, 497593, -32342]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33447, 4831, -314]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [95, 51, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18, 105], [34, 88, 2], [0, 1]]
 g := ![![[1, 75, 23], [62, 41, 13], [8, 85], [29, 4, 48], [89, 83], [1]], ![[43, 65, 20, 36], [41, 6, 14, 39], [95, 44], [62, 63, 76, 33], [58, 101], [53, 69, 62, 99]], ![[8, 68, 50, 54], [79, 55, 23, 50], [97, 102], [39, 20, 9, 95], [40, 101], [42, 46, 33, 8]]]
 h' := ![![[12, 18, 105], [102, 3, 68], [76, 81, 21], [27, 8, 37], [35, 48, 35], [12, 56, 46], [0, 1]], ![[34, 88, 2], [100, 53, 93], [89, 84, 81], [74, 16, 30], [47, 72, 95], [10, 16, 84], [12, 18, 105]], ![[0, 1], [20, 51, 53], [73, 49, 5], [73, 83, 40], [68, 94, 84], [4, 35, 84], [34, 88, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 38], []]
 b := ![[], [52, 58, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [95, 51, 61, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1831180880, -504833276, 138684947]
  a := ![1, -41, 102]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17113840, -4718068, 1296121]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26113, -5797, 2498]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![26113, -5797, 2498]] 
 ![![109, 0, 0], ![26, 1, 0], ![8, 0, 1]] where
  M :=![![![26113, -5797, 2498], ![-319744, 70982, -30587], ![422272, -93743, 40395]]]
  hmulB := by decide  
  f := ![![![749, -199, -197]], ![![410, -55, -67]], ![![520, -13, -42]]]
  g := ![![![1439, -5797, 2498], ![-17620, 70982, -30587], ![23270, -93743, 40395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![529212003736382449, -117483226168225323, 50624953831491720]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![529212003736382449, -117483226168225323, 50624953831491720]] 
 ![![109, 0, 0], ![27, 1, 0], ![32, 0, 1]] where
  M :=![![![529212003736382449, -117483226168225323, 50624953831491720], ![-6479994090430940160, 1438536174387467338, -619882767851610381], ![8557858859101901184, -1899814933828379193, 818653406535856957]]]
  hmulB := by decide  
  f := ![![![-9485632067, 673340151, 1096436703]], ![![-3637210677, 171883810, 355072650]], ![![-4863042784, 144920973, 410461042]]]
  g := ![![![19094133831841570, -117483226168225323, 50624953831491720], ![-233800203923312166, 1438536174387467338, -619882767851610381], ![308770211590098319, -1899814933828379193, 818653406535856957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-600462297533, -14006467343, 26526498482]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-600462297533, -14006467343, 26526498482]] 
 ![![109, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![-600462297533, -14006467343, 26526498482], ![-3395391805696, -266651412202, 8060722527], ![-1602563985792, -472389122557, -258590689675]]]
  hmulB := by decide  
  f := ![![![-72761370225832864155889, 16152771392558307241999, -6960426034164099341603]], ![![-28540741560071585438979, 6335945466159578162114, -2730236112548382664776]], ![![-39498707574176805228935, 8768575849615759478598, -3778486189331352266063]]]
  g := ![![![-8905926866, -14006467343, 26526498482], ![100218576117, -266651412202, 8060722527], ![325671902852, -472389122557, -258590689675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![26113, -5797, 2498]] ![![529212003736382449, -117483226168225323, 50624953831491720]]
  ![![72761370225832864155889, -16152771392558307241999, 6960426034164099341603]] where
 M := ![![![72761370225832864155889, -16152771392558307241999, 6960426034164099341603]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![72761370225832864155889, -16152771392558307241999, 6960426034164099341603]] ![![-600462297533, -14006467343, 26526498482]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1368574915956693157633803, 303818876450867758273691, -130919256264183050680431]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-1368574915956693157633803, 303818876450867758273691, -130919256264183050680431]] 
 ![![113, 0, 0], ![0, 113, 0], ![90, 29, 1]] where
  M :=![![![-1368574915956693157633803, 303818876450867758273691, -130919256264183050680431], ![16757664801815430487095168, -3720143364215309989939617, 1603055110099342105194113], ![-22131151383895642571937280, 4913038716129741949175773, -2117088254115967884745504]]]
  hmulB := by decide  
  f := ![![![-2001750888563, -123333126877, 30399270388]], ![![-3891106609664, -1297359533664, -741734806587]], ![![-2487647239118, -446414721553, -184189994658]]]
  g := ![![![92160691573626384102699, 36287409806302444495630, -130919256264183050680431], ![-1128471638116153619295354, -444325146522975495934238, 1603055110099342105194113], ![1490325588376473159780160, 586801752968962925723853, -2117088254115967884745504]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [51, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 112], [0, 1]]
 g := ![![[3, 82], [63], [61], [97], [1, 72], [73, 1]], ![[0, 31], [63], [61], [97], [59, 41], [33, 112]]]
 h' := ![![[73, 112], [32, 46], [104, 96], [27, 93], [62, 53], [6, 80], [0, 1]], ![[0, 1], [0, 67], [106, 17], [36, 20], [89, 60], [83, 33], [73, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [112, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [51, 40, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2036, -1437, 1135]
  a := ![-1, -3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-922, -304, 1135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2001750888563, 123333126877, -30399270388]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![2001750888563, 123333126877, -30399270388]] 
 ![![113, 0, 0], ![19, 1, 0], ![5, 0, 1]] where
  M :=![![![2001750888563, 123333126877, -30399270388], ![3891106609664, 1297359533664, 741734806587], ![-11895533630592, 1721455640303, 2039094340251]]]
  hmulB := by decide  
  f := ![![![1368574915956693157633803, -303818876450867758273691, 130919256264183050680431]], ![![81816447799661411574753, -18162967153550242630624, 7826643884248989891452]], ![![256407309413089454514215, -56921531844106909208356, 24528181729529939275643]]]
  g := ![![![-1677718320, 123333126877, -30399270388], ![-216525650999, 1297359533664, 741734806587], ![-484943915908, 1721455640303, 2039094340251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-1368574915956693157633803, 303818876450867758273691, -130919256264183050680431]] ![![2001750888563, 123333126877, -30399270388]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![350390766650939350291106984519, -77785532820634587049202686666, 33518734003473057689110960948]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![350390766650939350291106984519, -77785532820634587049202686666, 33518734003473057689110960948]] 
 ![![127, 0, 0], ![0, 127, 0], ![8, 106, 1]] where
  M :=![![![350390766650939350291106984519, -77785532820634587049202686666, 33518734003473057689110960948], ![-4290397952444551384206203001344, 952453439151046746018935614945, -410423793730549878587974962870], ![5666150248596675758091740891904, -1257865669068657149810561084702, 542029645420496867430960652075]]]
  hmulB := by decide  
  f := ![![![-1318412496533495, -30516749405398, 58422482944280]], ![![-7478077816867840, -584214935930221, 20072685939334]], ![![-6352720334277448, -497698198760924, 15991671835691]]]
  g := ![![![647566099394920384080466905, -28588750686525816551928854702, 33518734003473057689110960948], ![-7929193721261042169310262192, 350058075390467195876726627395, -410423793730549878587974962870], ![10471756576635439516882328152, -462307150264892323602302285076, 542029645420496867430960652075]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [70, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [120, 126], [0, 1]]
 g := ![![[89, 49], [115, 35], [34, 1], [75, 25], [82, 60], [120, 1]], ![[0, 78], [124, 92], [27, 126], [27, 102], [43, 67], [113, 126]]]
 h' := ![![[120, 126], [78, 120], [33, 17], [84, 1], [102, 122], [109, 106], [0, 1]], ![[0, 1], [0, 7], [41, 110], [77, 126], [10, 5], [2, 21], [120, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [77, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [70, 7, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7226, -7924, 4780]
  a := ![0, -8, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-358, -4052, 4780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1318412496533495, -30516749405398, 58422482944280]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-1318412496533495, -30516749405398, 58422482944280]] 
 ![![127, 0, 0], ![16, 1, 0], ![61, 0, 1]] where
  M :=![![![-1318412496533495, -30516749405398, 58422482944280], ![-7478077816867840, -584214935930221, 20072685939334], ![-3571933892976896, -1036754038790738, -564142249990887]]]
  hmulB := by decide  
  f := ![![![350390766650939350291106984519, -77785532820634587049202686666, 33518734003473057689110960948]], ![![10361057590318726145287470480, -2300118787237060210774073793, 991149215157630271163782774]], ![![212913283577196662408261944469, -47266009221475330392219881664, 20367499367183884932808891889]]]
  g := ![![![-34597763509041, -30516749405398, 58422482944280], ![5078167840286, -584214935930221, 20072685939334], ![373455180922197, -1036754038790738, -564142249990887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![350390766650939350291106984519, -77785532820634587049202686666, 33518734003473057689110960948]] ![![-1318412496533495, -30516749405398, 58422482944280]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 9, 7]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-3, 9, 7]] 
 ![![131, 0, 0], ![74, 1, 0], ![129, 0, 1]] where
  M :=![![![-3, 9, 7], ![-896, 47, 91], ![-2048, 15, 138]]]
  hmulB := by decide  
  f := ![![![-5121, 1137, -490]], ![![-2414, 536, -231]], ![![-5675, 1260, -543]]]
  g := ![![![-12, 9, 7], ![-123, 47, 91], ![-160, 15, 138]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65074742913135248380129433939, 14446366835079013524463002869, -6225115515737081905343040056]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-65074742913135248380129433939, 14446366835079013524463002869, -6225115515737081905343040056]] 
 ![![131, 0, 0], ![91, 1, 0], ![35, 0, 1]] where
  M :=![![![-65074742913135248380129433939, 14446366835079013524463002869, -6225115515737081905343040056], ![796814786014346483883909127168, -176890114091480189912291883162, 76224105782604767049868859859], ![-1052320168875767247247355240064, 233611421374714131633209512231, -100666008308875422862423023303]]]
  hmulB := by decide  
  f := ![![![-3509525793888657, -359262487931371, -55006237998399]], ![![-2384168311298265, -272745750762074, -59087252102042]], ![![-532877907382385, -121114500678338, -58754867523161]]]
  g := ![![![-8868817418736852003200429718, 14446366835079013524463002869, -6225115515737081905343040056], ![108595202030136465031733285495, -176890114091480189912291883162, 76224105782604767049868859859], ![-143417169642474148287668817080, 233611421374714131633209512231, -100666008308875422862423023303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40191194476069, -596707995560, 2033569209638]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-40191194476069, -596707995560, 2033569209638]] 
 ![![131, 0, 0], ![96, 1, 0], ![72, 0, 1]] where
  M :=![![![-40191194476069, -596707995560, 2033569209638], ![-260296858833664, -16031809183371, 3957320869632], ![-183918235401984, -30966618466816, -12074488313739]]]
  hmulB := by decide  
  f := ![![![316120738153369364083765881, -70177705559828351549371448, 30240428526189127887695778]], ![![202113099323444660934476832, -44868405840630434528573475, 19334342852672628457434944]], ![![212768432117163472081875032, -47233852700610860406489920, 20353642730477176214624525]]]
  g := ![![![-987207709895, -596707995560, 2033569209638], ![7586486413408, -16031809183371, 3957320869632], ![27925498442760, -30966618466816, -12074488313739]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-3, 9, 7]] ![![-65074742913135248380129433939, 14446366835079013524463002869, -6225115515737081905343040056]]
  ![![316120738153369364083765881, -70177705559828351549371448, 30240428526189127887695778]] where
 M := ![![![316120738153369364083765881, -70177705559828351549371448, 30240428526189127887695778]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![316120738153369364083765881, -70177705559828351549371448, 30240428526189127887695778]] ![![-40191194476069, -596707995560, 2033569209638]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [82, 54, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 65, 12], [24, 71, 125], [0, 1]]
 g := ![![[95, 30, 68], [102, 64], [129, 129], [106, 79, 18], [26, 59], [43, 1], []], ![[34, 31, 125, 131], [23, 87], [44, 130], [114, 110, 81, 13], [62, 68], [102, 109], [80, 7]], ![[28, 84, 56, 24], [11, 44], [113, 4], [2, 19, 60, 131], [89, 19], [33, 115], [104, 7]]]
 h' := ![![[19, 65, 12], [42, 91, 94], [130, 57, 8], [76, 50, 102], [123, 3, 44], [36, 62, 14], [0, 0, 1], [0, 1]], ![[24, 71, 125], [82, 136, 94], [119, 68, 19], [24, 136, 33], [54, 125, 9], [53, 97, 94], [103, 42, 71], [19, 65, 12]], ![[0, 1], [18, 47, 86], [80, 12, 110], [116, 88, 2], [68, 9, 84], [70, 115, 29], [131, 95, 65], [24, 71, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 50], []]
 b := ![[], [53, 41, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [82, 54, 94, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81899970, 18526236, -3879840]
  a := ![2, 14, -36]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-597810, 135228, -28320]
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



lemma PB169I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB169I2 : PrimesBelowBoundCertificateInterval O 79 137 169 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 3, 2, 2, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB169I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
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
      exact NI109N1
      exact NI109N2
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
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I97N1, I101N1, I109N0, I109N1, I109N2, I113N1, I127N1, I131N0, I131N1, I131N2]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [], [], [I109N0, I109N1, I109N2], [I113N1], [I127N1], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
