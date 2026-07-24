
import IdealArithmetic.Examples.NF3_3_567849_1.RI3_3_567849_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [76, 86, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 118, 127], [26, 20, 12], [0, 1]]
 g := ![![[37, 31, 91], [92, 45, 7], [81, 89], [33, 45, 113], [75, 137], [133, 1], []], ![[110, 55, 134, 30], [40, 23, 115, 124], [43, 13], [24, 14, 92, 44], [59, 69], [69, 122], [57, 5]], ![[51, 137, 77, 18], [69, 104, 118, 105], [136, 35], [133, 98, 11, 90], [81, 65], [9, 24], [33, 5]]]
 h' := ![![[107, 118, 127], [97, 82, 62], [135, 68, 110], [133, 78, 28], [130, 83, 104], [39, 23, 89], [0, 0, 1], [0, 1]], ![[26, 20, 12], [43, 13, 117], [66, 45, 133], [89, 132, 41], [108, 6, 111], [127, 10, 114], [28, 93, 20], [107, 118, 127]], ![[0, 1], [123, 44, 99], [126, 26, 35], [71, 68, 70], [105, 50, 63], [80, 106, 75], [114, 46, 118], [26, 20, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 109], []]
 b := ![[], [99, 81, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [76, 86, 6, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35862, 29746, -56017]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258, 214, -403]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52445, 20836, -3838]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-52445, 20836, -3838]] 
 ![![149, 0, 0], ![0, 149, 0], ![87, 49, 1]] where
  M :=![![![-52445, 20836, -3838], ![445208, -211995, 41672], ![-2639580, 1201896, -232831]]]
  hmulB := by decide  
  f := ![![![4875183, -1599932, -366718]], ![![42539288, -13960495, -3199864]], ![![17938849, -5887151, -1349385]]]
  g := ![![![1889, 1402, -3838], ![-21344, -15127, 41672], ![118233, 84635, -232831]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [34, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 148], [0, 1]]
 g := ![![[12, 30], [7], [20, 46], [36], [81, 123], [31], [1]], ![[139, 119], [7], [26, 103], [36], [110, 26], [31], [1]]]
 h' := ![![[39, 148], [113, 103], [65, 56], [86, 33], [77, 143], [102, 47], [115, 39], [0, 1]], ![[0, 1], [107, 46], [14, 93], [32, 116], [141, 6], [147, 102], [146, 110], [39, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [72, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [34, 110, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75, -443, 1186]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-693, -393, 1186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4875183, -1599932, -366718]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![4875183, -1599932, -366718]] 
 ![![149, 0, 0], ![51, 1, 0], ![15, 0, 1]] where
  M :=![![![4875183, -1599932, -366718], ![42539288, -13960495, -3199864], ![164322468, -53927160, -12360563]]]
  hmulB := by decide  
  f := ![![![-52445, 20836, -3838]], ![![-14963, 5709, -1034]], ![![-22995, 10164, -1949]]]
  g := ![![![617265, -1599932, -366718], ![5386057, -13960495, -3199864], ![20805477, -53927160, -12360563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-52445, 20836, -3838]] ![![4875183, -1599932, -366718]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72093, 23428, 5382]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-72093, 23428, 5382]] 
 ![![151, 0, 0], ![0, 151, 0], ![18, 131, 1]] where
  M :=![![![-72093, 23428, 5382], ![-624312, 204289, 46856], ![-2405492, 788960, 180861]]]
  hmulB := by decide  
  f := ![![![129781, -59412, 11530]], ![![-1337480, 612279, -118824]], ![![-1094790, 501179, -97263]]]
  g := ![![![-1119, -4514, 5382], ![-9720, -39297, 46856], ![-37490, -151681, 180861]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [27, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 150], [0, 1]]
 g := ![![[17, 137], [11, 148], [41, 18], [59], [140, 37], [36], [1]], ![[101, 14], [29, 3], [84, 133], [59], [69, 114], [36], [1]]]
 h' := ![![[145, 150], [5, 99], [101, 65], [93, 138], [146, 132], [59, 108], [124, 145], [0, 1]], ![[0, 1], [15, 52], [13, 86], [20, 13], [109, 19], [15, 43], [9, 6], [145, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [63, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [27, 6, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3797, -58, 169]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -147, 169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129781, 59412, -11530]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-129781, 59412, -11530]] 
 ![![151, 0, 0], ![40, 1, 0], ![86, 0, 1]] where
  M :=![![![-129781, 59412, -11530], ![1337480, -612279, 118824], ![-7560532, 3461104, -671691]]]
  hmulB := by decide  
  f := ![![![72093, -23428, -5382]], ![![23232, -7559, -1736]], ![![56990, -18568, -4263]]]
  g := ![![![-10031, 59412, -11530], ![103376, -612279, 118824], ![-584366, 3461104, -671691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-72093, 23428, 5382]] ![![-129781, 59412, -11530]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194229, 5572, 4320]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-194229, 5572, 4320]] 
 ![![157, 0, 0], ![0, 157, 0], ![149, 125, 1]] where
  M :=![![![-194229, 5572, 4320], ![-501120, 14383, 11144], ![-395792, 11324, 8811]]]
  hmulB := by decide  
  f := ![![![-3401, 1116, 256]], ![![-29696, 9747, 2232]], ![![-27601, 9059, 2075]]]
  g := ![![![-5337, -3404, 4320], ![-13768, -8781, 11144], ![-10883, -6943, 8811]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [137, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 156], [0, 1]]
 g := ![![[129, 49], [147], [116, 93], [135, 52], [92, 144], [71], [1]], ![[7, 108], [147], [3, 64], [60, 105], [150, 13], [71], [1]]]
 h' := ![![[68, 156], [83, 150], [122, 33], [31, 67], [113, 44], [93, 12], [20, 68], [0, 1]], ![[0, 1], [78, 7], [11, 124], [34, 90], [122, 113], [124, 145], [91, 89], [68, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [41, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [137, 89, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-643, -688, 728]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-695, -584, 728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3401, -1116, -256]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![3401, -1116, -256]] 
 ![![157, 0, 0], ![64, 1, 0], ![118, 0, 1]] where
  M :=![![![3401, -1116, -256], ![29696, -9747, -2232], ![114608, -37604, -8631]]]
  hmulB := by decide  
  f := ![![![194229, -5572, -4320]], ![![82368, -2363, -1832]], ![![148502, -4260, -3303]]]
  g := ![![![669, -1116, -256], ![5840, -9747, -2232], ![22546, -37604, -8631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-194229, 5572, 4320]] ![![3401, -1116, -256]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1791861, -821756, 159572]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![1791861, -821756, 159572]] 
 ![![163, 0, 0], ![0, 163, 0], ![130, 145, 1]] where
  M :=![![![1791861, -821756, 159572], ![-18510352, 8469989, -1643512], ![104578872, -47877708, 9291745]]]
  hmulB := by decide  
  f := ![![![82149143, -26959612, -6179372]], ![![716807152, -235240953, -53919224]], ![![720155442, -236339791, -54171087]]]
  g := ![![![-116273, -146992, 159572], ![1197216, 1513983, -1643512], ![-6769006, -8559391, 9291745]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [129, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 162], [0, 1]]
 g := ![![[125, 146], [59, 1], [39], [40], [60], [99, 144], [1]], ![[84, 17], [71, 162], [39], [40], [60], [34, 19], [1]]]
 h' := ![![[12, 162], [50, 31], [58, 162], [6, 56], [73, 140], [106, 68], [34, 12], [0, 1]], ![[0, 1], [96, 132], [46, 1], [26, 107], [123, 23], [107, 95], [15, 151], [12, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [21, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [129, 151, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-741, -256, -22]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 18, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![82149143, -26959612, -6179372]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![82149143, -26959612, -6179372]] 
 ![![163, 0, 0], ![36, 1, 0], ![149, 0, 1]] where
  M :=![![![82149143, -26959612, -6179372], ![716807152, -235240953, -53919224], ![2768911416, -908698188, -208281341]]]
  hmulB := by decide  
  f := ![![![1791861, -821756, 159572]], ![![282188, -129529, 25160]], ![![2279547, -1044904, 202871]]]
  g := ![![![12106881, -26959612, -6179372], ![105640772, -235240953, -53919224], ![408073411, -908698188, -208281341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![1791861, -821756, 159572]] ![![82149143, -26959612, -6179372]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [155, 58, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 101, 43], [24, 65, 124], [0, 1]]
 g := ![![[67, 145, 6], [130, 159, 108], [124, 108, 154], [30, 114], [54, 66], [158, 160, 1], []], ![[59, 161, 105, 26], [123, 125, 144, 160], [55, 54, 85, 80], [17, 72], [156, 1], [0, 43, 137, 146], [85, 12]], ![[52, 31, 165, 4], [147, 121, 91, 66], [51, 163, 48, 133], [29, 9], [143, 107], [130, 25, 62, 66], [4, 12]]]
 h' := ![![[136, 101, 43], [57, 104, 29], [152, 122, 129], [138, 42, 34], [121, 79, 75], [59, 104, 147], [0, 0, 1], [0, 1]], ![[24, 65, 124], [7, 64, 11], [83, 117, 104], [58, 18, 8], [122, 17, 89], [134, 2, 166], [144, 141, 65], [136, 101, 43]], ![[0, 1], [108, 166, 127], [76, 95, 101], [151, 107, 125], [53, 71, 3], [95, 61, 21], [123, 26, 101], [24, 65, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 10], []]
 b := ![[], [26, 70, 159], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [155, 58, 7, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59280825, 7124888, 20526972]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-354975, 42664, 122916]
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



lemma PB168I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 167 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 167 (by omega)

def PB168I3 : PrimesBelowBoundCertificateInterval O 137 167 168 where
  m := 6
  g := ![1, 2, 2, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB168I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
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
  β := ![I149N1, I151N1, I157N1, I163N1]
  Il := ![[], [I149N1], [I151N1], [I157N1], [I163N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
