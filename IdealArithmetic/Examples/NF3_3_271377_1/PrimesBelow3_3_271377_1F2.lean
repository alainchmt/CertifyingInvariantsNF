
import IdealArithmetic.Examples.NF3_3_271377_1.RI3_3_271377_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142396371, 136570506, 27571342]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![142396371, 136570506, 27571342]] 
 ![![83, 0, 0], ![0, 83, 0], ![26, 78, 1]] where
  M :=![![![142396371, 136570506, 27571342], ![1268281732, 1216392505, 245569670], ![5013961544, 4808825256, 970822835]]]
  hmulB := by decide  
  f := ![![![-132852215, -733626, 3958570]], ![![182094220, 1005539, -5425822]], ![![126907838, 700794, -3781445]]]
  g := ![![![-6921187, -24264990, 27571342], ![-61644936, -216120985, 245569670], ![-243704002, -854401878, 970822835]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [52, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 82], [0, 1]]
 g := ![![[82, 64], [46, 25], [70], [17], [76, 48], [1]], ![[7, 19], [18, 58], [70], [17], [82, 35], [1]]]
 h' := ![![[52, 82], [15, 8], [24, 5], [57, 30], [32, 10], [31, 52], [0, 1]], ![[0, 1], [16, 75], [35, 78], [40, 53], [54, 73], [79, 31], [52, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [64, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [52, 31, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![190, 404, 218]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -200, 218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-132852215, -733626, 3958570]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-132852215, -733626, 3958570]] 
 ![![83, 0, 0], ![11, 1, 0], ![17, 0, 1]] where
  M :=![![![-132852215, -733626, 3958570], ![182094220, 1005539, -5425822], ![-215841016, -1191864, 6431361]]]
  hmulB := by decide  
  f := ![![![142396371, 136570506, 27571342]], ![![34152311, 32755037, 6612704]], ![![89574697, 85909926, 17343803]]]
  g := ![![![-2314193, -733626, 3958570], ![3171955, 1005539, -5425822], ![-3759803, -1191864, 6431361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![142396371, 136570506, 27571342]] ![![-132852215, -733626, 3958570]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [21, 21, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 83, 13], [55, 5, 76], [0, 1]]
 g := ![![[32, 48, 45], [49, 2], [67, 1], [45, 81, 45], [15, 6, 1], []], ![[60, 79, 40, 3], [21, 36], [46, 1], [4, 74, 78, 76], [7, 8, 66, 58], [57, 80]], ![[79, 61, 19, 19], [1, 5], [48, 4], [43, 30, 0, 65], [34, 22, 58, 66], [83, 80]]]
 h' := ![![[40, 83, 13], [28, 73, 57], [16, 58, 64], [34, 14, 88], [41, 4, 32], [0, 0, 1], [0, 1]], ![[55, 5, 76], [20, 8, 77], [4, 6, 6], [13, 69, 88], [14, 64, 34], [47, 25, 5], [40, 83, 13]], ![[0, 1], [43, 8, 44], [81, 25, 19], [56, 6, 2], [78, 21, 23], [36, 64, 83], [55, 5, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 46], []]
 b := ![[], [41, 24, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [21, 21, 83, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37914, 111695, 118548]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-426, 1255, 1332]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14430320205, -79686102, 429977302]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-14430320205, -79686102, 429977302]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 33, 1]] where
  M :=![![![-14430320205, -79686102, 429977302], ![19778955892, 109221961, -589349506], ![-23444516584, -129463656, 698571467]]]
  hmulB := by decide  
  f := ![![![39338483, 37729026, 7616870]], ![![350376020, 336041089, 67841182]], ![![150107687, 143966331, 29064439]]]
  g := ![![![-330509171, -147102444, 429977302], ![453013254, 201626347, -589349506], ![-536968523, -238993011, 698571467]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [64, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 96], [0, 1]]
 g := ![![[60, 47], [49], [95], [3], [62], [40, 1]], ![[0, 50], [49], [95], [3], [62], [80, 96]]]
 h' := ![![[40, 96], [92, 85], [67, 7], [6, 80], [95, 10], [59, 81], [0, 1]], ![[0, 1], [0, 12], [56, 90], [5, 17], [10, 87], [1, 16], [40, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [11, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [64, 57, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![466, 6, 106]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -36, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39338483, -37729026, -7616870]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-39338483, -37729026, -7616870]] 
 ![![97, 0, 0], ![32, 1, 0], ![54, 0, 1]] where
  M :=![![![-39338483, -37729026, -7616870], ![-350376020, -336041089, -67841182], ![-1385159176, -1328488104, -268199907]]]
  hmulB := by decide  
  f := ![![![14430320205, 79686102, -429977302]], ![![4556611244, 25162199, -135772414]], ![![8275070182, 45696012, -246570575]]]
  g := ![![![16281457, -37729026, -7616870], ![145014048, -336041089, -67841182], ![573291290, -1328488104, -268199907]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-14430320205, -79686102, 429977302]] ![![-39338483, -37729026, -7616870]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1220999883, -6742520, 36381884]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1220999883, -6742520, 36381884]] 
 ![![101, 0, 0], ![0, 101, 0], ![88, 57, 1]] where
  M :=![![![-1220999883, -6742520, 36381884], ![1673566664, 9241653, -49866924], ![-1983722584, -10954376, 59108577]]]
  hmulB := by decide  
  f := ![![![-767343, -735944, -148572]], ![![-6834312, -6554735, -1323316]], ![![-4793080, -4596995, -928067]]]
  g := ![![![-43788175, -20599108, 36381884], ![60018376, 28234221, -49866924], ![-71141360, -33466765, 59108577]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [51, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 100], [0, 1]]
 g := ![![[79, 92], [80], [57, 64], [16], [52], [11, 1]], ![[81, 9], [80], [54, 37], [16], [52], [22, 100]]]
 h' := ![![[11, 100], [40, 30], [22, 22], [29, 8], [80, 4], [45, 70], [0, 1]], ![[0, 1], [67, 71], [62, 79], [16, 93], [23, 97], [7, 31], [11, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [96, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [51, 90, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88, 650, 403]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-352, -221, 403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![767343, 735944, 148572]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![767343, 735944, 148572]] 
 ![![101, 0, 0], ![89, 1, 0], ![35, 0, 1]] where
  M :=![![![767343, 735944, 148572], ![6834312, 6554735, 1323316], ![27019112, 25913528, 5231419]]]
  hmulB := by decide  
  f := ![![![1220999883, 6742520, -36381884]], ![![1059360623, 5849927, -31565552]], ![![442759589, 2444976, -13192817]]]
  g := ![![![-692393, 735944, 148572], ![-6166863, 6554735, 1323316], ![-24380045, 25913528, 5231419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1220999883, -6742520, 36381884]] ![![767343, 735944, 148572]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2377801, -2280602, -460470]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-2377801, -2280602, -460470]] 
 ![![103, 0, 0], ![0, 103, 0], ![66, 82, 1]] where
  M :=![![![-2377801, -2280602, -460470], ![-21181620, -20314383, -4100734], ![-83726072, -80303288, -16213649]]]
  hmulB := by decide  
  f := ![![![658759225, 3637754, -19628914]], ![![-902930044, -4986097, 26904422]], ![![-286329010, -1581146, 8531687]]]
  g := ![![![271973, 344446, -460470], ![2422008, 3067435, -4100734], ![9576454, 12128310, -16213649]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [28, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 102], [0, 1]]
 g := ![![[82, 92], [89, 46], [70, 38], [50], [38], [73, 1]], ![[0, 11], [48, 57], [63, 65], [50], [38], [43, 102]]]
 h' := ![![[73, 102], [83, 68], [100, 47], [92, 48], [16, 87], [16, 48], [0, 1]], ![[0, 1], [0, 35], [29, 56], [94, 55], [84, 16], [18, 55], [73, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [18, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [28, 30, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![166, 406, 221]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, -172, 221]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-658759225, -3637754, 19628914]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-658759225, -3637754, 19628914]] 
 ![![103, 0, 0], ![43, 1, 0], ![84, 0, 1]] where
  M :=![![![-658759225, -3637754, 19628914], ![902930044, 4986097, -26904422], ![-1070266728, -5910152, 31890519]]]
  hmulB := by decide  
  f := ![![![2377801, 2280602, 460470]], ![![1198321, 1149323, 232048]], ![![2752052, 2639552, 532943]]]
  g := ![![![-20885093, -3637754, 19628914], ![28626207, 4986097, -26904422], ![-33931396, -5910152, 31890519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-2377801, -2280602, -460470]] ![![-658759225, -3637754, 19628914]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [53, 24, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 47, 18], [65, 59, 89], [0, 1]]
 g := ![![[99, 47, 48], [90, 64, 11], [59, 9], [9, 19, 29], [102, 83], [1]], ![[20, 78, 60, 71], [21, 44, 62, 60], [17, 81], [91, 27, 101, 20], [43, 30], [18, 44, 79, 54]], ![[84, 23, 1, 23], [23, 35, 68, 27], [36, 36], [15, 37, 37, 36], [77, 3], [44, 69, 19, 53]]]
 h' := ![![[103, 47, 18], [45, 6, 72], [23, 19, 15], [58, 46, 104], [78, 84, 52], [54, 83, 61], [0, 1]], ![[65, 59, 89], [86, 28, 76], [72, 100, 50], [63, 95, 9], [104, 79, 86], [52, 27, 64], [103, 47, 18]], ![[0, 1], [1, 73, 66], [53, 95, 42], [79, 73, 101], [41, 51, 76], [85, 104, 89], [65, 59, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 44], []]
 b := ![[], [44, 35, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [53, 24, 46, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30722696, 37525328, 12750227]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![287128, 350704, 119161]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3041, -2918, -590]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-3041, -2918, -590]] 
 ![![109, 0, 0], ![0, 109, 0], ![70, 60, 1]] where
  M :=![![![-3041, -2918, -590], ![-27140, -26019, -5246], ![-107088, -102752, -20773]]]
  hmulB := by decide  
  f := ![![![13355, 74, -398]], ![![-18308, -103, 546]], ![![-1302, -8, 39]]]
  g := ![![![351, 298, -590], ![3120, 2649, -5246], ![12358, 10492, -20773]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [20, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 108], [0, 1]]
 g := ![![[98, 60], [29], [38, 34], [10, 15], [38], [2, 1]], ![[0, 49], [29], [106, 75], [40, 94], [38], [4, 108]]]
 h' := ![![[2, 108], [83, 13], [3, 47], [18, 90], [77, 48], [69, 93], [0, 1]], ![[0, 1], [0, 96], [97, 62], [89, 19], [64, 61], [37, 16], [2, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [43, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [20, 107, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52, 356, 144]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -76, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13355, 74, -398]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![13355, 74, -398]] 
 ![![109, 0, 0], ![99, 1, 0], ![64, 0, 1]] where
  M :=![![![13355, 74, -398], ![-18308, -103, 546], ![21712, 128, -649]]]
  hmulB := by decide  
  f := ![![![-3041, -2918, -590]], ![![-3011, -2889, -584]], ![![-2768, -2656, -537]]]
  g := ![![![289, 74, -398], ![-395, -103, 546], ![464, 128, -649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-3041, -2918, -590]] ![![13355, 74, -398]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [11, 14, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 63, 1], [95, 49, 112], [0, 1]]
 g := ![![[80, 12, 31], [78, 72], [10, 56], [76, 77], [74, 48, 36], [1]], ![[13, 89, 61, 15], [98, 7], [41, 30], [66, 77], [94, 42, 34, 91], [30, 27, 82, 1]], ![[44, 96, 108, 28], [68, 1], [70, 50], [58, 82], [105, 74, 46, 16], [106, 44, 28, 112]]]
 h' := ![![[24, 63, 1], [33, 21, 12], [10, 67, 80], [32, 57, 13], [90, 26, 23], [102, 99, 6], [0, 1]], ![[95, 49, 112], [82, 48, 44], [16, 15, 32], [69, 91, 16], [2, 70, 23], [47, 6, 54], [24, 63, 1]], ![[0, 1], [93, 44, 57], [29, 31, 1], [102, 78, 84], [66, 17, 67], [8, 8, 53], [95, 49, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 23], []]
 b := ![[], [66, 54, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [11, 14, 107, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216395, 444768, 243176]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1915, 3936, 2152]
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



lemma PB116I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 115 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 115 (by omega)

def PB116I2 : PrimesBelowBoundCertificateInterval O 79 115 116 where
  m := 8
  g := ![2, 1, 2, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB116I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
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
      exact NI97N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I83N1, I97N1, I101N1, I103N1, I109N1]
  Il := ![[I83N1], [], [I97N1], [I101N1], [I103N1], [], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
