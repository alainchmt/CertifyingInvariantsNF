
import IdealArithmetic.Examples.NF3_1_342171_1.RI3_1_342171_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [48, 80, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 58, 30], [71, 24, 53], [0, 1]]
 g := ![![[37, 12, 1], [12, 42, 63], [14, 30], [13, 31], [36, 38, 1], []], ![[64, 15, 69, 69], [33, 75, 1, 37], [64, 49], [1, 77], [62, 67, 22, 16], [81, 70]], ![[62, 58, 44, 32], [0, 46, 13, 32], [47, 26], [34, 12], [61, 36, 36, 8], [58, 70]]]
 h' := ![![[50, 58, 30], [5, 13, 82], [82, 66, 35], [16, 25, 14], [15, 27, 23], [0, 0, 1], [0, 1]], ![[71, 24, 53], [51, 63, 34], [37, 42, 81], [11, 2, 7], [68, 29, 34], [23, 27, 24], [50, 58, 30]], ![[0, 1], [82, 7, 50], [16, 58, 50], [23, 56, 62], [59, 27, 26], [16, 56, 58], [71, 24, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 23], []]
 b := ![[], [16, 9, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [48, 80, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-228250, 110390, -117362]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2750, 1330, -1414]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [85, 1, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 83, 59], [88, 5, 30], [0, 1]]
 g := ![![[47, 45, 44], [7, 57], [42, 73], [64, 84, 9], [80, 9, 1], []], ![[72, 83, 58, 14], [8, 34], [42, 81], [56, 62], [16, 49, 88, 51], [5, 10]], ![[47, 22, 27, 38], [27, 88], [57, 21], [49, 69, 2, 3], [80, 12, 37, 12], [34, 10]]]
 h' := ![![[10, 83, 59], [67, 78, 20], [22, 19, 71], [78, 55, 47], [53, 45, 3], [0, 0, 1], [0, 1]], ![[88, 5, 30], [43, 57, 74], [10, 81, 52], [38, 36, 9], [62, 9], [31, 4, 5], [10, 83, 59]], ![[0, 1], [59, 43, 84], [29, 78, 55], [54, 87, 33], [63, 35, 86], [48, 85, 83], [88, 5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 38], []]
 b := ![[], [49, 84, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [85, 1, 80, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10867879, -2306880, 586332]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![122111, -25920, 6588]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, -50, 68]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![65, -50, 68]] 
 ![![97, 0, 0], ![0, 97, 0], ![68, 82, 1]] where
  M :=![![![65, -50, 68], ![6496, -1005, -418], ![-7026, 1838, -905]]]
  hmulB := by decide  
  f := ![![![17297, 822, 920]], ![![90884, 4319, 4834]], ![![89474, 4252, 4759]]]
  g := ![![![-47, -58, 68], ![360, 343, -418], ![562, 784, -905]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 96], [0, 1]]
 g := ![![[66, 27], [49], [4], [8], [91], [73, 1]], ![[0, 70], [49], [4], [8], [91], [49, 96]]]
 h' := ![![[73, 96], [56, 67], [29, 90], [2, 95], [7, 69], [44, 73], [0, 1]], ![[0, 1], [0, 30], [3, 7], [50, 2], [0, 28], [38, 24], [73, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [60, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 24, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1214534, 262544, -569323]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![411634, 483990, -569323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17297, 822, 920]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![17297, 822, 920]] 
 ![![97, 0, 0], ![9, 1, 0], ![29, 0, 1]] where
  M :=![![![17297, 822, 920], ![90884, 4319, 4834], ![50294, 2390, 2675]]]
  hmulB := by decide  
  f := ![![![65, -50, 68]], ![![73, -15, 2]], ![![-53, 4, 11]]]
  g := ![![![-173, 822, 920], ![-909, 4319, 4834], ![-503, 2390, 2675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![65, -50, 68]] ![![17297, 822, 920]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [46, 85, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 12, 79], [90, 88, 22], [0, 1]]
 g := ![![[63, 22, 100], [9, 56], [49, 31, 82], [55, 31], [55, 97], [1]], ![[81, 52, 90, 9], [46, 71], [42, 14, 64, 80], [68, 65], [73, 36], [57, 76, 0, 58]], ![[97, 2, 95, 9], [51, 85], [19, 35, 11, 13], [28, 4], [87, 95], [22, 59, 63, 43]]]
 h' := ![![[31, 12, 79], [4, 93, 10], [69, 0, 64], [95, 39, 48], [91, 97, 58], [55, 16, 20], [0, 1]], ![[90, 88, 22], [36, 58, 46], [43, 16, 77], [22, 76, 33], [76, 17, 41], [0, 96, 95], [31, 12, 79]], ![[0, 1], [92, 51, 45], [69, 85, 61], [70, 87, 20], [34, 88, 2], [81, 90, 87], [90, 88, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 8], []]
 b := ![[], [10, 45, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [46, 85, 81, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10913454, 2898296, -1461066]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108054, 28696, -14466]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25575, -5288, 760]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![25575, -5288, 760]] 
 ![![103, 0, 0], ![26, 1, 0], ![3, 0, 1]] where
  M :=![![![25575, -5288, 760], ![63144, 8887, -37776], ![-537256, 91480, 19463]]]
  hmulB := by decide  
  f := ![![![3628716161, 172445144, 193005368]], ![![1101097390, 52326743, 58565536]], ![![208127725, 9890720, 11069967]]]
  g := ![![![1561, -5288, 760], ![-530, 8887, -37776], ![-28875, 91480, 19463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40555278, 261341611, -486210469]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![40555278, 261341611, -486210469]] 
 ![![103, 0, 0], ![87, 1, 0], ![69, 0, 1]] where
  M :=![![![40555278, 261341611, -486210469], ![-46639732271, 7595053924, 2315601746], ![40908871275, -11699491669, 7072370702]]]
  hmulB := by decide  
  f := ![![![-80806400188256588722, -3840110578596201839, -4297957821202383162]], ![![-72376106273710163002, -3439483143560064108, -3849564530811440435]], ![![-56413569794515145039, -2680905790130417766, -3000543805384359977]]]
  g := ![![![105362694, 261341611, -486210469], ![-8419281011, 7595053924, 2315601746], ![5541466680, -11699491669, 7072370702]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![323552403372, -5292662635, -101712351676]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![323552403372, -5292662635, -101712351676]] 
 ![![103, 0, 0], ![93, 1, 0], ![61, 0, 1]] where
  M :=![![![323552403372, -5292662635, -101712351676], ![-9876683437842, 1843945015877, 64663713231], ![2741406978037, -1548007687291, 1854530341147]]]
  hmulB := by decide  
  f := ![![![-3519751904521051888638140, -167266905728956157692061, -187209740707230758736167]], ![![-3357580638645797296661547, -159560144975091935249023, -178584121215222552500697]], ![![-2183874216785063380810671, -103782849658715295083626, -116156631760434083813687]]]
  g := ![![![68157509521, -5292662635, -101712351676], ![-1799107343898, 1843945015877, 64663713231], ![326017195011, -1548007687291, 1854530341147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![25575, -5288, 760]] ![![40555278, 261341611, -486210469]]
  ![![278758847652898, -42370447117227, -19304733044003]] where
 M := ![![![278758847652898, -42370447117227, -19304733044003]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![278758847652898, -42370447117227, -19304733044003]] ![![323552403372, -5292662635, -101712351676]]
  ![![103, 0, 0]] where
 M := ![![![455750458540009293507114079, -49720276166221649522413436, -66894261544972333276978926]]]
 hmul := by decide  
 g := ![![![![4424761733398148480651593, -482721127827394655557412, -649458849951187701718242]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3348, -159, -178]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-3348, -159, -178]] 
 ![![107, 0, 0], ![0, 107, 0], ![14, 58, 1]] where
  M :=![![![-3348, -159, -178], ![-17584, -837, -935], ![-9727, -463, -519]]]
  hmulB := by decide  
  f := ![![![-14, 1, 3]], ![![293, -58, 4]], ![![157, -31, 2]]]
  g := ![![![-8, 95, -178], ![-42, 499, -935], ![-23, 277, -519]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [71, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 106], [0, 1]]
 g := ![![[97, 47], [70, 62], [44], [37, 37], [57], [68, 1]], ![[83, 60], [6, 45], [44], [92, 70], [57], [29, 106]]]
 h' := ![![[68, 106], [59, 49], [36, 94], [48, 30], [81, 95], [94, 59], [0, 1]], ![[0, 1], [74, 58], [8, 13], [55, 77], [14, 12], [40, 48], [68, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [101, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [71, 39, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1153, 298, -980]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, 534, -980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 1, 3]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-14, 1, 3]] 
 ![![107, 0, 0], ![23, 1, 0], ![59, 0, 1]] where
  M :=![![![-14, 1, 3], ![293, -58, 4], ![1, 33, -60]]]
  hmulB := by decide  
  f := ![![![-3348, -159, -178]], ![![-884, -42, -47]], ![![-1937, -92, -103]]]
  g := ![![![-2, 1, 3], ![13, -58, 4], ![26, 33, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-3348, -159, -178]] ![![-14, 1, 3]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [17, 47, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 69, 12], [101, 39, 97], [0, 1]]
 g := ![![[100, 19, 94], [39, 12], [98, 81, 25], [3, 84, 60], [108, 97], [1]], ![[68, 39, 104, 108], [16, 105], [51, 32, 4, 108], [89, 14, 93, 1], [0, 43], [4, 36, 20, 93]], ![[88, 57, 61, 106], [1, 43], [4, 63, 68, 61], [48, 97, 79, 83], [12, 16], [13, 83, 93, 16]]]
 h' := ![![[44, 69, 12], [80, 2, 58], [78, 106, 11], [58, 71, 104], [88, 105, 96], [92, 62, 36], [0, 1]], ![[101, 39, 97], [103, 96, 106], [22, 97, 66], [36, 54, 3], [60, 98, 99], [96, 31, 77], [44, 69, 12]], ![[0, 1], [85, 11, 54], [59, 15, 32], [5, 93, 2], [42, 15, 23], [30, 16, 105], [101, 39, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 82], []]
 b := ![[], [46, 7, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [17, 47, 73, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![845077, 836902, -298006]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7753, 7678, -2734]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [88, 24, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 46, 36], [88, 66, 77], [0, 1]]
 g := ![![[94, 46, 53], [30, 106], [7, 95], [86, 105], [108, 79, 44], [1]], ![[20, 2, 90, 81], [105, 13], [48, 56], [74, 81], [17, 70, 94, 100], [15, 99, 28, 100]], ![[56, 60, 45, 91], [99, 44], [24, 32], [30, 41], [88, 7, 64, 14], [36, 27, 39, 13]]]
 h' := ![![[90, 46, 36], [19, 99, 77], [88, 66, 85], [34, 30, 78], [101, 8, 52], [25, 89, 65], [0, 1]], ![[88, 66, 77], [76, 50, 58], [84, 10, 76], [50, 27, 13], [11, 31, 104], [73, 85, 36], [90, 46, 36]], ![[0, 1], [100, 77, 91], [87, 37, 65], [74, 56, 22], [51, 74, 70], [78, 52, 12], [88, 66, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 9], []]
 b := ![[], [29, 12, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [88, 24, 48, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2654370, 613590, -190857]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23490, 5430, -1689]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [72, 40, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 112, 114], [14, 14, 13], [0, 1]]
 g := ![![[87, 80, 35], [16, 52, 117], [95, 112, 13], [56, 73, 16], [123, 3, 94], [1]], ![[17, 122, 63, 86], [42, 86, 36, 51], [81, 16, 111, 116], [27, 53, 38, 91], [90, 126, 64, 123], [72, 112, 25, 89]], ![[51, 114, 118, 31], [76, 30, 107, 1], [92, 106, 108, 71], [101, 56, 36, 98], [73, 8, 94, 94], [33, 27, 103, 38]]]
 h' := ![![[86, 112, 114], [118, 4, 17], [18, 82, 25], [32, 10, 93], [34, 48, 123], [55, 87, 100], [0, 1]], ![[14, 14, 13], [22, 1, 59], [58, 55, 46], [121, 109, 29], [82, 65, 82], [63, 25, 15], [86, 112, 114]], ![[0, 1], [90, 122, 51], [19, 117, 56], [86, 8, 5], [31, 14, 49], [114, 15, 12], [14, 14, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 111], []]
 b := ![[], [95, 42, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [72, 40, 27, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3110611, -840105, 559181]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24493, -6615, 4403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [114, 105, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 118, 105], [2, 12, 26], [0, 1]]
 g := ![![[64, 109, 21], [32, 0, 43], [32, 75], [21, 45], [95, 102], [42, 1], []], ![[72, 45, 10, 123], [67, 34, 39, 38], [130, 21], [108, 109], [117, 62], [46, 13], [117, 21]], ![[8, 60, 47, 23], [104, 66, 120, 76], [126, 41], [4, 48], [126, 45], [50, 38], [65, 21]]]
 h' := ![![[40, 118, 105], [20, 98, 105], [24, 19, 49], [2, 2, 72], [118, 5, 62], [59, 61, 87], [0, 0, 1], [0, 1]], ![[2, 12, 26], [99, 10, 22], [57, 64, 94], [27, 46, 26], [5, 128, 90], [80, 80, 113], [52, 1, 12], [40, 118, 105]], ![[0, 1], [71, 23, 4], [38, 48, 119], [75, 83, 33], [111, 129, 110], [117, 121, 62], [61, 130, 118], [2, 12, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 76], []]
 b := ![[], [128, 22, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [114, 105, 89, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1448336, 923550, -1146250]
  a := ![-5, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11056, 7050, -8750]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120, -19, -7]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![120, -19, -7]] 
 ![![137, 0, 0], ![0, 137, 0], ![22, 81, 1]] where
  M :=![![![120, -19, -7], ![-717, 206, -126], ![-1619, 173, 244]]]
  hmulB := by decide  
  f := ![![![-526, -25, -28]], ![![-2766, -131, -147]], ![![-1731, -82, -92]]]
  g := ![![![2, 4, -7], ![15, 76, -126], ![-51, -143, 244]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [100, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 136], [0, 1]]
 g := ![![[127, 37], [122], [17], [131, 123], [78], [37], [1]], ![[0, 100], [122], [17], [105, 14], [78], [37], [1]]]
 h' := ![![[41, 136], [100, 41], [45, 56], [52, 90], [13, 64], [135, 30], [37, 41], [0, 1]], ![[0, 1], [0, 96], [12, 81], [43, 47], [34, 73], [132, 107], [74, 96], [41, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [135, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [100, 96, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35296, 9388, -3348]
  a := ![6, -6, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![280, 2048, -3348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![526, 25, 28]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![526, 25, 28]] 
 ![![137, 0, 0], ![119, 1, 0], ![74, 0, 1]] where
  M :=![![![526, 25, 28], ![2766, 131, 147], ![1529, 73, 81]]]
  hmulB := by decide  
  f := ![![![-120, 19, 7]], ![![-99, 15, 7]], ![![-53, 9, 2]]]
  g := ![![![-33, 25, 28], ![-173, 131, 147], ![-96, 73, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![120, -19, -7]] ![![526, 25, 28]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB166I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB166I2 : PrimesBelowBoundCertificateInterval O 79 137 166 where
  m := 11
  g := ![1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB166I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
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
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I97N1, I103N0, I103N1, I103N2, I107N1, I137N1]
  Il := ![[], [], [I97N1], [], [I103N0, I103N1, I103N2], [I107N1], [], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
