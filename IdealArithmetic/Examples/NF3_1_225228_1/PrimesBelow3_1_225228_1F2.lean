
import IdealArithmetic.Examples.NF3_1_225228_1.RI3_1_225228_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![348873941523264, 31278959816504, 30351864753609]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![348873941523264, 31278959816504, 30351864753609]] 
 ![![83, 0, 0], ![0, 83, 0], ![34, 56, 1]] where
  M :=![![![348873941523264, 31278959816504, 30351864753609], ![2854929476965036, 255964157136647, 248377488406242], ![4729128053088517, 423999011487631, 411431861156272]]]
  hmulB := by decide  
  f := ![![![-18808346, -272323, 1551915]], ![![142231534, -19815615, 1469892]], ![![89097533, -13197378, 1394290]]]
  g := ![![![-8229993495174, -20101511643200, 30351864753609], ![-67348254564424, -164496086670035, 248377488406242], ![-111560906340057, -272484159195947, 411431861156272]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [3, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 82], [0, 1]]
 g := ![![[75, 28], [7, 17], [78], [16], [68, 78], [1]], ![[0, 55], [0, 66], [78], [16], [31, 5], [1]]]
 h' := ![![[24, 82], [62, 32], [74, 73], [68, 24], [45, 79], [80, 24], [0, 1]], ![[0, 1], [0, 51], [0, 10], [63, 59], [32, 4], [75, 59], [24, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [23, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [3, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![494, 135, -171]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76, 117, -171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18808346, 272323, -1551915]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![18808346, 272323, -1551915]] 
 ![![83, 0, 0], ![77, 1, 0], ![20, 0, 1]] where
  M :=![![![18808346, 272323, -1551915], ![-142231534, 19815615, -1469892], ![-69613099, -23551048, 19352992]]]
  hmulB := by decide  
  f := ![![![-348873941523264, -31278959816504, -30351864753609]], ![![-358050879207908, -32101735698885, -31150253908845]], ![![-141043456428359, -12645520576117, -12270712725644]]]
  g := ![![![347925, 272323, -1551915], ![-19742603, 19815615, -1469892], ![16346479, -23551048, 19352992]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![348873941523264, 31278959816504, 30351864753609]] ![![18808346, 272323, -1551915]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13856574724, 4241656964, -1538430251]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-13856574724, 4241656964, -1538430251]] 
 ![![89, 0, 0], ![0, 89, 0], ![18, 19, 1]] where
  M :=![![![-13856574724, 4241656964, -1538430251], ![-133052269164, -20801458401, 22373081282], ![296388195377, -27318110729, -5373260796]]]
  hmulB := by decide  
  f := ![![![8123168232992263166, 728298168768571307, 706711720864234373]], ![![66474074657046704930, 5959860174590886179, 5783212454339896588]], ![![17071205541316572895, 1530551550553438935, 1485186653691501794]]]
  g := ![![![155451346, 376087997, -1538430251], ![-6019862160, -5010000031, 22373081282], ![4416931345, 840155555, -5373260796]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [9, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 88], [0, 1]]
 g := ![![[19, 10], [73], [71], [48, 4], [39, 49], [1]], ![[0, 79], [73], [71], [76, 85], [26, 40], [1]]]
 h' := ![![[7, 88], [57, 30], [64, 47], [13, 58], [5, 2], [80, 7], [0, 1]], ![[0, 1], [0, 59], [37, 42], [63, 31], [19, 87], [40, 82], [7, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [69, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [9, 82, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3224, 325, 612]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-160, -127, 612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8123168232992263166, -728298168768571307, -706711720864234373]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-8123168232992263166, -728298168768571307, -706711720864234373]] 
 ![![89, 0, 0], ![62, 1, 0], ![33, 0, 1]] where
  M :=![![![-8123168232992263166, -728298168768571307, -706711720864234373], ![-66474074657046704930, -5959860174590886179, -5783212454339896588], ![-110112846499426856997, -9872377644194944288, -9579764570529405780]]]
  hmulB := by decide  
  f := ![![![13856574724, -4241656964, 1538430251]], ![![11147864068, -2721137903, 820332520]], ![![1807626635, -1265804147, 630802911]]]
  g := ![![![678121404709875193, -728298168768571307, -706711720864234373], ![5549250192818031748, -5959860174590886179, -5783212454339896588], ![9192211216495843591, -9872377644194944288, -9579764570529405780]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-13856574724, 4241656964, -1538430251]] ![![-8123168232992263166, -728298168768571307, -706711720864234373]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![769559950550176560, 68996367755499579, 66951344766274075]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![769559950550176560, 68996367755499579, 66951344766274075]] 
 ![![97, 0, 0], ![30, 1, 0], ![22, 0, 1]] where
  M :=![![![769559950550176560, 68996367755499579, 66951344766274075], ![6297516454008214058, 564615870272903327, 547880896065545624], ![10431697864248679843, 935273803738611546, 907552686061175718]]]
  hmulB := by decide  
  f := ![![![-3702360918, -998552772, 875944771]], ![![-334855816, -335441065, 227205320]], ![![-1235939837, -80726151, 139910500]]]
  g := ![![![-28590316154359180, 68996367755499579, 66951344766274075], ![-233962261521864840, 564615870272903327, 547880896065545624], ![-387553354033562189, 935273803738611546, 907552686061175718]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-226546330, -6732581, 20777013]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-226546330, -6732581, 20777013]] 
 ![![97, 0, 0], ![80, 1, 0], ![92, 0, 1]] where
  M :=![![![-226546330, -6732581, 20777013], ![1898020034, -233858181, 1158540], ![648000341, 318387776, -240011492]]]
  hmulB := by decide  
  f := ![![![55759785964209012, 4999250150172236, 4851074502401613]], ![![50691548779979524, 4544847661600431, 4410140310288306]], ![![60677802754325497, 5440184342285543, 5278939592634040]]]
  g := ![![![-16488918, -6732581, 20777013], ![211341122, -233858181, 1158540], ![-28267675, 318387776, -240011492]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -1, 2]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-19, -1, 2]] 
 ![![97, 0, 0], ![84, 1, 0], ![81, 0, 1]] where
  M :=![![![-19, -1, 2], ![182, -19, -2], ![30, 31, -21]]]
  hmulB := by decide  
  f := ![![![-461, -41, -40]], ![![-438, -39, -38]], ![![-449, -40, -39]]]
  g := ![![![-1, -1, 2], ![20, -19, -2], ![-9, 31, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![769559950550176560, 68996367755499579, 66951344766274075]] ![![-226546330, -6732581, 20777013]]
  ![![461, 41, 40]] where
 M := ![![![461, 41, 40]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![461, 41, 40]] ![![-19, -1, 2]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9890, 975, 141]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-9890, 975, 141]] 
 ![![101, 0, 0], ![0, 101, 0], ![81, 37, 1]] where
  M :=![![![-9890, 975, 141], ![14922, -11981, 6132], ![98301, 1140, -7940]]]
  hmulB := by decide  
  f := ![![![872660, 78240, 75921]], ![![7141212, 640259, 621282]], ![![3433065, 307798, 298675]]]
  g := ![![![-211, -42, 141], ![-4770, -2365, 6132], ![7341, 2920, -7940]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [11, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 100], [0, 1]]
 g := ![![[77, 14], [65], [6, 84], [68], [25], [62, 1]], ![[36, 87], [65], [63, 17], [68], [25], [23, 100]]]
 h' := ![![[62, 100], [5, 32], [35, 41], [47, 65], [47, 88], [25, 96], [0, 1]], ![[0, 1], [70, 69], [52, 60], [37, 36], [49, 13], [18, 5], [62, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [9, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [11, 39, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1000322, 257749, 10897]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1165, -1440, 10897]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![872660, 78240, 75921]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![872660, 78240, 75921]] 
 ![![101, 0, 0], ![79, 1, 0], ![47, 0, 1]] where
  M :=![![![872660, 78240, 75921], ![7141212, 640259, 621282], ![11829261, 1060575, 1029140]]]
  hmulB := by decide  
  f := ![![![-9890, 975, 141]], ![![-7588, 644, 171]], ![![-3629, 465, -13]]]
  g := ![![![-87887, 78240, 75921], ![-719203, 640259, 621282], ![-1191344, 1060575, 1029140]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-9890, 975, 141]] ![![872660, 78240, 75921]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [87, 4, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 99, 91], [96, 3, 12], [0, 1]]
 g := ![![[52, 26, 18], [2, 40, 38], [81, 3, 8], [97, 30], [96, 1], [1]], ![[77, 69, 43, 79], [100, 39, 61, 81], [2, 95, 2, 55], [0, 93], [69, 26], [5, 53, 46, 23]], ![[41, 65, 102, 75], [99, 76, 96, 42], [81, 52, 69, 101], [77, 14], [82, 26], [63, 4, 37, 80]]]
 h' := ![![[8, 99, 91], [32, 9, 92], [60, 88, 48], [40, 2, 76], [41, 19, 37], [16, 99, 1], [0, 1]], ![[96, 3, 12], [8, 98, 65], [78, 9, 15], [17, 40, 101], [29, 7, 89], [77, 60, 51], [8, 99, 91]], ![[0, 1], [39, 99, 49], [0, 6, 40], [48, 61, 29], [19, 77, 80], [47, 47, 51], [96, 3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 78], []]
 b := ![[], [8, 85, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [87, 4, 102, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-685877, 63757, 23587]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6659, 619, 229]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8519, 395, 390]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-8519, 395, 390]] 
 ![![107, 0, 0], ![0, 107, 0], ![13, 60, 1]] where
  M :=![![![-8519, 395, 390], ![36670, -9699, 3150], ![60130, 5455, -7729]]]
  hmulB := by decide  
  f := ![![![-540003, -48415, -46980]], ![![-4418990, -396193, -384450]], ![![-2611957, -234180, -227239]]]
  g := ![![![-127, -215, 390], ![-40, -1857, 3150], ![1501, 4385, -7729]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [69, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 106], [0, 1]]
 g := ![![[95, 76], [64, 1], [64], [81, 86], [86], [79, 1]], ![[0, 31], [36, 106], [64], [27, 21], [86], [51, 106]]]
 h' := ![![[79, 106], [78, 41], [61, 106], [82, 99], [94, 73], [6, 73], [0, 1]], ![[0, 1], [0, 66], [89, 1], [92, 8], [83, 34], [102, 34], [79, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [5, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [69, 28, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![591, 135, -78]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 45, -78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![540003, 48415, 46980]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![540003, 48415, 46980]] 
 ![![107, 0, 0], ![66, 1, 0], ![81, 0, 1]] where
  M :=![![![540003, 48415, 46980], ![4418990, 396193, 384450], ![7319960, 656285, 636833]]]
  hmulB := by decide  
  f := ![![![8519, -395, -390]], ![![4912, -153, -270]], ![![5887, -350, -223]]]
  g := ![![![-60381, 48415, 46980], ![-494114, 396193, 384450], ![-818489, 656285, 636833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-8519, 395, 390]] ![![540003, 48415, 46980]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [56, 89, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 106, 38], [83, 2, 71], [0, 1]]
 g := ![![[91, 100, 22], [1, 7], [86, 101, 100], [49, 68, 48], [41, 1], [1]], ![[36, 35], [65, 105], [14, 1, 19, 20], [83, 56, 51, 104], [64, 1], [86, 100, 20, 45]], ![[103, 38, 103, 36], [104, 21], [32, 107, 42, 28], [65, 51, 100, 46], [], [81, 34, 8, 64]]]
 h' := ![![[27, 106, 38], [17, 56, 26], [89, 22, 94], [90, 49, 99], [77, 50, 22], [53, 20, 1], [0, 1]], ![[83, 2, 71], [91, 28], [104, 106, 43], [46, 4, 98], [9, 41, 91], [43, 23, 108], [27, 106, 38]], ![[0, 1], [84, 25, 83], [26, 90, 81], [100, 56, 21], [7, 18, 105], [15, 66], [83, 2, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 10], []]
 b := ![[], [71, 104, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [56, 89, 108, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6429692, 445047, 388476]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58988, 4083, 3564]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-570802298524042, -51176370699246, -49659524842143]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-570802298524042, -51176370699246, -49659524842143]] 
 ![![113, 0, 0], ![0, 113, 0], ![17, 39, 1]] where
  M :=![![![-570802298524042, -51176370699246, -49659524842143], ![-4671029026875648, -418790032283407, -406377273879762], ![-7737457119701355, -693716501932899, -673155039922534]]]
  hmulB := by decide  
  f := ![![![-22084100, -895161, 2169573]], ![![197810394, -22463351, -1031820]], ![![65390839, -7591590, -240997]]]
  g := ![![![2419554192853, 16686239806587, -49659524842143], ![19799863974162, 136547996894047, -406377273879762], ![32798040344971, 226188761549079, -673155039922534]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [47, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 112], [0, 1]]
 g := ![![[34, 8], [112], [91], [111], [92, 63], [97, 1]], ![[19, 105], [112], [91], [111], [101, 50], [81, 112]]]
 h' := ![![[97, 112], [69, 11], [94, 15], [90, 54], [83, 26], [74, 96], [0, 1]], ![[0, 1], [6, 102], [80, 98], [17, 59], [6, 87], [7, 17], [97, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [33, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [47, 16, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2104, 431, -44]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 19, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22084100, 895161, -2169573]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![22084100, 895161, -2169573]] 
 ![![113, 0, 0], ![103, 1, 0], ![18, 0, 1]] where
  M :=![![![22084100, 895161, -2169573], ![-197810394, 22463351, 1031820], ![-49989141, -33438756, 23874422]]]
  hmulB := by decide  
  f := ![![![570802298524042, 51176370699246, 49659524842143]], ![![561625360839398, 50353594816865, 48861135686907]], ![![159397331797647, 14291072340879, 13867491036116]]]
  g := ![![![-274913, 895161, -2169573], ![-22390339, 22463351, 1031820], ![26234187, -33438756, 23874422]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-570802298524042, -51176370699246, -49659524842143]] ![![22084100, 895161, -2169573]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8804, -3274, 1327]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![8804, -3274, 1327]] 
 ![![127, 0, 0], ![17, 1, 0], ![106, 0, 1]] where
  M :=![![![8804, -3274, 1327], ![115536, 14025, -16990], ![-220261, 23179, 2256]]]
  hmulB := by decide  
  f := ![![![425451610, 38144677, 37014085]], ![![84364272, 7563840, 7339651]], ![![400512127, 35908680, 34844362]]]
  g := ![![![-600, -3274, 1327], ![13213, 14025, -16990], ![-6720, 23179, 2256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-337426979, 86734921, -27468616]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-337426979, 86734921, -27468616]] 
 ![![127, 0, 0], ![41, 1, 0], ![9, 0, 1]] where
  M :=![![![-337426979, 86734921, -27468616], ![-2353642830, -483428205, 465472294], ![6304027156, -498764161, -163957137]]]
  hmulB := by decide  
  f := ![![![-311422402622504419, -27921170538152353, -27093598921064494]], ![![-120604503538085979, -10813027202278596, -10492533675863680]], ![![-55309124781870003, -4958845260796742, -4811867196758973]]]
  g := ![![![-28711348, 86734921, -27468616], ![104548527, -483428205, 465472294], ![222275370, -498764161, -163957137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107044418, -23202128, 6110097]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![107044418, -23202128, 6110097]] 
 ![![127, 0, 0], ![69, 1, 0], ![13, 0, 1]] where
  M :=![![![107044418, -23202128, 6110097], ![515724668, 147338577, -126992574], ![-1761879859, 114853583, 60640162]]]
  hmulB := by decide  
  f := ![![![23520187316422116, 2108747333592287, 2046244959685503]], ![![14294212250325802, 1281574911082046, 1243589575899405]], ![![4918016790116485, 440934192113307, 427865090232427]]]
  g := ![![![12823307, -23202128, 6110097], ![-62990029, 147338577, -126992574], ![-82481096, 114853583, 60640162]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![8804, -3274, 1327]] ![![-337426979, 86734921, -27468616]]
  ![![13100563538316, 1684498146007, -1983361106619]] where
 M := ![![![13100563538316, 1684498146007, -1983361106619]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![13100563538316, 1684498146007, -1983361106619]] ![![107044418, -23202128, 6110097]]
  ![![127, 0, 0]] where
 M := ![![![5765523433403100207485, -283565521774368290286, -254144380295758207644]]]
 hmul := by decide  
 g := ![![![![45397822310260631555, -2232799384050144018, -2001136852722505572]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24848, 3558, -3981]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![24848, 3558, -3981]] 
 ![![131, 0, 0], ![0, 131, 0], ![101, 15, 1]] where
  M :=![![![24848, 3558, -3981], ![-359136, 21713, 13386], ![84495, -63273, 31964]]]
  hmulB := by decide  
  f := ![![![-11763410, -1054671, -1023411]], ![![-96263154, -8630657, -8374848]], ![![-21309233, -1910520, -1853893]]]
  g := ![![![3259, 483, -3981], ![-13062, -1367, 13386], ![-23999, -4143, 31964]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [37, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 130], [0, 1]]
 g := ![![[79, 11], [123, 43], [15], [80], [36], [109], [1]], ![[21, 120], [63, 88], [15], [80], [36], [109], [1]]]
 h' := ![![[90, 130], [34, 81], [77, 82], [34, 43], [80, 92], [87, 6], [94, 90], [0, 1]], ![[0, 1], [119, 50], [121, 49], [105, 88], [107, 39], [103, 125], [72, 41], [90, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [38, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [37, 41, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1217, 505, 252]
  a := ![2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-185, -25, 252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11763410, -1054671, -1023411]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-11763410, -1054671, -1023411]] 
 ![![131, 0, 0], ![39, 1, 0], ![0, 0, 1]] where
  M :=![![![-11763410, -1054671, -1023411], ![-96263154, -8630657, -8374848], ![-159457803, -14296494, -13872752]]]
  hmulB := by decide  
  f := ![![![24848, 3558, -3981]], ![![4656, 1225, -1083]], ![![645, -483, 244]]]
  g := ![![![224189, -1054671, -1023411], ![1834599, -8630657, -8374848], ![3038973, -14296494, -13872752]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![24848, 3558, -3981]] ![![-11763410, -1054671, -1023411]]
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


lemma PB135I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 134 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 134 (by omega)

def PB135I2 : PrimesBelowBoundCertificateInterval O 79 134 135 where
  m := 10
  g := ![2, 2, 3, 2, 1, 2, 1, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB135I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
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
      exact NI97N2
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
      exact NI107N1
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I107N1, I113N1, I127N0, I127N1, I127N2, I131N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [], [I107N1], [], [I113N1], [I127N0, I127N1, I127N2], [I131N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
