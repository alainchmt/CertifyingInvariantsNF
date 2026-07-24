
import IdealArithmetic.Examples.NF3_1_482727_1.RI3_1_482727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [25, 5, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 13, 24], [36, 23, 13], [0, 1]]
 g := ![![[28, 12, 10], [27, 33], [21, 35, 1], [2, 1], []], ![[31, 0, 9, 19], [22, 3], [13, 22, 35, 15], [32, 11], [0, 21]], ![[4, 9, 33, 6], [6, 26], [15, 15, 23, 14], [9, 21], [11, 21]]]
 h' := ![![[3, 13, 24], [3, 34, 26], [30, 3, 12], [24, 2, 36], [0, 0, 1], [0, 1]], ![[36, 23, 13], [6, 31, 8], [36, 3, 15], [21, 29, 25], [9, 34, 23], [3, 13, 24]], ![[0, 1], [23, 9, 3], [32, 31, 10], [0, 6, 13], [22, 3, 13], [36, 23, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 8], []]
 b := ![[], [19, 14, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [25, 5, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2745030, -821437, -523032]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74190, -22201, -14136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![464056323837341827895784, -17840678459641053679576, 23174628571950927158791]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![464056323837341827895784, -17840678459641053679576, 23174628571950927158791]] 
 ![![41, 0, 0], ![0, 41, 0], ![23, 28, 1]] where
  M :=![![![464056323837341827895784, -17840678459641053679576, 23174628571950927158791], ![-2287115450388120481999163, 87928316573817119875913, -114216848992867628798602], ![1153018924409120461191028, -44327894765365994829073, 57580909766844885995976]]]
  hmulB := by decide  
  f := ![![![229005023662, 50311098913, 7628723209]], ![![-921434340848, 49005630196, 468057336635]], ![![-629952957063, 38038863191, 328991066091]]]
  g := ![![![-1681954471159256018449, -16261714109128463759164, 23174628571950927158791], ![8289562840191097082163, 80146343618880749420409, -114216848992867628798602], ![-4179073176300290651620, -40404716298463970797961, 57580909766844885995976]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[34, 21], [31], [10], [23, 32], [1]], ![[0, 20], [31], [10], [20, 9], [1]]]
 h' := ![![[14, 40], [4, 29], [5, 21], [36, 16], [39, 14], [0, 1]], ![[0, 1], [0, 12], [12, 20], [14, 25], [30, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [4, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![755, -4008, -6299]
  a := ![-7, -3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3552, 4204, -6299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229005023662, -50311098913, -7628723209]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-229005023662, -50311098913, -7628723209]] 
 ![![41, 0, 0], ![33, 1, 0], ![19, 0, 1]] where
  M :=![![![-229005023662, -50311098913, -7628723209], ![921434340848, -49005630196, -468057336635], ![5295025240065, 969719529656, -207567650144]]]
  hmulB := by decide  
  f := ![![![-464056323837341827895784, 17840678459641053679576, -23174628571950927158791]], ![![-317725444786442922891749, 12214977380349698818295, -15866973021500316279061]], ![![-243172904324844272956364, 9348799646306000359537, -12143874454485670780805]]]
  g := ![![![38444072718, -50311098913, -7628723209], ![278822183741, -49005630196, -468057336635], ![-555169119167, 969719529656, -207567650144]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![464056323837341827895784, -17840678459641053679576, 23174628571950927158791]] ![![-229005023662, -50311098913, -7628723209]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-412, -72, 23]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-412, -72, 23]] 
 ![![43, 0, 0], ![0, 43, 0], ![12, 38, 1]] where
  M :=![![![-412, -72, 23], ![-2107, -731, -602], ![6628, 879, -924]]]
  hmulB := by decide  
  f := ![![![28014, -1077, 1399]], ![![-138068, 5308, -6895]], ![![-112577, 4328, -5622]]]
  g := ![![![-16, -22, 23], ![119, 515, -602], ![412, 837, -924]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 42], [0, 1]]
 g := ![![[12, 1], [30, 9], [17], [23, 4], [1]], ![[14, 42], [5, 34], [17], [31, 39], [1]]]
 h' := ![![[2, 42], [5, 1], [2, 3], [11, 24], [36, 2], [0, 1]], ![[0, 1], [7, 42], [8, 40], [16, 19], [40, 41], [2, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [25, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 41, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122970, -71076, -81821]
  a := ![2, 1, -70]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19974, 70654, -81821]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28014, -1077, 1399]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![28014, -1077, 1399]] 
 ![![43, 0, 0], ![0, 1, 0], ![14, 0, 1]] where
  M :=![![![28014, -1077, 1399], ![-138068, 5308, -6895], ![69605, -2676, 3476]]]
  hmulB := by decide  
  f := ![![![-412, -72, 23]], ![![-49, -17, -14]], ![![20, -3, -14]]]
  g := ![![![196, -1077, 1399], ![-966, 5308, -6895], ![487, -2676, 3476]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-412, -72, 23]] ![![28014, -1077, 1399]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5704400925802224080, 219306100346965971, -284873550666872399]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-5704400925802224080, 219306100346965971, -284873550666872399]] 
 ![![47, 0, 0], ![0, 47, 0], ![29, 1, 1]] where
  M :=![![![-5704400925802224080, 219306100346965971, -284873550666872399], ![28114310316313214386, -1080856664812359268, 1404007801788948941], ![-14173456716371135899, 544899554104664478, -707811914438333754]]]
  hmulB := by decide  
  f := ![![![543389058, 147984204, 74841643]], ![![-8002958555, -876903077, 1481541122]], ![![-197588223, -4759942, 70081701]]]
  g := ![![![54402809436959053, 10727226617315710, -284873550666872399], ![-268125870969495849, -52869456736198047, 1404007801788948941], ![135172102177458361, 26653435500914856, -707811914438333754]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [10, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[32, 1], [20, 37], [27, 1], [32, 34], [1]], ![[41, 46], [24, 10], [36, 46], [9, 13], [1]]]
 h' := ![![[9, 46], [35, 1], [12, 32], [9, 1], [37, 9], [0, 1]], ![[0, 1], [44, 46], [18, 15], [18, 46], [24, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [22, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [10, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-523, -5436, -9901]
  a := ![8, 3, -23]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6098, 95, -9901]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-543389058, -147984204, -74841643]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-543389058, -147984204, -74841643]] 
 ![![47, 0, 0], ![36, 1, 0], ![32, 0, 1]] where
  M :=![![![-543389058, -147984204, -74841643], ![8002958555, 876903077, -1481541122], ![17041970608, 3638356113, 358108822]]]
  hmulB := by decide  
  f := ![![![5704400925802224080, -219306100346965971, 284873550666872399]], ![![3771151553458869202, -144982190376136504, 188328511111031009]], ![![4185410347703027797, -160908399259735650, 209016287995281926]]]
  g := ![![![152744146, -147984204, -74841643], ![507314121, 876903077, -1481541122], ![-2668049612, 3638356113, 358108822]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-5704400925802224080, 219306100346965971, -284873550666872399]] ![![-543389058, -147984204, -74841643]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2314459, 319117, -298505]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![2314459, 319117, -298505]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 29, 1]] where
  M :=![![![2314459, 319117, -298505], ![29191654, 7069927, 2275043], ![-23872677, -947414, 7728773]]]
  hmulB := by decide  
  f := ![![![-1071646575441, 41199529007, -53517235022]], ![![5281642150201, -203053109074, 263761291019]], ![![2010706470069, -77301753616, 100413189558]]]
  g := ![![![274588, 169354, -298505], ![-1209153, -1111440, 2275043], ![-6429290, -4246827, 7728773]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52], [0, 1]]
 g := ![![[16, 46], [4], [26, 15], [40], [25, 1]], ![[0, 7], [4], [30, 38], [40], [50, 52]]]
 h' := ![![[25, 52], [36, 24], [34, 2], [52, 42], [49, 27], [0, 1]], ![[0, 1], [0, 29], [31, 51], [42, 11], [35, 26], [25, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [31, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 28, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1468, -1717, -2775]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2119, 1486, -2775]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1071646575441, 41199529007, -53517235022]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1071646575441, 41199529007, -53517235022]] 
 ![![53, 0, 0], ![2, 1, 0], ![23, 0, 1]] where
  M :=![![![-1071646575441, 41199529007, -53517235022], ![5281642150201, -203053109074, 263761291019], ![-2662669849091, 102366532211, -132971757075]]]
  hmulB := by decide  
  f := ![![![2314459, 319117, -298505]], ![![638124, 145437, 31661]], ![![553960, 120609, 16286]]]
  g := ![![![1450014567, 41199529007, -53517235022], ![-7146440096, -203053109074, 263761291019], ![3602783004, 102366532211, -132971757075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![2314459, 319117, -298505]] ![![-1071646575441, 41199529007, -53517235022]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-489826231226552517, 18831404386752405, -24461558630656174]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-489826231226552517, 18831404386752405, -24461558630656174]] 
 ![![59, 0, 0], ![0, 59, 0], ![55, 35, 1]] where
  M :=![![![-489826231226552517, 18831404386752405, -24461558630656174], ![2414123208536016359, -92811138892149964, 120559522219459297], ![-1217048201403620033, 46789504885051725, -60778484362548923]]]
  hmulB := by decide  
  f := ![![![148719467, 13223565, -33625111]], ![![3356465516, 707122789, 51761863]], ![![2123081132, 436545250, 11448347]]]
  g := ![![![14501008363720967, 14830270448469805, -24461558630656174], ![-71468652771766864, -73091430789376701, 120559522219459297], ![36029973534518148, 36848075552106170, -60778484362548923]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [14, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 58], [0, 1]]
 g := ![![[28, 21], [0, 46], [15], [14, 19], [21, 1]], ![[56, 38], [22, 13], [15], [0, 40], [42, 58]]]
 h' := ![![[21, 58], [0, 32], [33, 39], [40, 29], [1, 14], [0, 1]], ![[0, 1], [23, 27], [26, 20], [0, 30], [0, 45], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [14, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [14, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112499, -65052, -72485]
  a := ![-22, -1, 67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65664, 41897, -72485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-148719467, -13223565, 33625111]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-148719467, -13223565, 33625111]] 
 ![![59, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![-148719467, -13223565, 33625111], ![-3356465516, -707122789, -51761863], ![394076957, -279576060, -713168373]]]
  hmulB := by decide  
  f := ![![![489826231226552517, -18831404386752405, 24461558630656174]], ![![266261819438075030, -10236454634198119, 13296917747708799]], ![![95347191227840554, -3665629565522430, 4761568000651771]]]
  g := ![![![642821, -13223565, 33625111], ![394456516, -707122789, -51761863], ![290795026, -279576060, -713168373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-489826231226552517, 18831404386752405, -24461558630656174]] ![![-148719467, -13223565, 33625111]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [14, 9, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 27, 59], [58, 33, 2], [0, 1]]
 g := ![![[54, 21, 41], [12, 14], [57, 33, 20], [12, 18, 58], [1]], ![[15, 4, 26, 30], [41, 13], [14, 49, 58, 30], [27, 13, 7, 10], [24, 45, 52, 53]], ![[15, 50, 53, 37], [14, 49], [60, 6, 34, 53], [0, 27, 43, 23], [7, 41, 58, 8]]]
 h' := ![![[37, 27, 59], [40, 59, 23], [56, 43, 40], [15, 19, 52], [47, 52, 34], [0, 1]], ![[58, 33, 2], [50, 20, 31], [40, 14, 14], [38, 4, 31], [53, 60, 42], [37, 27, 59]], ![[0, 1], [28, 43, 7], [23, 4, 7], [34, 38, 39], [58, 10, 46], [58, 33, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 48], []]
 b := ![[], [39, 24, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [14, 9, 27, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7198, 976, -549]
  a := ![0, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![118, 16, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29539747384, -5962837897, 61063955]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-29539747384, -5962837897, 61063955]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 11, 1]] where
  M :=![![![-29539747384, -5962837897, 61063955], ![11721054236, -24614996722, -53543413163], ![600536836857, 100452284924, -42442446458]]]
  hmulB := by decide  
  f := ![![![95869833959559083064, -3685722602610589618, 4787668390973468563]], ![![-472497339680488556009, 18165193915620707111, -23596166641548369436]], ![![-74018917441327786335, 2845662558979190646, -3696449829227905328]]]
  g := ![![![-440891752, -99023006, 61063955], ![174941108, 8423321613, -53543413163], ![8963236371, 8467450686, -42442446458]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [17, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 66], [0, 1]]
 g := ![![[53, 4], [28, 59], [16], [55], [29], [1]], ![[0, 63], [0, 8], [16], [55], [29], [1]]]
 h' := ![![[37, 66], [60, 2], [6, 27], [12, 63], [64, 16], [50, 37], [0, 1]], ![[0, 1], [0, 65], [0, 40], [65, 4], [53, 51], [12, 30], [37, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [42, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [17, 30, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4020, -5223, -6852]
  a := ![-7, -2, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, 1047, -6852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95869833959559083064, 3685722602610589618, -4787668390973468563]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-95869833959559083064, 3685722602610589618, -4787668390973468563]] 
 ![![67, 0, 0], ![33, 1, 0], ![61, 0, 1]] where
  M :=![![![-95869833959559083064, 3685722602610589618, -4787668390973468563], ![472497339680488556009, -18165193915620707111, 23596166641548369436], ![-238203267916412431654, 9157741620222004939, -11895694498762406820]]]
  hmulB := by decide  
  f := ![![![29539747384, 5962837897, -61063955]], ![![14374486708, 3304308169, 769079144]], ![![17931160501, 3929564579, 577873809]]]
  g := ![![![1112673014980194655, 3685722602610589618, -4787668390973468563], ![-5483842182663860372, -18165193915620707111, 23596166641548369436], ![2764606314041316737, 9157741620222004939, -11895694498762406820]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-29539747384, -5962837897, 61063955]] ![![-95869833959559083064, 3685722602610589618, -4787668390973468563]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [16, 14, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 20, 29], [18, 50, 42], [0, 1]]
 g := ![![[13, 63, 10], [16, 2, 5], [40, 5, 10], [41, 40], [23, 1], []], ![[65, 33, 31, 25], [29, 22, 34, 36], [32, 24, 18, 32], [34, 19], [66, 15], [55, 60]], ![[6, 17, 57, 17], [24, 17, 69, 51], [24, 4, 21, 11], [50, 10], [39, 45], [42, 60]]]
 h' := ![![[5, 20, 29], [28, 29, 62], [70, 28, 17], [10, 48, 62], [58, 17, 18], [0, 0, 1], [0, 1]], ![[18, 50, 42], [58, 8, 36], [17, 39, 29], [64, 33, 19], [18, 64, 44], [68, 32, 50], [5, 20, 29]], ![[0, 1], [61, 34, 44], [54, 4, 25], [30, 61, 61], [64, 61, 9], [7, 39, 20], [18, 50, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 14], []]
 b := ![[], [22, 38, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [16, 14, 48, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-278959, -79875, -44020]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3929, -1125, -620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12746925425564764499, 490056456910251810, -636571999987149320]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-12746925425564764499, 490056456910251810, -636571999987149320]] 
 ![![73, 0, 0], ![0, 73, 0], ![47, 71, 1]] where
  M :=![![![-12746925425564764499, 490056456910251810, -636571999987149320], ![62823602627971325890, -2415257882693477869, 3137364112217967650], ![-31671686148295251850, 1217620232332959030, -1581660511949871759]]]
  hmulB := by decide  
  f := ![![![-1136153727, -162264030, 135403460]], ![![-13188957370, -3275748517, -1189569350]], ![![-13386545593, -3280508459, -1119487649]]]
  g := ![![![235232309230565117, 625844773369833610, -636571999987149320], ![-1159349460907851420, -3084494655481769603, 3137364112217967650], ![584470656347242751, 1555007076448956903, -1581660511949871759]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 72], [0, 1]]
 g := ![![[40, 4], [16], [35], [23, 72], [27], [1]], ![[0, 69], [16], [35], [33, 1], [27], [1]]]
 h' := ![![[63, 72], [53, 71], [38, 4], [49, 20], [7, 27], [18, 63], [0, 1]], ![[0, 1], [0, 2], [71, 69], [68, 53], [29, 46], [45, 10], [63, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [67, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 10, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6741, -2220, -1664]
  a := ![4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![979, 1588, -1664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1136153727, -162264030, 135403460]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1136153727, -162264030, 135403460]] 
 ![![73, 0, 0], ![16, 1, 0], ![46, 0, 1]] where
  M :=![![![-1136153727, -162264030, 135403460], ![-13188957370, -3275748517, -1189569350], ![12597370150, 727436610, -3627137147]]]
  hmulB := by decide  
  f := ![![![-12746925425564764499, 490056456910251810, -636571999987149320]], ![![-1933249372343354878, 74323909970829467, -96545039555841390]], ![![-8466167886633896148, 325482428084993730, -422794143991215623]]]
  g := ![![![-65321759, -162264030, 135403460], ![1286893274, -3275748517, -1189569350], ![2298721824, 727436610, -3627137147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-12746925425564764499, 490056456910251810, -636571999987149320]] ![![-1136153727, -162264030, 135403460]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-124253668992080921063, 4776941164356152853, -6205136057154406031]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-124253668992080921063, 4776941164356152853, -6205136057154406031]] 
 ![![79, 0, 0], ![19, 1, 0], ![67, 0, 1]] where
  M :=![![![-124253668992080921063, 4776941164356152853, -6205136057154406031], ![612387918279526550572, -23543297184812171389, 30582198364896563615], ![-308727247999648069285, 11869041063261491964, -15417609748898118861]]]
  hmulB := by decide  
  f := ![![![-17288178069, -5378625549, -3710996536]], ![![790773968, -645778441, -1599222243]], ![![-6470365154, -2699573790, -2750712057]]]
  g := ![![![2540867907778447833, 4776941164356152853, -6205136057154406031], ![-12522743362748252598, -23543297184812171389, 30582198364896563615], ![6313174999677943634, 11869041063261491964, -15417609748898118861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![385632, 70953, -14464]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![385632, 70953, -14464]] 
 ![![79, 0, 0], ![25, 1, 0], ![12, 0, 1]] where
  M :=![![![385632, 70953, -14464], ![1248005, 560567, 609649], ![-6761261, -989241, 758962]]]
  hmulB := by decide  
  f := ![![![-1028538837863, 39542248962, -51364466585]], ![![-261320083144, 10046469230, -13050131103]], ![![-188582634622, 7250072835, -9417676881]]]
  g := ![![![-15375, 70953, -14464], ![-254202, 560567, 609649], ![112180, -989241, 758962]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30488, 6366, 357]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![30488, 6366, 357]] 
 ![![79, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![30488, 6366, 357], ![-55155, 18053, 58008], ![-652962, -113577, 37508]]]
  hmulB := by decide  
  f := ![![![-7265506540, 279322917, -362834007]], ![![-2673657676, 102788960, -133520481]], ![![-3263468079, 125464263, -162975175]]]
  g := ![![![-2503, 6366, 357], ![-32699, 18053, 58008], ![24948, -113577, 37508]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-124253668992080921063, 4776941164356152853, -6205136057154406031]] ![![385632, 70953, -14464]]
  ![![7265506540, -279322917, 362834007]] where
 M := ![![![7265506540, -279322917, 362834007]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![7265506540, -279322917, 362834007]] ![![30488, 6366, 357]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB197I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB197I1 : PrimesBelowBoundCertificateInterval O 31 79 197 where
  m := 11
  g := ![1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB197I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N1, I53N1, I59N1, I67N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [I59N1], [], [I67N1], [], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
