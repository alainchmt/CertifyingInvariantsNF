
import IdealArithmetic.Examples.NF3_1_383075_1.RI3_1_383075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165431969063, 4193759886, -6767510753]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-165431969063, 4193759886, -6767510753]] 
 ![![83, 0, 0], ![0, 83, 0], ![36, 11, 1]] where
  M :=![![![-165431969063, 4193759886, -6767510753], ![284235451626, -7205470877, 11627537810], ![-34020189399, 862424031, -1391701972]]]
  hmulB := by decide  
  f := ![![![-52498, -31203, -5413]], ![![227346, 108617, -198044]], ![![24519, 10862, -28479]]]
  g := ![![![942149615, 947426243, -6767510753], ![-1618745898, -1627811889, 11627537810], ![193747971, 194833081, -1391701972]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [23, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[79, 65], [25, 28], [69], [49], [66, 81], [1]], ![[0, 18], [28, 55], [69], [49], [48, 2], [1]]]
 h' := ![![[9, 82], [6, 27], [60, 32], [30, 22], [59, 7], [60, 9], [0, 1]], ![[0, 1], [0, 56], [16, 51], [62, 61], [39, 76], [58, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [52, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [23, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-418, -326, -1667]
  a := ![0, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![718, 217, -1667]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52498, -31203, -5413]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-52498, -31203, -5413]] 
 ![![83, 0, 0], ![15, 1, 0], ![48, 0, 1]] where
  M :=![![![-52498, -31203, -5413], ![227346, 108617, -198044], ![1424199, 830067, 9595]]]
  hmulB := by decide  
  f := ![![![-165431969063, 4193759886, -6767510753]], ![![-26472820293, 671095511, -1082953295]], ![![-96081381981, 2435697573, -3930508652]]]
  g := ![![![8137, -31203, -5413], ![97641, 108617, -198044], ![-138402, 830067, 9595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-165431969063, 4193759886, -6767510753]] ![![-52498, -31203, -5413]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7120364707172096, 180503804988603, -291280730042681]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-7120364707172096, 180503804988603, -291280730042681]] 
 ![![89, 0, 0], ![0, 89, 0], ![28, 81, 1]] where
  M :=![![![-7120364707172096, 180503804988603, -291280730042681], ![12233790661792602, -310130991136355, 500461369846256], ![-1464264478625025, 37119630913743, -59900306213227]]]
  hmulB := by decide  
  f := ![![![11752007, 6703518, -1139917]], ![![47876514, 32406497, 37941274]], ![![44375779, 29986956, 34749468]]]
  g := ![![![11634783528348, 267126325151076, -291280730042681], ![-19990198807894, -458960696052619, 500461369846256], ![2392630284779, 54933083530170, -59900306213227]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [46, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 88], [0, 1]]
 g := ![![[64, 87], [68], [84], [41, 44], [34, 49], [1]], ![[78, 2], [68], [84], [0, 45], [47, 40], [1]]]
 h' := ![![[82, 88], [34, 40], [74, 54], [72, 23], [38, 69], [43, 82], [0, 1]], ![[0, 1], [21, 49], [52, 35], [0, 66], [0, 20], [3, 7], [82, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [64, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [46, 7, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1304, -1560, -5946]
  a := ![-1, -3, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1856, 5394, -5946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11752007, -6703518, 1139917]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-11752007, -6703518, 1139917]] 
 ![![89, 0, 0], ![46, 1, 0], ![11, 0, 1]] where
  M :=![![![-11752007, -6703518, 1139917], ![-47876514, -32406497, -37941274], ![257609499, 143785677, -51377134]]]
  hmulB := by decide  
  f := ![![![7120364707172096, -180503804988603, 291280730042681]], ![![3542730178293526, -89809483576847, 144926429349630]], ![![896497486039529, -22726533548184, 36674026254862]]]
  g := ![![![3191806, -6703518, 1139917], ![20900858, -32406497, -37941274], ![-65071721, 143785677, -51377134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-7120364707172096, 180503804988603, -291280730042681]] ![![-11752007, -6703518, 1139917]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [67, 95, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 46, 16], [25, 50, 81], [0, 1]]
 g := ![![[75, 24, 96], [66, 49], [66, 73], [9, 95], [0, 93], [1]], ![[66, 33, 68, 62], [25, 48], [17, 54], [19, 44], [20, 1], [95, 14, 18, 22]], ![[60, 49, 67, 54], [62, 75], [62, 62], [38, 36], [27, 85], [27, 81, 87, 75]]]
 h' := ![![[19, 46, 16], [7, 69, 75], [8, 80, 90], [29, 55, 49], [27, 0, 17], [30, 2, 44], [0, 1]], ![[25, 50, 81], [38, 25, 4], [89, 37, 57], [89, 95, 32], [2, 48, 74], [9, 85, 1], [19, 46, 16]], ![[0, 1], [5, 3, 18], [52, 77, 47], [61, 44, 16], [52, 49, 6], [42, 10, 52], [25, 50, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 8], []]
 b := ![[], [18, 91, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [67, 95, 53, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-102141, -21825, -13968]
  a := ![-64, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1053, -225, -144]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15285199718003443, -387485307646006, 625288776040305]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![15285199718003443, -387485307646006, 625288776040305]] 
 ![![101, 0, 0], ![0, 101, 0], ![76, 39, 1]] where
  M :=![![![15285199718003443, -387485307646006, 625288776040305], ![-26262128593692810, 665754400682129, -1074334293795426], ![3143318624285847, -79684257100431, 128587253784416]]]
  hmulB := by decide  
  f := ![![![-15252742, -9123059, -2051889]], ![![86179338, 43115653, -58842132]], ![![26020237, 12256334, -24129625]]]
  g := ![![![-319175715456037, -245284629437801, 625288776040305], ![548388888462966, 421433582759443, -1074334293795426], ![-65636759042869, -50441456977155, 128587253784416]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [51, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 100], [0, 1]]
 g := ![![[], [81], [], [], [76], [0, 1]], ![[], [81], [], [], [76], [0, 100]]]
 h' := ![![[0, 100], [10], [0, 92], [30], [63], [0, 50], [0, 1]], ![[0, 1], [10], [0, 9], [30], [63], [0, 51], [0, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [51, 0, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1733, -1890, -6831]
  a := ![1, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5123, 2619, -6831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15252742, -9123059, -2051889]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-15252742, -9123059, -2051889]] 
 ![![101, 0, 0], ![67, 1, 0], ![71, 0, 1]] where
  M :=![![![-15252742, -9123059, -2051889], ![86179338, 43115653, -58842132], ![426258147, 249731751, 13694587]]]
  hmulB := by decide  
  f := ![![![15285199718003443, -387485307646006, 625288776040305]], ![![9879665866460771, -250453081302973, 404158551494109]], ![![10776163352500300, -273179614851157, 440832577748971]]]
  g := ![![![7343330, -9123059, -2051889], ![13616059, 43115653, -58842132], ![-171070147, 249731751, 13694587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![15285199718003443, -387485307646006, 625288776040305]] ![![-15252742, -9123059, -2051889]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4685336204232649116064, 118774957083727200007, -191668293154931595039]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-4685336204232649116064, 118774957083727200007, -191668293154931595039]] 
 ![![103, 0, 0], ![0, 103, 0], ![9, 79, 1]] where
  M :=![![![-4685336204232649116064, 118774957083727200007, -191668293154931595039], ![8050068312507126991638, -204072125598018035135, 329313156192500009964], ![-963514041262978904475, 24425427314521125417, -39415547501768030153]]]
  hmulB := by decide  
  f := ![![![9752429411, 5616856264, -495409461]], ![![20807197362, 16025400211, 32710318662]], ![![14621709630, 11545484608, 25359582997]]]
  g := ![![![-28740986076099657871, 148160874915760419496, -191668293154931595039], ![49381067056064338854, -254561276357335134197, 329313156192500009964], ![-5910428288806472166, 30468482329652383568, -39415547501768030153]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [13, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 102], [0, 1]]
 g := ![![[5, 8], [32, 82], [65, 7], [50], [18], [38, 1]], ![[0, 95], [58, 21], [22, 96], [50], [18], [76, 102]]]
 h' := ![![[38, 102], [99, 76], [82, 44], [72, 78], [1, 16], [21, 92], [0, 1]], ![[0, 1], [0, 27], [3, 59], [49, 25], [94, 87], [15, 11], [38, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [94, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [13, 65, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-428, -335, -1604]
  a := ![0, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 1227, -1604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9752429411, -5616856264, 495409461]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-9752429411, -5616856264, 495409461]] 
 ![![103, 0, 0], ![39, 1, 0], ![62, 0, 1]] where
  M :=![![![-9752429411, -5616856264, 495409461], ![-20807197362, -16025400211, -32710318662], ![225504364407, 127373408421, -32380559542]]]
  hmulB := by decide  
  f := ![![![4685336204232649116064, -118774957083727200007, 191668293154931595039]], ![![1695903336432681442086, -42991759229780026846, 69376216280095458219]], ![![2829653967996963340781, -71732745305879684717, 115755822554442008957]]]
  g := ![![![1733879401, -5616856264, 495409461], ![25555564737, -16025400211, -32710318662], ![-26548192936, 127373408421, -32380559542]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-4685336204232649116064, 118774957083727200007, -191668293154931595039]] ![![-9752429411, -5616856264, 495409461]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6267126986997157, -158873922056308, 256376379457637]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![6267126986997157, -158873922056308, 256376379457637]] 
 ![![107, 0, 0], ![39, 1, 0], ![74, 0, 1]] where
  M :=![![![6267126986997157, -158873922056308, 256376379457637], ![-10767807937220754, 272967802070177, -440490773422574], ![1288800757754559, -32671562513163, 52722415358890]]]
  hmulB := by decide  
  f := ![![![-15518032, -4997711, 33705043]], ![![-18886122, -9479926, 12634771]], ![![-15385387, -7060385, 15826577]]]
  g := ![![![-60828431146467, -158873922056308, 256376379457637], ![104511822573017, 272967802070177, -440490773422574], ![-12509037764392, -32671562513163, 52722415358890]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19918613, -504944, 814833]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![19918613, -504944, 814833]] 
 ![![107, 0, 0], ![73, 1, 0], ![87, 0, 1]] where
  M :=![![![19918613, -504944, 814833], ![-34222986, 867565, -1399998], ![4096155, -103839, 167566]]]
  hmulB := by decide  
  f := ![![![4468, 2417, -1533]], ![![3650, 2012, -939]], ![![2985, 1638, -830]]]
  g := ![![![-131878, -504944, 814833], ![226585, 867565, -1399998], ![-27120, -103839, 167566]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25491443675, -13193905068, 13724913469]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-25491443675, -13193905068, 13724913469]] 
 ![![107, 0, 0], ![101, 1, 0], ![100, 0, 1]] where
  M :=![![![-25491443675, -13193905068, 13724913469], ![-576446365698, -341695461863, -51713603470], ![265920830007, 110780019597, -367552263598]]]
  hmulB := by decide  
  f := ![![![131319774474747819364664, -3329003490377574862671, 5372045021727039918707]], ![![121847395617168168964910, -3088875281163164719172, 4984547815846912733185]], ![![122981146248732450863605, -3117616267239264377043, 5030927422121259283923]]]
  g := ![![![-611199801, -13193905068, 13724913469], ![365478089995, -341695461863, -51713603470], ![241423973930, 110780019597, -367552263598]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![6267126986997157, -158873922056308, 256376379457637]] ![![19918613, -504944, 814833]]
  ![![131319774474747819364664, -3329003490377574862671, 5372045021727039918707]] where
 M := ![![![131319774474747819364664, -3329003490377574862671, 5372045021727039918707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![131319774474747819364664, -3329003490377574862671, 5372045021727039918707]] ![![-25491443675, -13193905068, 13724913469]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [17, 15, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 19, 5], [96, 89, 104], [0, 1]]
 g := ![![[49, 86, 83], [85, 89], [69, 107, 1], [21, 1, 66], [10, 22], [1]], ![[98, 86, 48, 82], [65, 26], [22, 56, 107, 61], [36, 65, 90, 82], [45, 102], [78, 49, 97, 16]], ![[7, 90, 68, 105], [5, 16], [50, 93, 13, 71], [82, 66, 84, 73], [61, 31], [107, 20, 46, 93]]]
 h' := ![![[39, 19, 5], [103, 26, 44], [26, 8, 31], [79, 95, 1], [10, 95, 34], [92, 94, 26], [0, 1]], ![[96, 89, 104], [90, 106, 13], [43, 57, 74], [72, 72, 19], [23, 108, 13], [5, 1, 59], [39, 19, 5]], ![[0, 1], [4, 86, 52], [78, 44, 4], [41, 51, 89], [15, 15, 62], [17, 14, 24], [96, 89, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 63], []]
 b := ![[], [2, 72, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [17, 15, 83, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14625293, 9283748, 6473510]
  a := ![1, -1, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![134177, 85172, 59390]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63065681124121517174, 1598737687640571471, -2579898417277666037]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-63065681124121517174, 1598737687640571471, -2579898417277666037]] 
 ![![113, 0, 0], ![0, 113, 0], ![85, 47, 1]] where
  M :=![![![-63065681124121517174, 1598737687640571471, -2579898417277666037], ![108355733525661973554, -2746856797098103757, 4432629291288096752], ![-12969116118073015005, 328771755791275251, -530542151454055381]]]
  hmulB := by decide  
  f := ![![![1132645295, 653085972, -51309391]], ![![2154994422, 1710984707, 3815897050]], ![![1515110392, 1071010322, 1580573419]]]
  g := ![![![1382528180039646867, 1087203215041512170, -2579898417277666037], ![-2375378373750674782, -1867968437943704877, 4432629291288096752], ![284309440314351260, 223577459063113966, -530542151454055381]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [1, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 112], [0, 1]]
 g := ![![[15, 1], [26], [25], [56], [106, 4], [98, 1]], ![[0, 112], [26], [25], [56], [46, 109], [83, 112]]]
 h' := ![![[98, 112], [98, 112], [24, 34], [106, 108], [7, 100], [15, 111], [0, 1]], ![[0, 1], [0, 1], [79, 79], [68, 5], [89, 13], [45, 2], [98, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [3, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [1, 15, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50, 21, -252]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![190, 105, -252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1132645295, 653085972, -51309391]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1132645295, 653085972, -51309391]] 
 ![![113, 0, 0], ![55, 1, 0], ![70, 0, 1]] where
  M :=![![![1132645295, 653085972, -51309391], ![2154994422, 1710984707, 3815897050], ![-26352113613, -14904422463, 3618933232]]]
  hmulB := by decide  
  f := ![![![-63065681124121517174, 1598737687640571471, -2579898417277666037]], ![![-29736785206203729832, 753838194894985196, -1216475961583925091]], ![![-39182007033686541745, 993277963633905117, -1602862224432660867]]]
  g := ![![![-276065715, 653085972, -51309391], ![-3177539451, 1710984707, 3815897050], ![4779343324, -14904422463, 3618933232]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-63065681124121517174, 1598737687640571471, -2579898417277666037]] ![![1132645295, 653085972, -51309391]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [78, 71, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 37, 47], [56, 89, 80], [0, 1]]
 g := ![![[33, 92, 81], [32, 65, 74], [82, 98, 25], [70, 68, 113], [58, 31, 103], [1]], ![[9, 44, 3, 35], [44, 98, 62, 17], [12, 76, 48, 42], [61, 123, 4, 81], [48, 94, 110, 115], [109, 38, 100, 64]], ![[70, 36, 116, 39], [104, 75, 24, 20], [0, 38, 0, 66], [18, 20, 41, 95], [12, 46, 110, 111], [89, 55, 4, 63]]]
 h' := ![![[93, 37, 47], [44, 108, 118], [81, 124, 70], [1, 31, 5], [48, 56, 85], [49, 56, 22], [0, 1]], ![[56, 89, 80], [86, 42, 84], [83, 120, 120], [101, 84, 124], [109, 3, 37], [73, 11, 18], [93, 37, 47]], ![[0, 1], [62, 104, 52], [77, 10, 64], [7, 12, 125], [63, 68, 5], [18, 60, 87], [56, 89, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 14], []]
 b := ![[], [13, 112, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [78, 71, 105, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1311402, 850392, 750570]
  a := ![0, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10326, 6696, 5910]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [97, 117, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 123, 128], [43, 7, 3], [0, 1]]
 g := ![![[77, 89, 113], [5, 118, 12], [86, 114], [20, 49], [101, 64], [41, 1], []], ![[86, 130, 54, 79], [84, 4, 105, 106], [107, 36], [45, 4], [124, 20], [48, 49], [24, 9]], ![[10, 2, 120, 52], [21, 42, 52, 1], [60, 52], [117, 25], [94, 34], [46, 64], [18, 9]]]
 h' := ![![[129, 123, 128], [39, 79, 84], [78, 49, 55], [125, 59, 101], [10, 17, 7], [84, 84, 123], [0, 0, 1], [0, 1]], ![[43, 7, 3], [117, 47, 89], [16, 129, 107], [35, 6, 6], [83, 128, 129], [37, 93, 85], [34, 19, 7], [129, 123, 128]], ![[0, 1], [36, 5, 89], [121, 84, 100], [96, 66, 24], [21, 117, 126], [121, 85, 54], [103, 112, 123], [43, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 75], []]
 b := ![[], [59, 56, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [97, 117, 90, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10611, 3406, -3406]
  a := ![2, -2, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81, 26, -26]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-90841384536244731445459994886523, -53056517333363434163645311817084, -1542438494262821767034136188838]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-90841384536244731445459994886523, -53056517333363434163645311817084, -1542438494262821767034136188838]] 
 ![![137, 0, 0], ![0, 137, 0], ![128, 107, 1]] where
  M :=![![![-90841384536244731445459994886523, -53056517333363434163645311817084, -1542438494262821767034136188838], ![64782416759038514215433719931196, -766343340573574872995414537327, -321423980988706248515940143280180], ![2260764936380783491980819956283126, 1296492993414664746432999526442586, -161478333834926699130965486177417]]]
  hmulB := by decide  
  f := ![![![-3042683847540783719419622335435716447298241567825646953323888247, 77133129333286492736571590802758509817647985794104234595158008, -124470474315457294610973263661265350804430404613532036372633862]], ![![5227759921249206373660877073773144733786076993768345527650622204, -132525593303095141492835598368106537809559842894982314975833567, 213857827368804367197483017494020357297027105537561334825680324]], ![![1235628230781542601371508172854930629310125114927459535357573394, -31323619839689966977849376839281271989204792685936399700206211, 50547227273465989941839496595599393931779286217961755642975671]]]
  g := ![![![778034618462747844780360856093, 817404390896047408094943506486, -1542438494262821767034136188838], ![300781401338054294337633372699228, 251033573886503613257902189171109, -321423980988706248515940143280180], ![167372201950740153144119723992646, 135581567253662931047053332462965, -161478333834926699130965486177417]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [23, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 136], [0, 1]]
 g := ![![[116, 30], [39], [65], [127, 49], [63], [115], [1]], ![[84, 107], [39], [65], [93, 88], [63], [115], [1]]]
 h' := ![![[72, 136], [3, 116], [30, 83], [93, 32], [80, 7], [76, 36], [114, 72], [0, 1]], ![[0, 1], [135, 21], [115, 54], [68, 105], [36, 130], [65, 101], [92, 65], [72, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [21, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [23, 65, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![932, -227, -134]
  a := ![13, -1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![132, 103, -134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3042683847540783719419622335435716447298241567825646953323888247, -77133129333286492736571590802758509817647985794104234595158008, 124470474315457294610973263661265350804430404613532036372633862]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![3042683847540783719419622335435716447298241567825646953323888247, -77133129333286492736571590802758509817647985794104234595158008, 124470474315457294610973263661265350804430404613532036372633862]] 
 ![![137, 0, 0], ![41, 1, 0], ![92, 0, 1]] where
  M :=![![![3042683847540783719419622335435716447298241567825646953323888247, -77133129333286492736571590802758509817647985794104234595158008, 124470474315457294610973263661265350804430404613532036372633862], ![-5227759921249206373660877073773144733786076993768345527650622204, 132525593303095141492835598368106537809559842894982314975833567, -213857827368804367197483017494020357297027105537561334825680324], ![625711471373429508105568276829285045448176906468205089171325234, -15862010732983593486880775652776026442904410144478915305715738, 25596679618692957894094089621096359161046290126201647562993405]]]
  hmulB := by decide  
  f := ![![![90841384536244731445459994886523, 53056517333363434163645311817084, 1542438494262821767034136188838]], ![![26713243425014565511302380076031, 15883821562105652376514256927283, 2807766125937824386601019905274]], ![![44501039714990743073003646520270, 26165741614998329902353059567366, 2214472082533622640132160697449]]]
  g := ![![![-38293003553405410091901333565602897256830571088036691785087217, -77133129333286492736571590802758509817647985794104234595158008, 124470474315457294610973263661265350804430404613532036372633862], ![65792780082145216111688328486017226914952285817467316513159061, 132525593303095141492835598368106537809559842894982314975833567, -213857827368804367197483017494020357297027105537561334825680324], ![-7874749003605805001379388076990970169408766198676722329122064, -15862010732983593486880775652776026442904410144478915305715738, 25596679618692957894094089621096359161046290126201647562993405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-90841384536244731445459994886523, -53056517333363434163645311817084, -1542438494262821767034136188838]] ![![3042683847540783719419622335435716447298241567825646953323888247, -77133129333286492736571590802758509817647985794104234595158008, 124470474315457294610973263661265350804430404613532036372633862]]
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


lemma PB176I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB176I2 : PrimesBelowBoundCertificateInterval O 79 137 176 where
  m := 11
  g := ![2, 2, 1, 2, 2, 3, 1, 2, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB176I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I101N1, I103N1, I107N0, I107N1, I107N2, I113N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [], [I113N1], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
