
import IdealArithmetic.Examples.NF3_1_138355_1.RI3_1_138355_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [28, 35, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12, 15], [18, 24, 22], [0, 1]]
 g := ![![[9, 36, 36], [16, 27], [3, 12, 4], [25, 1], []], ![[12, 28, 24, 2], [13, 4], [16, 12, 25, 17], [30, 21], [28, 3]], ![[6, 17, 24, 32], [11, 26], [31, 12, 11, 8], [18, 33], [21, 3]]]
 h' := ![![[7, 12, 15], [22, 35, 31], [27, 12, 8], [3, 22, 35], [0, 0, 1], [0, 1]], ![[18, 24, 22], [15, 24, 11], [3, 6, 2], [36, 21, 23], [5, 29, 24], [7, 12, 15]], ![[0, 1], [16, 15, 32], [18, 19, 27], [2, 31, 16], [32, 8, 12], [18, 24, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 32], []]
 b := ![[], [14, 14, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [28, 35, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4662, -370, -370]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126, -10, -10]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169129, 38854, -904]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-169129, 38854, -904]] 
 ![![41, 0, 0], ![24, 1, 0], ![39, 0, 1]] where
  M :=![![![-169129, 38854, -904], ![-63280, -173649, 37950], ![2656500, 126470, -135699]]]
  hmulB := by decide  
  f := ![![![18764459151, 5158120066, 1317530604]], ![![13233516144, 3637731555, 929180126]], ![![28905108629, 7945660444, 2029547717]]]
  g := ![![![-26009, 38854, -904], ![64006, -173649, 37950], ![119841, 126470, -135699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3902197086629358297857, 1072666200078400333236, 273989462904385476876]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![3902197086629358297857, 1072666200078400333236, 273989462904385476876]] 
 ![![41, 0, 0], ![25, 1, 0], ![31, 0, 1]] where
  M :=![![![3902197086629358297857, 1072666200078400333236, 273989462904385476876], ![19179262403306983381320, 5272144401151285682237, 1346655662982785810112], ![94265896408795006707840, 25912540718220912431880, 6618800064134071492349]]]
  hmulB := by decide  
  f := ![![![553375534153, 21240795516, -27228969180]], ![![290935622225, 23128062833, -16749083004]], ![![408182180543, -31158635364, -10557451951]]]
  g := ![![![-766051982082112190639, 1072666200078400333236, 273989462904385476876], ![-3765138370193695580197, 5272144401151285682237, 1346655662982785810112], ![-18505620086216683423219, 25912540718220912431880, 6618800064134071492349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1283937, -323026, 118872]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-1283937, -323026, 118872]] 
 ![![41, 0, 0], ![32, 1, 0], ![1, 0, 1]] where
  M :=![![![-1283937, -323026, 118872], ![8321040, -689577, -204154], ![-14290780, 7300270, -893731]]]
  hmulB := by decide  
  f := ![![![2106675663367, 579099345434, 147918447148]], ![![1896778354344, 521401145195, 133180685398]], ![![1292632223027, 355328770944, 90761076557]]]
  g := ![![![217903, -323026, 118872], ![746138, -689577, -204154], ![-6024529, 7300270, -893731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-169129, 38854, -904]] ![![3902197086629358297857, 1072666200078400333236, 273989462904385476876]]
  ![![2106675663367, 579099345434, 147918447148]] where
 M := ![![![2106675663367, 579099345434, 147918447148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![2106675663367, 579099345434, 147918447148]] ![![-1283937, -323026, 118872]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101241131338117, -25073537541184, 910500100213]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![101241131338117, -25073537541184, 910500100213]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 13, 1]] where
  M :=![![![101241131338117, -25073537541184, 910500100213], ![63735007014910, 105793631839182, -24163037440971], ![-1691412620867970, -57080180189945, 81630594398211]]]
  hmulB := by decide  
  f := ![![![168762012081649182811982949, 46390610776036902819382873, 11849481720784848846081486]], ![![829463720454939419225704020, 228009420685573427042390379, 58240092496821751665464359]], ![![365201044211627464664571445, 100389295482132261469791049, 25642281959186097548588345]]]
  g := ![![![2248572810164, -858372996371, 910500100213], ![4291864981855, 9765421362135, -24163037440971], ![-48827106810675, -26006462962016, 81630594398211]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 42], [0, 1]]
 g := ![![[36, 11], [25, 16], [16], [13, 10], [1]], ![[0, 32], [0, 27], [16], [35, 33], [1]]]
 h' := ![![[28, 42], [29, 22], [17, 4], [34, 39], [39, 28], [0, 1]], ![[0, 1], [0, 21], [0, 39], [8, 4], [6, 15], [28, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [24, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [4, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-220, 589, 85]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -12, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6801073311229, 6797845534334, -1664618888900]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![6801073311229, 6797845534334, -1664618888900]] 
 ![![43, 0, 0], ![29, 1, 0], ![19, 0, 1]] where
  M :=![![![6801073311229, 6797845534334, -1664618888900], ![-116523322223000, -1522021133271, 5133226645434], ![359325865180380, -90857188995830, 3611205512163]]]
  hmulB := by decide  
  f := ![![![460894212376530558680065047, 126694175730396266462182558, 32361296700639925248739056]], ![![363516812278236766724037681, 99926320745609811914582663, 25524025040688233114519866]], ![![462578444309921256620598811, 127157150466918716017390944, 32479553619137789682807535]]]
  g := ![![![-3690899727799, 6797845534334, -1664618888900], ![-3951535247009, -1522021133271, 5133226645434], ![68036545147171, -90857188995830, 3611205512163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![101241131338117, -25073537541184, 910500100213]] ![![6801073311229, 6797845534334, -1664618888900]]
  ![![43, 0, 0]] where
 M := ![![![3937366486780026747025268733, 643658546895511768962430152, -293948047580016550208364437]]]
 hmul := by decide  
 g := ![![![![91566662483256435977331831, 14968803416174692301451864, -6836001106512012795543359]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24248701, 6665671, 1702602]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![24248701, 6665671, 1702602]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 24, 1]] where
  M :=![![![24248701, 6665671, 1702602], ![119182140, 32761711, 8368273], ![585779110, 161023505, 41129984]]]
  hmulB := by decide  
  f := ![![![-303, 1718, -337]], ![![-23590, -1988, 1381]], ![![-10189, -237, 470]]]
  g := ![![![-607063, -727591, 1702602], ![-2983709, -3576103, 8368273], ![-14664902, -17576513, 41129984]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [32, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46], [0, 1]]
 g := ![![[12, 25], [34, 16], [46, 6], [0, 17], [1]], ![[0, 22], [0, 31], [45, 41], [5, 30], [1]]]
 h' := ![![[39, 46], [40, 5], [32, 4], [0, 10], [15, 39], [0, 1]], ![[0, 1], [0, 42], [0, 43], [14, 37], [32, 8], [39, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [6, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [32, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3546, -55, 125]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -65, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-303, 1718, -337]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-303, 1718, -337]] 
 ![![47, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![-303, 1718, -337], ![-23590, -1988, 1381], ![96670, -16685, -607]]]
  hmulB := by decide  
  f := ![![![24248701, 6665671, 1702602]], ![![13886246, 3817159, 975011]], ![![29489069, 8106184, 2070550]]]
  g := ![![![-574, 1718, -337], ![-541, -1988, 1381], ![10293, -16685, -607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![24248701, 6665671, 1702602]] ![![-303, 1718, -337]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [18, 21, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 47, 39], [20, 5, 14], [0, 1]]
 g := ![![[41, 52, 42], [17, 37], [41, 35, 37], [43, 46], [1]], ![[7, 28, 4, 5], [5, 4], [20, 28, 22, 3], [21, 47], [45, 49, 46, 12]], ![[15, 25, 52, 18], [14, 44], [5, 19, 11, 50], [16, 37], [39, 19, 2, 41]]]
 h' := ![![[4, 47, 39], [28, 36, 25], [4, 33, 39], [27, 32, 14], [35, 32, 24], [0, 1]], ![[20, 5, 14], [40, 40, 45], [17, 36, 51], [9, 51, 46], [49, 5, 43], [4, 47, 39]], ![[0, 1], [26, 30, 36], [38, 37, 16], [21, 23, 46], [37, 16, 39], [20, 5, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 24], []]
 b := ![[], [5, 41, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [18, 21, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135521, 477, -1431]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2557, 9, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀


def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![813151379, -332571782, 34003862]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![813151379, -332571782, 34003862]] 
 ![![59, 0, 0], ![18, 1, 0], ![30, 0, 1]] where
  M :=![![![813151379, -332571782, 34003862], ![2380270340, 983170689, -298567920], ![-20899754400, 887430740, 684602769]]]
  hmulB := by decide  
  f := ![![![938039726274898641, 257855635265982238, 65863664771232522]], ![![364324942490414442, 100148465846080365, 25580767218972884]], ![![861043098150033770, 236690204951725720, 60457411750936469]]]
  g := ![![![97954705, -332571782, 34003862], ![-107792618, 983170689, -298567920], ![-973077810, 887430740, 684602769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1684905811, -365928720, 4703805]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1684905811, -365928720, 4703805]] 
 ![![59, 0, 0], ![22, 1, 0], ![47, 0, 1]] where
  M :=![![![1684905811, -365928720, 4703805], ![329266350, 1708424836, -361224915], ![-25285744050, -1476858225, 1347199921]]]
  hmulB := by decide  
  f := ![![![-1768111817300962081, -486032289572584995, -124146473492357820]], ![![-806588358052308698, -221721263650163069, -56633918303335845]], ![![-2132436759791376523, -586180755418665360, -149727240711330704]]]
  g := ![![![161258624, -365928720, 4703805], ![-343703543, 1708424836, -361224915], ![-951072193, -1476858225, 1347199921]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![813151379, -332571782, 34003862]] ![![813151379, -332571782, 34003862]]
  ![![-841067947897437039, -567229958783167296, 150224690560953016]] where
 M := ![![![-841067947897437039, -567229958783167296, 150224690560953016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-841067947897437039, -567229958783167296, 150224690560953016]] ![![1684905811, -365928720, 4703805]]
  ![![59, 0, 0]] where
 M := ![![![-5402433086512129722662578029, -883159401554306845785659976, 403324065284208754937058181]]]
 hmul := by decide  
 g := ![![![![-91566662483256435977331831, -14968803416174692301451864, 6836001106512012795543359]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4821870463356829, 1325473150733896, 338563550000196]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![4821870463356829, 1325473150733896, 338563550000196]] 
 ![![61, 0, 0], ![0, 61, 0], ![51, 53, 1]] where
  M :=![![![4821870463356829, 1325473150733896, 338563550000196], ![23699448500013720, 6514688213357809, 1664036700734092], ![116482569051386440, 32019632003684180, 8178724914091901]]]
  hmulB := by decide  
  f := ![![![-86968191, 19382344, -343412]], ![![-24038840, -88685251, 19038932]], ![![-71749361, -59682999, 15113165]]]
  g := ![![![-204014271912347, -272432704906172, 338563550000196], ![-1002728249793852, -1339004211894247, 1664036700734092], ![-4928400025693451, -6581193253166993, 8178724914091901]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [10, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 60], [0, 1]]
 g := ![![[58, 15], [13], [39, 56], [17, 15], [30, 1]], ![[20, 46], [13], [11, 5], [40, 46], [60, 60]]]
 h' := ![![[30, 60], [19, 25], [37, 47], [13, 19], [5, 36], [0, 1]], ![[0, 1], [37, 36], [44, 14], [34, 42], [48, 25], [30, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [5, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [10, 31, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220, 54, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 20, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86968191, 19382344, -343412]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-86968191, 19382344, -343412]] 
 ![![61, 0, 0], ![7, 1, 0], ![12, 0, 1]] where
  M :=![![![-86968191, 19382344, -343412], ![-24038840, -88685251, 19038932], ![1332725240, 71155820, -69646319]]]
  hmulB := by decide  
  f := ![![![4821870463356829, 1325473150733896, 338563550000196]], ![![941844946614943, 258901643745821, 66130845094024]], ![![2858114993633908, 785660816598212, 200680123181873]]]
  g := ![![![-3582355, 19382344, -343412], ![6037553, -88685251, 19038932], ![27383448, 71155820, -69646319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![4821870463356829, 1325473150733896, 338563550000196]] ![![-86968191, 19382344, -343412]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![66, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![70, 5, 2]]]
  hmulB := by decide  
  f := ![![![-3, -2, 1]], ![![1, 0, 0]], ![![-4, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-1, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![67, 0, 0], ![64, 1, 0], ![58, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![70, 5, -2]]]
  hmulB := by decide  
  f := ![![![1, 2, 1]], ![![2, 2, 1]], ![![4, 3, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![-2, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![1, 1, 0]]
  ![![1, 2, 1]] where
 M := ![![![1, 2, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![1, 2, 1]] ![![-3, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [34, 22, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 4, 41], [53, 66, 30], [0, 1]]
 g := ![![[34, 42, 29], [31, 47, 60], [4, 60, 50], [3, 4], [33, 1], []], ![[25, 22, 51, 55], [0, 46, 15, 46], [6, 53, 33, 55], [61, 1], [37, 25], [66, 48]], ![[32, 7, 53, 38], [58, 2], [49, 59, 11, 1], [47, 1], [68, 16], [6, 48]]]
 h' := ![![[51, 4, 41], [11, 28, 61], [6, 34, 29], [23, 31, 11], [14, 21, 2], [0, 0, 1], [0, 1]], ![[53, 66, 30], [70, 34, 62], [23, 64, 42], [64, 11, 9], [24, 57, 70], [2, 22, 66], [51, 4, 41]], ![[0, 1], [11, 9, 19], [34, 44], [4, 29, 51], [18, 64, 70], [49, 49, 4], [53, 66, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 38], []]
 b := ![[], [45, 65, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [34, 22, 38, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![697575, 134829, 34861]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9825, 1899, 491]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11264226830731057588893777, 3096398035030643274438756, 790908145044780058937173]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![11264226830731057588893777, 3096398035030643274438756, 790908145044780058937173]] 
 ![![73, 0, 0], ![0, 73, 0], ![37, 66, 1]] where
  M :=![![![11264226830731057588893777, 3096398035030643274438756, 790908145044780058937173], ![55363570153134604125602110, 15218767555954957883579642, 3887306180075423333375929], ![272111432605279633336315030, 74800101053511720792481755, 19106073736030381216955571]]]
  hmulB := by decide  
  f := ![![![369705005619, -1179612585357, 224698839346]], ![![15728918754220, 1493199202349, -954913746011]], ![![13492380284461, 902189475630, -742084448282]]]
  g := ![![![-246566774464737049202488, -672651226546915624868694, 790908145044780058937173], ![-1211873404241863824785031, -3306074525055109344099064, 3887306180075423333375929], ![-5956346515449924269740289, -16249325555130047116802547, 19106073736030381216955571]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [4, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 72], [0, 1]]
 g := ![![[62, 55], [54], [61], [25, 36], [38], [1]], ![[0, 18], [54], [61], [3, 37], [38], [1]]]
 h' := ![![[44, 72], [22, 36], [47, 45], [46, 34], [10, 6], [69, 44], [0, 1]], ![[0, 1], [0, 37], [56, 28], [9, 39], [55, 67], [34, 29], [44, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [2, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [4, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-374, 126, -18]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 18, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![369705005619, -1179612585357, 224698839346]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![369705005619, -1179612585357, 224698839346]] 
 ![![73, 0, 0], ![6, 1, 0], ![37, 0, 1]] where
  M :=![![![369705005619, -1179612585357, 224698839346], ![15728918754220, 1493199202349, -954913746011], ![-66843962220770, 10954350024165, 538285456338]]]
  hmulB := by decide  
  f := ![![![11264226830731057588893777, 3096398035030643274438756, 790908145044780058937173]], ![![1684231933390697940533764, 462974736522449555208386, 118256918497864434068479]], ![![9436819525237380330484723, 2594066141775966054064599, 662598289077907443803164]]]
  g := ![![![-11869541617, -1179612585357, 224698839346], ![576733317021, 1493199202349, -954913746011], ![-2088857866442, 10954350024165, 538285456338]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![11264226830731057588893777, 3096398035030643274438756, 790908145044780058937173]] ![![369705005619, -1179612585357, 224698839346]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-876019639024529724607, -240807072663305327664, -61508976881879963058]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-876019639024529724607, -240807072663305327664, -61508976881879963058]] 
 ![![79, 0, 0], ![0, 79, 0], ![13, 53, 1]] where
  M :=![![![-876019639024529724607, -240807072663305327664, -61508976881879963058], ![-4305628381731597414060, -1183564523433929539897, -302316049545185290722], ![-21162123468162970350540, -5817208629457523867670, -1485880572979114830619]]]
  hmulB := by decide  
  f := ![![![-24163936057, -7028172036, 2430227742]], ![![170115941940, -12012797347, -4597944294]], ![![106077944981, -7353395891, -2895048463]]]
  g := ![![![-967125817216331707, 38217325342738388790, -61508976881879963058], ![-4753414400559349806, 187837798765327732511, -302316049545185290722], ![-23362987587778196867, 923221034663741293103, -1485880572979114830619]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [22, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 78], [0, 1]]
 g := ![![[69, 18], [46, 9], [35, 11], [20, 10], [52], [1]], ![[0, 61], [51, 70], [6, 68], [8, 69], [52], [1]]]
 h' := ![![[62, 78], [15, 52], [20, 3], [34, 66], [51, 22], [57, 62], [0, 1]], ![[0, 1], [0, 27], [48, 76], [18, 13], [72, 57], [30, 17], [62, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [29, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [22, 17, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![582, 337, 63]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -38, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24163936057, 7028172036, -2430227742]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![24163936057, 7028172036, -2430227742]] 
 ![![79, 0, 0], ![25, 1, 0], ![7, 0, 1]] where
  M :=![![![24163936057, 7028172036, -2430227742], ![-170115941940, 12012797347, 4597944294], ![321856100580, -147126220470, 16610741641]]]
  hmulB := by decide  
  f := ![![![876019639024529724607, 240807072663305327664, 61508976881879963058]], ![![331723029839808107965, 91186599240715983943, 23291651539141574268]], ![![345496973940945296491, 94972887824059002042, 24258777356357905975]]]
  g := ![![![-1702895831, 7028172036, -2430227742], ![-6362297287, 12012797347, 4597944294], ![49161220517, -147126220470, 16610741641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-876019639024529724607, -240807072663305327664, -61508976881879963058]] ![![24163936057, 7028172036, -2430227742]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB106I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB106I1 : PrimesBelowBoundCertificateInterval O 31 79 106 where
  m := 11
  g := ![1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB106I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
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
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I41N0, I41N1, I41N2, I43N1, I47N1, I59N0, I59N1, I61N1, I67N0, I67N1, I73N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [], [I59N0, I59N0, I59N1], [I61N1], [I67N0, I67N0, I67N1], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
