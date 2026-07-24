
import IdealArithmetic.Examples.NF3_3_376300_1.RI3_3_376300_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [39, 13, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 32, 79], [34, 50, 4], [0, 1]]
 g := ![![[68, 39, 69], [72, 19, 44], [38, 1], [5, 69], [20, 38, 1], []], ![[69, 75, 60, 2], [21, 57, 78, 57], [79, 10], [81, 44], [74, 0, 4, 43], [20, 16]], ![[40, 11, 7, 63], [73, 46, 20, 11], [5, 28], [78, 51], [73, 48, 9, 29], [12, 16]]]
 h' := ![![[4, 32, 79], [14, 4, 61], [41, 48, 58], [64, 0, 82], [50, 1, 61], [0, 0, 1], [0, 1]], ![[34, 50, 4], [72, 0, 46], [77, 55, 52], [81, 47, 33], [13, 70, 58], [66, 36, 50], [4, 32, 79]], ![[0, 1], [37, 79, 59], [77, 63, 56], [40, 36, 51], [54, 12, 47], [24, 47, 32], [34, 50, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 29], []]
 b := ![[], [6, 60, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [39, 13, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-279959, -730732, -1117927]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3373, -8804, -13469]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [60, 57, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 25, 15], [64, 63, 74], [0, 1]]
 g := ![![[74, 51, 32], [30, 87], [34, 18], [58, 2, 88], [79, 74, 1], []], ![[68, 78, 11, 63], [49, 72], [17, 47], [31, 3, 23, 12], [8, 20, 23, 83], [45, 47]], ![[38, 28, 87, 83], [81, 85], [66, 40], [53, 66, 40, 12], [87, 21, 66, 59], [75, 47]]]
 h' := ![![[10, 25, 15], [70, 12, 11], [88, 0, 49], [80, 40, 75], [66, 46, 55], [0, 0, 1], [0, 1]], ![[64, 63, 74], [70, 54, 72], [47, 45, 61], [34, 59, 74], [15, 9, 61], [70, 10, 63], [10, 25, 15]], ![[0, 1], [43, 23, 6], [50, 44, 68], [19, 79, 29], [14, 34, 62], [41, 79, 25], [64, 63, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 84], []]
 b := ![[], [10, 47, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [60, 57, 15, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68263, 218317, 450073]
  a := ![-1, 1, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![767, 2453, 5057]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401187094508451675583415, 1408573544144556616440, -16809246377765229299364]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![401187094508451675583415, 1408573544144556616440, -16809246377765229299364]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 45, 1]] where
  M :=![![![401187094508451675583415, 1408573544144556616440, -16809246377765229299364], ![-235329449288713210191096, -826245013769270984881, 9860014809011896315080], ![53338522373554251228888, 187272303938900195832, -2234818557913827601321]]]
  hmulB := by decide  
  f := ![![![1202512248647, 2317512564264, 1180133185572]], ![![16521864598008, 31843221266639, 16222587949848]], ![![8483214625087, 16349933402547, 8329150794371]]]
  g := ![![![11240888618523980173787, 7812625366428658506060, -16809246377765229299364], ![-6593711922249494423808, -4582751664116542321273, 9860014809011896315080], ![1494495703587847246217, 1038702138248053012941, -2234818557913827601321]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [35, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 96], [0, 1]]
 g := ![![[78, 61], [12], [48], [32], [22], [83, 1]], ![[0, 36], [12], [48], [32], [22], [69, 96]]]
 h' := ![![[83, 96], [92, 62], [30, 20], [35, 57], [31, 41], [5, 64], [0, 1]], ![[0, 1], [0, 35], [41, 77], [13, 40], [39, 56], [79, 33], [83, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [24, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [35, 14, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3233, 2, 138]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -64, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64331150973215, 123984523011022, 63151017787643]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![64331150973215, 123984523011022, 63151017787643]] 
 ![![97, 0, 0], ![73, 1, 0], ![32, 0, 1]] where
  M :=![![![64331150973215, 123984523011022, 63151017787643], ![884114249027002, 1703940100887669, 867891661077154], ![1609481286579022, 3101930587839814, 1579955577876647]]]
  hmulB := by decide  
  f := ![![![-9976338840337737638356487, -35027066299675015215168, 417996340886216904882779]], ![![-7447636974971626916821285, -26148758404582299454559, 312046839387588752061203]], ![![-3304837262894592664434902, -11603330216591412807050, 138468621126705247784321]]]
  g := ![![![-113478057711711, 123984523011022, 63151017787643], ![-1559546868765379, 1703940100887669, 867891661077154], ![-2839072475441032, 3101930587839814, 1579955577876647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![401187094508451675583415, 1408573544144556616440, -16809246377765229299364]] ![![64331150973215, 123984523011022, 63151017787643]]
  ![![97, 0, 0]] where
 M := ![![![97, 194, 97]]]
 hmul := by decide  
 g := ![![![![1, 2, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-206123, -400710, -204178]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-206123, -400710, -204178]] 
 ![![101, 0, 0], ![0, 101, 0], ![5, 61, 1]] where
  M :=![![![-206123, -400710, -204178], ![-2858492, -5507105, -2804970], ![-5201584, -10025396, -5106395]]]
  hmulB := by decide  
  f := ![![![-5132855, -7740238, 4456990]], ![![62397860, 94094667, -54181666]], ![![36270573, 54695265, -31494671]]]
  g := ![![![8067, 119348, -204178], ![110558, 1639565, -2804970], ![201291, 2984799, -5106395]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [52, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 100], [0, 1]]
 g := ![![[92, 68], [52], [23, 87], [88], [16], [64, 1]], ![[0, 33], [52], [36, 14], [88], [16], [27, 100]]]
 h' := ![![[64, 100], [77, 13], [16, 70], [71, 84], [1, 54], [5, 4], [0, 1]], ![[0, 1], [0, 88], [52, 31], [94, 17], [23, 47], [59, 97], [64, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [74, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [52, 37, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![480, 1816, 4843]
  a := ![1, -2, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-235, -2907, 4843]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5132855, -7740238, 4456990]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-5132855, -7740238, 4456990]] 
 ![![101, 0, 0], ![78, 1, 0], ![72, 0, 1]] where
  M :=![![![-5132855, -7740238, 4456990], ![62397860, 94094667, -54181666], ![-117277312, -176851732, 101834905]]]
  hmulB := by decide  
  f := ![![![-206123, -400710, -204178]], ![![-187486, -363985, -185454]], ![![-198440, -384916, -196111]]]
  g := ![![![2749529, -7740238, 4456990], ![-33424814, 94094667, -54181666], ![62822224, -176851732, 101834905]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-206123, -400710, -204178]] ![![-5132855, -7740238, 4456990]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [54, 31, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 5], [93, 99, 98], [0, 1]]
 g := ![![[61, 86, 49], [44, 38, 81], [93, 25, 82], [83, 34], [87, 64], [1]], ![[39, 13, 51, 35], [70, 99, 45, 69], [84, 47, 96, 96], [85, 16], [100, 91], [1, 35, 49, 22]], ![[42, 77, 74, 30], [21, 56, 85, 36], [102, 33, 92, 66], [26, 8], [84, 63], [47, 66, 82, 81]]]
 h' := ![![[2, 3, 5], [96, 93, 7], [25, 42, 94], [84, 66, 59], [72, 79, 72], [49, 72, 95], [0, 1]], ![[93, 99, 98], [92, 96, 25], [59, 67, 40], [86, 24, 94], [12, 91, 4], [57, 72, 83], [2, 3, 5]], ![[0, 1], [91, 17, 71], [49, 97, 72], [84, 13, 53], [56, 36, 27], [67, 62, 28], [93, 99, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 47], []]
 b := ![[], [73, 72, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [54, 31, 8, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-294374, -789598, -1269269]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2858, -7666, -12323]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4629771, 8911012, 4538509]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![4629771, 8911012, 4538509]] 
 ![![107, 0, 0], ![0, 107, 0], ![4, 54, 1]] where
  M :=![![![4629771, 8911012, 4538509], ![63539126, 122464999, 62377084], ![115677150, 222941306, 113553987]]]
  hmulB := by decide  
  f := ![![![-370719913, -559037870, 321905631]], ![![4506678834, 6795977361, -3913265090]], ![![2181377906, 3289472228, -1894146515]]]
  g := ![![![-126395, -2207182, 4538509], ![-1738030, -30335491, 62377084], ![-3163914, -55224056, 113553987]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [75, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 106], [0, 1]]
 g := ![![[34, 10], [2, 52], [89], [98, 14], [48], [18, 1]], ![[0, 97], [82, 55], [89], [29, 93], [48], [36, 106]]]
 h' := ![![[18, 106], [64, 44], [85, 65], [33, 14], [7, 96], [41, 35], [0, 1]], ![[0, 1], [0, 63], [78, 42], [71, 93], [23, 11], [29, 72], [18, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [81, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [75, 89, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38643, 147662, 365195]
  a := ![1, 20, 121]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13291, -182924, 365195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-370719913, -559037870, 321905631]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-370719913, -559037870, 321905631]] 
 ![![107, 0, 0], ![50, 1, 0], ![79, 0, 1]] where
  M :=![![![-370719913, -559037870, 321905631], ![4506678834, 6795977361, -3913265090], ![-8470341442, -12773097618, 7355015231]]]
  hmulB := by decide  
  f := ![![![4629771, 8911012, 4538509]], ![![2757268, 5308557, 2703762]], ![![4499337, 8662722, 4412114]]]
  g := ![![![20099334, -559037870, 321905631], ![-244338758, 6795977361, -3913265090], ![459236787, -12773097618, 7355015231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![4629771, 8911012, 4538509]] ![![-370719913, -559037870, 321905631]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22651758625033526023387543, 79530643842528526929304, -949080857360020998096495]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![22651758625033526023387543, 79530643842528526929304, -949080857360020998096495]] 
 ![![109, 0, 0], ![0, 109, 0], ![77, 34, 1]] where
  M :=![![![22651758625033526023387543, 79530643842528526929304, -949080857360020998096495], ![-13287132003040293973350930, -46651307764449403999033, 556714506897699688505128], ![3011590728515441373203246, 10573737500642650110306, -126181951606977930928337]]]
  hmulB := by decide  
  f := ![![![-400435838083, -783147639358, -443357093747]], ![![-6206999312458, -11824153727369, -5482033475506]], ![![-2311457696509, -4422072041222, -2124482940126]]]
  g := ![![![878265914144542595200162, 296773209120029747359726, -949080857360020998096495], ![-515175679212506146681154, -174082060020974668010765, 556714506897699688505128], ![116766981672043505088855, 39456514606769654143796, -126181951606977930928337]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [8, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[37, 108], [83], [80, 100], [87, 20], [21], [31, 1]], ![[6, 1], [83], [19, 9], [53, 89], [21], [62, 108]]]
 h' := ![![[31, 108], [77, 33], [14, 65], [67, 10], [78, 42], [79, 81], [0, 1]], ![[0, 1], [10, 76], [67, 44], [50, 99], [72, 67], [83, 28], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [56, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [8, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305, 1454, 3768]
  a := ![-1, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2659, -1162, 3768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22891787226517, 44113712626182, 22448430132770]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![22891787226517, 44113712626182, 22448430132770]] 
 ![![109, 0, 0], ![89, 1, 0], ![8, 0, 1]] where
  M :=![![![22891787226517, 44113712626182, 22448430132770], ![314278021858780, 605767823039179, 308795988383274], ![572695116501008, 1103625963293908, 561654110412997]]]
  hmulB := by decide  
  f := ![![![563282374897322709211485329, 1977692358562570523122294, -23600839482393547021484038]], ![![456896510212001940013957961, 1604170087986320438319953, -19143402453422822855506636]], ![![42028884139112337202372136, 147564004671698740338948, -1760958610452025646568843]]]
  g := ![![![-37457028234549, 44113712626182, 22448430132770], ![-514398404914627, 605767823039179, 308795988383274], ![-937094022935420, 1103625963293908, 561654110412997]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![22651758625033526023387543, 79530643842528526929304, -949080857360020998096495]] ![![22891787226517, 44113712626182, 22448430132770]]
  ![![109, 0, 0]] where
 M := ![![![-109, -218, -109]]]
 hmul := by decide  
 g := ![![![![-1, -2, -1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6248807, -10581616, 314498]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-6248807, -10581616, 314498]] 
 ![![113, 0, 0], ![0, 113, 0], ![106, 32, 1]] where
  M :=![![![-6248807, -10581616, 314498], ![4402972, -9282471, -74071312], ![-148771620, -253329788, 1299145]]]
  hmulB := by decide  
  f := ![![![-166163973819727, -583404054408, 6962066360750]], ![![97468929050500, 342214783865, -4083828380856]], ![![-128464312254498, -451040011220, 5382496857437]]]
  g := ![![![-350315, -182704, 314498], ![69521788, 20893801, -74071312], ![-2535230, -2609756, 1299145]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [103, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 112], [0, 1]]
 g := ![![[29, 99], [63], [44], [95], [32, 88], [64, 1]], ![[37, 14], [63], [44], [95], [14, 25], [15, 112]]]
 h' := ![![[64, 112], [54, 41], [92, 17], [68, 65], [94, 78], [75, 38], [0, 1]], ![[0, 1], [79, 72], [50, 96], [47, 48], [1, 35], [21, 75], [64, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [94, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [103, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![983, 3836, 10643]
  a := ![0, 3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9975, -2980, 10643]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1015199, -1954392, -995410]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1015199, -1954392, -995410]] 
 ![![113, 0, 0], ![2, 1, 0], ![96, 0, 1]] where
  M :=![![![-1015199, -1954392, -995410], ![-13935740, -26859431, -13680744], ![-25370668, -48896228, -24905039]]]
  hmulB := by decide  
  f := ![![![-1601260823, -2414667808, 1390415938]], ![![143923022, 217032905, -124972060]], ![![-1684134692, -2539639868, 1462377449]]]
  g := ![![![871265, -1954392, -995410], ![11974642, -26859431, -13680744], ![21799164, -48896228, -24905039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-6248807, -10581616, 314498]] ![![-1015199, -1954392, -995410]]
  ![![113, 0, 0]] where
 M := ![![![145827407628769, 281051037317296, 143151919622752]]]
 hmul := by decide  
 g := ![![![![1290508032113, 2487177321392, 1266831147104]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5251526624197, 10209126255922, 5543148521420]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![5251526624197, 10209126255922, 5543148521420]] 
 ![![127, 0, 0], ![0, 127, 0], ![89, 20, 1]] where
  M :=![![![5251526624197, 10209126255922, 5543148521420], ![77604079299880, 148496217394199, 71463883791454], ![131841470540068, 256105327184968, 138287091138277]]]
  hmulB := by decide  
  f := ![![![-17581327623323884292370013, -61728289120302723290458, 736636027713585789407496]], ![![10312904387990201051704944, 36208752681871930119433, -432098023842119063033206]], ![![-10715098730859315674737903, -37620862689209429532426, 448949472688731721653645]]]
  g := ![![![-3843218045529, -792549954114, 5543148521420], ![-49469933686138, -10084893373503, 71463883791454], ![-95871729454855, -19760917288036, 138287091138277]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [68, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 126], [0, 1]]
 g := ![![[33, 99], [78, 107], [8, 74], [15, 104], [95, 120], [42, 1]], ![[0, 28], [0, 20], [68, 53], [65, 23], [55, 7], [84, 126]]]
 h' := ![![[42, 126], [30, 90], [91, 19], [123, 70], [17, 55], [65, 45], [0, 1]], ![[0, 1], [0, 37], [0, 108], [15, 57], [41, 72], [50, 82], [42, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [86, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [68, 85, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6314, 21248, 47138]
  a := ![2, -8, -46]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32984, -7256, 47138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![437195722479985697604368921, 1535000344547474302105450, -18317963651037470081777509]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![437195722479985697604368921, 1535000344547474302105450, -18317963651037470081777509]] 
 ![![127, 0, 0], ![114, 1, 0], ![14, 0, 1]] where
  M :=![![![437195722479985697604368921, 1535000344547474302105450, -18317963651037470081777509], ![-256451491114524581144885126, -900404800366110056185845, 10745002411832320114738150], ![58125932125739580393031318, 204080967064443086975782, -2435405144913584358291295]]]
  hmulB := by decide  
  f := ![![![292301155764025, 563306888229288, 286758007242605]], ![![293991683925160, 566573113983895, 288453236561118]], ![![89803122845836, 173064391867702, 88103192369945]]]
  g := ![![![4083914758394474081175061, 1535000344547474302105450, -18317963651037470081777509], ![-2395554154633389892488448, -900404800366110056185845, 10745002411832320114738150], ![542963574088057082628900, 204080967064443086975782, -2435405144913584358291295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![5251526624197, 10209126255922, 5543148521420]] ![![437195722479985697604368921, 1535000344547474302105450, -18317963651037470081777509]]
  ![![127, 0, 0]] where
 M := ![![![-3175, 0, 127]]]
 hmul := by decide  
 g := ![![![![-25, 0, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157398908162539, 303351705252612, 154507075311176]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![157398908162539, 303351705252612, 154507075311176]] 
 ![![131, 0, 0], ![0, 131, 0], ![15, 70, 1]] where
  M :=![![![157398908162539, 303351705252612, 154507075311176], ![2163099054356464, 4168920420883375, 2123461936768284], ![3937909722914216, 7589455076685040, 3865568715630763]]]
  hmulB := by decide  
  f := ![![![5119230782386181088122185, 17973691440086208315236, -214489480503357467172968]], ![![-3002852727047004540421552, -10543058254311915713811, 125815840080603458206652]], ![![-1013210828368928852342875, -3557397501108297023042, 42452288919064747655283]]]
  g := ![![![-16490131461871, -80245370736868, 154507075311176], ![-226632290054716, -1102850497350355, 2123461936768284], ![-412561992454559, -2007636297843270, 3865568715630763]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [120, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 130], [0, 1]]
 g := ![![[27, 55], [50, 12], [75], [13], [91], [46], [1]], ![[118, 76], [77, 119], [75], [13], [91], [46], [1]]]
 h' := ![![[35, 130], [26, 29], [51, 76], [55, 59], [82, 119], [103, 22], [11, 35], [0, 1]], ![[0, 1], [124, 102], [91, 55], [24, 72], [55, 12], [87, 109], [57, 96], [35, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [95, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [120, 96, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1535, 2, 146]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -78, 146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205864030539906141961679, -722791513183557892658, 8625449963451325211289]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-205864030539906141961679, -722791513183557892658, 8625449963451325211289]] 
 ![![131, 0, 0], ![34, 1, 0], ![92, 0, 1]] where
  M :=![![![-205864030539906141961679, -722791513183557892658, 8625449963451325211289], ![120756299488318552958046, 423977069742105216599, -5059540592284905248606], ![-27369981111472460919790, -96096389502739001214, 1146768582925663109257]]]
  hmulB := by decide  
  f := ![![![2937018850741, 5662445369740, 2891832851363]], ![![1071330540796, 2065088513163, 1053125454462]], ![![2623635906426, 5058223882386, 2583126943579]]]
  g := ![![![-7441454318543412924045, -722791513183557892658, 8625449963451325211289], ![4365029111506093576072, 423977069742105216599, -5059540592284905248606], ![-989354301507941533818, -96096389502739001214, 1146768582925663109257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![157398908162539, 303351705252612, 154507075311176]] ![![-205864030539906141961679, -722791513183557892658, 8625449963451325211289]]
  ![![131, 0, 0]] where
 M := ![![![131, 262, 131]]]
 hmul := by decide  
 g := ![![![![1, 2, 1]]]]
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
  g := ![1, 1, 2, 2, 1, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB137I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
  β := ![I97N1, I101N1, I107N1, I109N1, I113N1, I127N1, I131N1]
  Il := ![[], [], [I97N1], [I101N1], [], [I107N1], [I109N1], [I113N1], [I127N1], [I131N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
