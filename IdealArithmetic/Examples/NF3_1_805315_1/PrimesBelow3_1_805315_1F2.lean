
import IdealArithmetic.Examples.NF3_1_805315_1.RI3_1_805315_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2278770269, -847127022, -226957064]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2278770269, -847127022, -226957064]] 
 ![![83, 0, 0], ![0, 83, 0], ![36, 8, 1]] where
  M :=![![![-2278770269, -847127022, -226957064], ![49930554080, -9253738019, -4235635110], ![176381834024, -12886318778, -8406610997]]]
  hmulB := by decide  
  f := ![![![279648572760642161, -50564171847929074, 17926743918018388]], ![![-3943883661964045360, 713106486699209563, -252820859239645370]], ![![-115311158281831804, 20849787166040190, -7391969088209185]]]
  g := ![![![70984145, 11669030, -226957064], ![2438715880, 296763167, -4235635110], ![5771323252, 655018906, -8406610997]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [34, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 82], [0, 1]]
 g := ![![[71, 21], [65, 17], [1], [70], [50, 49], [1]], ![[7, 62], [29, 66], [1], [70], [39, 34], [1]]]
 h' := ![![[76, 82], [31, 41], [59, 10], [50, 1], [43, 53], [49, 76], [0, 1]], ![[0, 1], [76, 42], [72, 73], [43, 82], [4, 30], [15, 7], [76, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [64, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [34, 7, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4322, -2602, 2144]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-982, -238, 2144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52579911770807, -1910452454132, -1866758698376]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![52579911770807, -1910452454132, -1866758698376]] 
 ![![83, 0, 0], ![43, 1, 0], ![20, 0, 1]] where
  M :=![![![52579911770807, -1910452454132, -1866758698376], ![410686913642720, 266974460523, -9552262270660], ![338162157180496, 30555166466980, 2177426914655]]]
  hmulB := by decide  
  f := ![![![292452281192136943700471365, -52879252189765873717520020, 18747519793920458095577768]], ![![101819201645775756603532045, -18410262418333844955298913, 6527073375780124452075228]], ![![220570746705105195759870524, -39882117154837303866612804, 14139586885619258725212367]]]
  g := ![![![2073066762241, -1910452454132, -1866758698376], ![7111472978957, 266974460523, -9552262270660], ![-12280223363768, 30555166466980, 2177426914655]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2278770269, -847127022, -226957064]] ![![52579911770807, -1910452454132, -1866758698376]]
  ![![83, 0, 0]] where
 M := ![![![-544469812168078589540667, -2807389898255851497718, 11851711292338853784744]]]
 hmul := by decide  
 g := ![![![![-6559877255037091440249, -33823974677781343346, 142791702317335587768]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![15, 3, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![15, 3, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![15, 3, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![15, 3, 1], ![-220, 45, 15], ![-616, 37, 42]]]
  hmulB := by decide  
  f := ![![![-14, -3, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -3, 89]], ![![0, 0, 1], ![-5, 0, 15], ![-14, -1, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [75, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 88], [0, 1]]
 g := ![![[43, 67], [21], [71], [42, 67], [30, 85], [1]], ![[60, 22], [21], [71], [59, 22], [25, 4], [1]]]
 h' := ![![[68, 88], [63, 44], [83, 56], [54, 58], [64, 44], [14, 68], [0, 1]], ![[0, 1], [29, 45], [64, 33], [82, 31], [30, 45], [10, 21], [68, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [15, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [75, 21, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-869, -1758, 1461]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-256, -69, 1461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-15, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-15, 1, 0]] 
 ![![89, 0, 0], ![74, 1, 0], ![47, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-15, 1, 0], ![0, -14, 5], ![-220, 27, -15]]]
  hmulB := by decide  
  f := ![![![391, -26, 0], ![2314, 0, 0]], ![![346, -23, 0], ![2048, 0, 0]], ![![223, -12, -1], ![1320, 18, 0]]]
  g := ![![![1, 0, 0], ![-74, 89, 0], ![-47, 0, 89]], ![![-1, 1, 0], ![9, -14, 5], ![-17, 27, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![15, 3, 1]] ![![89, 0, 0], ![-15, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1335, 89, 0]], ![![1335, 267, 89], ![-445, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-15, 1, 0]]], ![![![15, 3, 1]], ![![-5, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42574179649, -7697976481, 2729198324]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![42574179649, -7697976481, 2729198324]] 
 ![![97, 0, 0], ![0, 97, 0], ![13, 19, 1]] where
  M :=![![![42574179649, -7697976481, 2729198324], ![-600423631280, 108564557916, -38489882405], ![1813639552076, -327930091243, 116262534397]]]
  hmulB := by decide  
  f := ![![![601621, -32575, -24907]], ![![5479540, -103443, -162875]], ![![1216525, -22397, -35972]]]
  g := ![![![73140221, -613945821, 2729198324], ![-1031496495, 8658477563, -38489882405], ![3115738195, -26153796338, 116262534397]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [73, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 96], [0, 1]]
 g := ![![[83, 4], [22], [22], [4], [47], [52, 1]], ![[0, 93], [22], [22], [4], [47], [7, 96]]]
 h' := ![![[52, 96], [7, 95], [35, 64], [34, 64], [36, 95], [84, 12], [0, 1]], ![[0, 1], [0, 2], [65, 33], [64, 33], [29, 2], [29, 85], [52, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [93, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [73, 45, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1333, -44, 110]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -22, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-601621, 32575, 24907]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-601621, 32575, 24907]] 
 ![![97, 0, 0], ![2, 1, 0], ![57, 0, 1]] where
  M :=![![![-601621, 32575, 24907], ![-5479540, 103443, 162875], ![-6070592, -216383, 70868]]]
  hmulB := by decide  
  f := ![![![-42574179649, 7697976481, -2729198324]], ![![5312116206, -960501082, 340530781]], ![![-43715131877, 7904275780, -2802338545]]]
  g := ![![![-21510, 32575, 24907], ![-154333, 103443, 162875], ![-99766, -216383, 70868]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![42574179649, -7697976481, 2729198324]] ![![-601621, 32575, 24907]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, -44, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, -44, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![1, 57, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, -44, 1], ![-220, -16, -220], ![9724, -1232, 28]]]
  hmulB := by decide  
  f := ![![![0, 44, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -57, 101]], ![![0, -1, 1], ![0, 124, -220], ![96, -28, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [19, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 100], [0, 1]]
 g := ![![[1, 16], [52], [54, 47], [45], [6], [82, 1]], ![[0, 85], [52], [70, 54], [45], [6], [63, 100]]]
 h' := ![![[82, 100], [76, 4], [85, 70], [75, 42], [18, 67], [58, 39], [0, 1]], ![[0, 1], [0, 97], [68, 31], [85, 59], [58, 34], [24, 62], [82, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [74, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [19, 19, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4317, -4174, 3056]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73, -1766, 3056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![73, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![0, 19, 5], ![-220, 27, 18]]]
  hmulB := by decide  
  f := ![![![1207, 67, 0], ![-6767, 0, 0]], ![![198, 11, 0], ![-1110, 0, 0]], ![![887, 34, -4], ![-4973, 81, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-73, 0, 101]], ![![0, 1, 0], ![-7, 19, 5], ![-20, 27, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, -44, 1]] ![![101, 0, 0], ![18, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1818, 101, 0]], ![![101, -4444, 101], ![-202, -808, -202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![18, 1, 0]]], ![![![1, -44, 1]], ![![-2, -8, -2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![20, 39, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![20, 39, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![20, 39, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![20, 39, 1], ![-220, 86, 195], ![-8536, 1009, 47]]]
  hmulB := by decide  
  f := ![![![-19, -39, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -39, 103]], ![![0, 0, 1], ![-40, -73, 195], ![-92, -8, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [82, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 102], [0, 1]]
 g := ![![[40, 49], [29, 98], [13, 49], [76], [97], [16, 1]], ![[0, 54], [52, 5], [76, 54], [76], [97], [32, 102]]]
 h' := ![![[16, 102], [94, 7], [67, 60], [70, 7], [88, 30], [27, 71], [0, 1]], ![[0, 1], [0, 96], [100, 43], [79, 96], [53, 73], [30, 32], [16, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [57, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [82, 87, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4274, -2762, 1424]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-318, -566, 1424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![11, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![11, 1, 0]] 
 ![![103, 0, 0], ![11, 1, 0], ![56, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![11, 1, 0], ![0, 12, 5], ![-220, 27, 11]]]
  hmulB := by decide  
  f := ![![![738, 67, 0], ![-6901, 0, 0]], ![![66, 6, 0], ![-617, 0, 0]], ![![388, 28, -3], ![-3628, 62, 0]]]
  g := ![![![1, 0, 0], ![-11, 103, 0], ![-56, 0, 103]], ![![0, 1, 0], ![-4, 12, 5], ![-11, 27, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![20, 39, 1]] ![![103, 0, 0], ![11, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1133, 103, 0]], ![![2060, 4017, 103], ![0, 515, 206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![11, 1, 0]]], ![![![20, 39, 1]], ![![0, 5, 2]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![10, 17, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![10, 17, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![10, 17, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![10, 17, 1], ![-220, 54, 85], ![-3696, 415, 37]]]
  hmulB := by decide  
  f := ![![![-9, -17, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -17, 107]], ![![0, 0, 1], ![-10, -13, 85], ![-38, -2, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [35, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 106], [0, 1]]
 g := ![![[30, 52], [24, 64], [76], [66, 3], [10], [20, 1]], ![[0, 55], [20, 43], [76], [19, 104], [10], [40, 106]]]
 h' := ![![[20, 106], [16, 42], [25, 99], [44, 41], [18, 18], [49, 44], [0, 1]], ![[0, 1], [0, 65], [79, 8], [8, 66], [57, 89], [73, 63], [20, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [33, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [35, 87, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-423993, -199024, 186356]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21379, -31468, 186356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![22, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![22, 1, 0]] 
 ![![107, 0, 0], ![22, 1, 0], ![70, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![22, 1, 0], ![0, 23, 5], ![-220, 27, 22]]]
  hmulB := by decide  
  f := ![![![1519, 69, 0], ![-7383, 0, 0]], ![![286, 13, 0], ![-1390, 0, 0]], ![![974, 35, -2], ![-4734, 43, 0]]]
  g := ![![![1, 0, 0], ![-22, 107, 0], ![-70, 0, 107]], ![![0, 1, 0], ![-8, 23, 5], ![-22, 27, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![10, 17, 1]] ![![107, 0, 0], ![22, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2354, 107, 0]], ![![1070, 1819, 107], ![0, 428, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![22, 1, 0]]], ![![![10, 17, 1]], ![![0, 4, 1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-52, 26, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-52, 26, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![57, 26, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-52, 26, 1], ![-220, 1, 130], ![-5676, 658, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -26, 109]], ![![-1, 0, 1], ![-70, -31, 130], ![-39, 12, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [52, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 108], [0, 1]]
 g := ![![[30, 88], [71], [56, 104], [95, 9], [87], [75, 1]], ![[90, 21], [71], [8, 5], [7, 100], [87], [41, 108]]]
 h' := ![![[75, 108], [103, 57], [31, 17], [74, 39], [85, 3], [24, 14], [0, 1]], ![[0, 1], [18, 52], [107, 92], [56, 70], [92, 106], [93, 95], [75, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [77, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [52, 34, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3985, -1332, 1567]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-856, -386, 1567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-21, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-21, 1, 0]] 
 ![![109, 0, 0], ![88, 1, 0], ![25, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-21, 1, 0], ![0, -20, 5], ![-220, 27, -21]]]
  hmulB := by decide  
  f := ![![![925, -44, 0], ![4796, 0, 0]], ![![736, -35, 0], ![3816, 0, 0]], ![![211, -6, -1], ![1094, 22, 0]]]
  g := ![![![1, 0, 0], ![-88, 109, 0], ![-25, 0, 109]], ![![-1, 1, 0], ![15, -20, 5], ![-19, 27, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-52, 26, 1]] ![![109, 0, 0], ![-21, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2289, 109, 0]], ![![-5668, 2834, 109], ![872, -545, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-21, 1, 0]]], ![![![-52, 26, 1]], ![![8, -5, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2631980960853713, -475897074286141, 168721936309360]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![2631980960853713, -475897074286141, 168721936309360]] 
 ![![113, 0, 0], ![3, 1, 0], ![88, 0, 1]] where
  M :=![![![2631980960853713, -475897074286141, 168721936309360], ![-37118825988059200, 6711576166920292, -2379485371430705], ![112121121540562860, -20272986203337647, 7187473241206433]]]
  hmulB := by decide  
  f := ![![![1650387301, -34530867, -50173715]], ![![141498931, 1394456, -2859960]], ![![1332948936, -15605365, -36456548]]]
  g := ![![![-95467771783288, -475897074286141, 168721936309360], ![1346381930947628, 6711576166920292, -2379485371430705], ![-4066881106863631, -20272986203337647, 7187473241206433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1548299, -279953, 99253]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1548299, -279953, 99253]] 
 ![![113, 0, 0], ![48, 1, 0], ![72, 0, 1]] where
  M :=![![![1548299, -279953, 99253], ![-21835660, 3948177, -1399765], ![65956792, -11925863, 4228130]]]
  hmulB := by decide  
  f := ![![![-3185, -2449, -736]], ![![80, -1266, -421]], ![![2452, -1859, -673]]]
  g := ![![![69379, -279953, 99253], ![-978452, 3948177, -1399765], ![2955512, -11925863, 4228130]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4350239960244530455889, 786581096259722134728, -278870143978828546998]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-4350239960244530455889, 786581096259722134728, -278870143978828546998]] 
 ![![113, 0, 0], ![61, 1, 0], ![12, 0, 1]] where
  M :=![![![-4350239960244530455889, 786581096259722134728, -278870143978828546998], ![61351431675342280339560, -11093152751413179090107, 3932905481298610673640], ![-185318127512207325708072, 33507975934080953705568, -11879733847672901224835]]]
  hmulB := by decide  
  f := ![![![-1896432379825, -2747285016, 43608178866]], ![![-1108638712565, -7870293995, 23419137042]], ![![-179062176852, -17928353856, -1731977027]]]
  g := ![![![-433497744286209186817, 786581096259722134728, -278870143978828546998], ![6113618440141264396039, -11093152751413179090107, 3932905481298610673640], ![-18466795162115669796900, 33507975934080953705568, -11879733847672901224835]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![2631980960853713, -475897074286141, 168721936309360]] ![![1548299, -279953, 99253]]
  ![![25594977857809465745367, -4627911546517865808126, 1640754355063448030054]] where
 M := ![![![25594977857809465745367, -4627911546517865808126, 1640754355063448030054]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![25594977857809465745367, -4627911546517865808126, 1640754355063448030054]] ![![-4350239960244530455889, 786581096259722134728, -278870143978828546998]]
  ![![113, 0, 0]] where
 M := ![![![-699334819292192714427810573485360721873276711, 126449012890895100633737465547170796973755330, -44830538896171464062156524425314565997447996]]]
 hmul := by decide  
 g := ![![![![-6188803710550378003785934278631510813037847, 1119017813193761952510951022541334486493410, -396730432709481982850942694029332442455292]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5238056987, -484358855, -283312349]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![5238056987, -484358855, -283312349]] 
 ![![127, 0, 0], ![0, 127, 0], ![2, 105, 1]] where
  M :=![![![5238056987, -484358855, -283312349], ![62328716780, -2895735291, -2421794275], ![94093204744, -611945729, -2411376436]]]
  hmulB := by decide  
  f := ![![![-43312607736284263, 7831494075365617, -2776534918969658]], ![![610837682173324760, -110447556473099412, 39157470376828085]], ![![489812875430798666, -88564665866576145, 31399230465988540]]]
  g := ![![![45706155, 230420770, -283312349], ![528915790, 1979469792, -2421794275], ![778865808, 1988839213, -2411376436]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [9, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126], [0, 1]]
 g := ![![[37, 113], [30, 47], [9, 103], [52, 73], [49, 81], [48, 1]], ![[0, 14], [0, 80], [0, 24], [0, 54], [0, 46], [96, 126]]]
 h' := ![![[48, 126], [111, 85], [46, 89], [40, 105], [67, 33], [76, 9], [0, 1]], ![[0, 1], [0, 42], [0, 38], [0, 22], [0, 94], [0, 118], [48, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [82, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [9, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9847, -6110, 6443]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-179, -5375, 6443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43312607736284263, -7831494075365617, 2776534918969658]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![43312607736284263, -7831494075365617, 2776534918969658]] 
 ![![127, 0, 0], ![110, 1, 0], ![98, 0, 1]] where
  M :=![![![43312607736284263, -7831494075365617, 2776534918969658], ![-610837682173324760, 110447556473099412, -39157470376828085], ![1845096233015100692, -333617876469536611, 118279050548465029]]]
  hmulB := by decide  
  f := ![![![-5238056987, 484358855, 283312349]], ![![-5027677050, 442324483, 264457895]], ![![-4782856610, 378575697, 237606194]]]
  g := ![![![4981704991869887, -7831494075365617, 2776534918969658], ![-70256982655788250, 110447556473099412, -39157470376828085], ![212218233786728780, -333617876469536611, 118279050548465029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![5238056987, -484358855, -283312349]] ![![43312607736284263, -7831494075365617, 2776534918969658]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-26, 42, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-26, 42, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![105, 42, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-26, 42, 1], ![-220, 43, 210], ![-9196, 1090, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -42, 131]], ![![-1, 0, 1], ![-170, -67, 210], ![-71, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [58, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 130], [0, 1]]
 g := ![![[125, 61], [121, 58], [61], [4], [44], [60], [1]], ![[0, 70], [0, 73], [61], [4], [44], [60], [1]]]
 h' := ![![[86, 130], [56, 42], [104, 78], [74, 89], [31, 129], [15, 31], [73, 86], [0, 1]], ![[0, 1], [0, 89], [0, 53], [130, 42], [121, 2], [61, 100], [2, 45], [86, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [65, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [58, 45, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65848, -26968, 23150]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19058, -7628, 23150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![52, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![52, 1, 0]] 
 ![![131, 0, 0], ![52, 1, 0], ![130, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![52, 1, 0], ![0, 53, 5], ![-220, 27, 52]]]
  hmulB := by decide  
  f := ![![![1717, 33, 0], ![-4323, 0, 0]], ![![676, 13, 0], ![-1702, 0, 0]], ![![1638, -11, -4], ![-4124, 105, 0]]]
  g := ![![![1, 0, 0], ![-52, 131, 0], ![-130, 0, 131]], ![![0, 1, 0], ![-26, 53, 5], ![-64, 27, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-26, 42, 1]] ![![131, 0, 0], ![52, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![6812, 131, 0]], ![![-3406, 5502, 131], ![-1572, 2227, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![52, 1, 0]]], ![![![-26, 42, 1]], ![![-12, 17, 2]]]]
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
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-54, -55, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-54, -55, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![83, 82, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-54, -55, 1], ![-220, -82, -275], ![12144, -1529, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -82, 137]], ![![-1, -1, 1], ![165, 164, -275], ![105, 5, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [121, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 136], [0, 1]]
 g := ![![[118, 77], [14], [8], [2, 1], [7], [78], [1]], ![[0, 60], [14], [8], [109, 136], [7], [78], [1]]]
 h' := ![![[107, 136], [72, 112], [56, 39], [32, 75], [121, 136], [134, 125], [16, 107], [0, 1]], ![[0, 1], [0, 25], [119, 98], [111, 62], [14, 1], [83, 12], [94, 30], [107, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [131, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [121, 30, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![724, -44, 83]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45, -50, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![1, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![1, 1, 0]] 
 ![![137, 0, 0], ![1, 1, 0], ![27, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![1, 1, 0], ![0, 2, 5], ![-220, 27, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![137, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -2], ![27, 55, 0]]]
  g := ![![![1, 0, 0], ![-1, 137, 0], ![-27, 0, 137]], ![![0, 1, 0], ![-1, 2, 5], ![-2, 27, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-54, -55, 1]] ![![137, 0, 0], ![1, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![137, 137, 0]], ![![-7398, -7535, 137], ![-274, -137, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![1, 1, 0]]], ![![![-54, -55, 1]], ![![-2, -1, -2]]]]
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


lemma PB254I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB254I2 : PrimesBelowBoundCertificateInterval O 79 137 254 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB254I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I109N1, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
