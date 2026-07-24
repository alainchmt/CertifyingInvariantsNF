
import IdealArithmetic.Examples.NF3_1_599427_1.RI3_1_599427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5188312081241, 978657364504, 184601508564]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![5188312081241, 978657364504, 184601508564]] 
 ![![83, 0, 0], ![0, 83, 0], ![28, 32, 1]] where
  M :=![![![5188312081241, 978657364504, 184601508564], ![27505624776036, 5188312081241, 978657364504], ![145819947311096, 27505624776036, 5188312081241]]]
  hmulB := by decide  
  f := ![![![-387061, 461480, -73276]], ![![-10918124, -387061, 461480]], ![![-3511532, -125092, 148537]]]
  g := ![![![234576403, -59380613368, 184601508564], ![1243597228, -314803898589, 978657364504], ![6592879956, -1668920021972, 5188312081241]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [82, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 82], [0, 1]]
 g := ![![[60, 75], [15, 63], [65], [78], [71, 31], [1]], ![[78, 8], [60, 20], [65], [78], [22, 52], [1]]]
 h' := ![![[60, 82], [15, 18], [47, 35], [56, 27], [71, 59], [1, 60], [0, 1]], ![[0, 1], [16, 65], [72, 48], [16, 56], [42, 24], [32, 23], [60, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [61, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [82, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![380, 126, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 10, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![387061, -461480, 73276]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![387061, -461480, 73276]] 
 ![![83, 0, 0], ![51, 1, 0], ![55, 0, 1]] where
  M :=![![![387061, -461480, 73276], ![10918124, 387061, -461480], ![-68760520, 10918124, 387061]]]
  hmulB := by decide  
  f := ![![![-5188312081241, -978657364504, -184601508564]], ![![-3519392059269, -663853465915, -125220895196]], ![![-5194904961197, -979900961732, -184836084967]]]
  g := ![![![239667, -461480, 73276], ![199511, 387061, -461480], ![-7793653, 10918124, 387061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![5188312081241, 978657364504, 184601508564]] ![![387061, -461480, 73276]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, -24, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, -24, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![42, 65, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, -24, 1], ![149, 42, -24], ![-3576, 149, 42]]]
  hmulB := by decide  
  f := ![![![-41, 24, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -65, 89]], ![![0, -1, 1], ![13, 18, -24], ![-60, -29, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [25, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 88], [0, 1]]
 g := ![![[64, 57], [69], [87], [69, 47], [86, 4], [1]], ![[0, 32], [69], [87], [74, 42], [5, 85], [1]]]
 h' := ![![[2, 88], [53, 18], [49, 46], [55, 49], [75, 74], [64, 2], [0, 1]], ![[0, 1], [0, 71], [52, 43], [64, 40], [45, 15], [68, 87], [2, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [76, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [25, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1849, 1171, 259]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -176, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![24, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![24, 1, 0]] 
 ![![89, 0, 0], ![24, 1, 0], ![47, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![24, 1, 0], ![0, 24, 1], ![149, 0, 24]]]
  hmulB := by decide  
  f := ![![![529, 22, 0], ![-1958, 0, 0]], ![![120, 5, 0], ![-444, 0, 0]], ![![247, 10, 0], ![-914, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 89, 0], ![-47, 0, 89]], ![![0, 1, 0], ![-7, 24, 1], ![-11, 0, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![42, -24, 1]] ![![89, 0, 0], ![24, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2136, 89, 0]], ![![3738, -2136, 89], ![1157, -534, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![24, 1, 0]]], ![![![42, -24, 1]], ![![13, -6, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![159892, 30160, 5689]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![159892, 30160, 5689]] 
 ![![97, 0, 0], ![46, 1, 0], ![18, 0, 1]] where
  M :=![![![159892, 30160, 5689], ![847661, 159892, 30160], ![4493840, 847661, 159892]]]
  hmulB := by decide  
  f := ![![![-4096, 709, 12]], ![![-1924, 294, 13]], ![![329, 150, -40]]]
  g := ![![![-13710, 30160, 5689], ![-72683, 159892, 30160], ![-385326, 847661, 159892]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1850472037297, 349049567326, 65840281828]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![1850472037297, 349049567326, 65840281828]] 
 ![![97, 0, 0], ![58, 1, 0], ![31, 0, 1]] where
  M :=![![![1850472037297, 349049567326, 65840281828], ![9810201992372, 1850472037297, 349049567326], ![52008385531574, 9810201992372, 1850472037297]]]
  hmulB := by decide  
  f := ![![![6628937, 1658194, -548640]], ![![3120938, 1059837, -310958]], ![![4665649, -312818, -106999]]]
  g := ![![![-210674758807, 349049567326, 65840281828], ![-1116883636680, 1850472037297, 349049567326], ![-5921113022497, 9810201992372, 1850472037297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31316029898460, 5907058559173, 1114232581034]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![31316029898460, 5907058559173, 1114232581034]] 
 ![![97, 0, 0], ![90, 1, 0], ![48, 0, 1]] where
  M :=![![![31316029898460, 5907058559173, 1114232581034], ![166020654574066, 31316029898460, 5907058559173], ![880151725316777, 166020654574066, 31316029898460]]]
  hmulB := by decide  
  f := ![![![-61835818, 8290664, 636289]], ![![-56396047, 7054886, 675842]], ![![-17864024, 5079989, -322618]]]
  g := ![![![-5709303137286, 5907058559173, 1114232581034], ![-30267637599254, 31316029898460, 5907058559173], ![-160462645582219, 166020654574066, 31316029898460]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![159892, 30160, 5689]] ![![1850472037297, 349049567326, 65840281828]]
  ![![887627072366555930, 167430709198370620, 31582004712777369]] where
 M := ![![![887627072366555930, 167430709198370620, 31582004712777369]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![887627072366555930, 167430709198370620, 31582004712777369]] ![![31316029898460, 5907058559173, 1114232581034]]
  ![![97, 0, 0]] where
 M := ![![![83390867810740750719126120828433, 15729795285529608225438745403444, 2967069011515922137231328880620]]]
 hmul := by decide  
 g := ![![![![859699668151966502259032173489, 162162837995150600262255107252, 30588340324906413785889988460]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![33, 29, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![33, 29, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![33, 29, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![33, 29, 1], ![149, 33, 29], ![4321, 149, 33]]]
  hmulB := by decide  
  f := ![![![-32, -29, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -29, 101]], ![![0, 0, 1], ![-8, -8, 29], ![32, -8, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [61, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 100], [0, 1]]
 g := ![![[7, 64], [20], [57, 78], [52], [56], [78, 1]], ![[50, 37], [20], [81, 23], [52], [56], [55, 100]]]
 h' := ![![[78, 100], [23, 8], [58, 11], [90, 49], [38, 31], [90, 64], [0, 1]], ![[0, 1], [41, 93], [7, 90], [74, 52], [32, 70], [32, 37], [78, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [63, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [61, 23, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2387, 44, 106]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -30, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-29, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-29, 1, 0]] 
 ![![101, 0, 0], ![72, 1, 0], ![68, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-29, 1, 0], ![0, -29, 1], ![149, 0, -29]]]
  hmulB := by decide  
  f := ![![![320, -11, 0], ![1111, 0, 0]], ![![262, -9, 0], ![910, 0, 0]], ![![212, -7, 0], ![736, 1, 0]]]
  g := ![![![1, 0, 0], ![-72, 101, 0], ![-68, 0, 101]], ![![-1, 1, 0], ![20, -29, 1], ![21, 0, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![33, 29, 1]] ![![101, 0, 0], ![-29, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2929, 101, 0]], ![![3333, 2929, 101], ![-808, -808, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-29, 1, 0]]], ![![![33, 29, 1]], ![![-8, -8, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [21, 5, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 19, 84], [96, 83, 19], [0, 1]]
 g := ![![[78, 81, 50], [63, 49, 41], [69, 87, 60], [42, 26], [100, 9], [1]], ![[45, 65, 71, 84], [90, 76, 28, 80], [47, 83, 15, 53], [11, 46], [38, 92], [75, 34, 0, 42]], ![[64, 79, 89, 32], [77, 6, 71, 64], [63, 59, 38, 81], [66, 25], [68, 2], [18, 26, 50, 61]]]
 h' := ![![[10, 19, 84], [16, 44, 87], [96, 46, 91], [63, 100, 67], [92, 36, 51], [82, 98, 3], [0, 1]], ![[96, 83, 19], [54, 11, 102], [100, 75, 87], [4, 18, 56], [21, 37, 47], [43, 79, 35], [10, 19, 84]], ![[0, 1], [23, 48, 17], [36, 85, 28], [46, 88, 83], [14, 30, 5], [0, 29, 65], [96, 83, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 82], []]
 b := ![[], [50, 68, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [21, 5, 100, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-691233, 136990, 3502]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6711, 1330, 34]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-22, 37, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-22, 37, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![85, 37, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-22, 37, 1], ![149, -22, 37], ![5513, 149, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -37, 107]], ![![-1, 0, 1], ![-28, -13, 37], ![69, 9, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [99, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 106], [0, 1]]
 g := ![![[42, 40], [58, 37], [33], [12, 41], [40], [15, 1]], ![[0, 67], [78, 70], [33], [92, 66], [40], [30, 106]]]
 h' := ![![[15, 106], [36, 19], [64, 12], [96, 56], [61, 24], [13, 19], [0, 1]], ![[0, 1], [0, 88], [30, 95], [80, 51], [100, 83], [84, 88], [15, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [75, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [99, 92, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397, 57, -91]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76, 32, -91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-37, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-37, 1, 0]] 
 ![![107, 0, 0], ![70, 1, 0], ![22, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-37, 1, 0], ![0, -37, 1], ![149, 0, -37]]]
  hmulB := by decide  
  f := ![![![3516, -95, 0], ![10165, 0, 0]], ![![2258, -61, 0], ![6528, 0, 0]], ![![716, -19, 0], ![2070, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 107, 0], ![-22, 0, 107]], ![![-1, 1, 0], ![24, -37, 1], ![9, 0, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-22, 37, 1]] ![![107, 0, 0], ![-37, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3959, 107, 0]], ![![-2354, 3959, 107], ![963, -1391, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-37, 1, 0]]], ![![![-22, 37, 1]], ![![9, -13, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [18, 12, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 61, 48], [41, 47, 61], [0, 1]]
 g := ![![[99, 69, 64], [66, 49], [56, 55, 1], [30, 89, 12], [64, 9], [1]], ![[100, 14, 106, 63], [47, 12], [101, 42, 26, 46], [61, 27, 34, 66], [69, 1], [50, 94, 0, 66]], ![[81, 84, 1, 100], [36, 16], [45, 20, 89, 64], [39, 91, 11, 9], [107, 16], [83, 70, 64, 43]]]
 h' := ![![[71, 61, 48], [86, 69, 101], [82, 107, 102], [5, 83, 108], [44, 47, 11], [91, 97, 3], [0, 1]], ![[41, 47, 61], [62, 98, 102], [6, 55, 11], [37, 12, 13], [54, 4, 48], [36, 33, 1], [71, 61, 48]], ![[0, 1], [1, 51, 15], [39, 56, 105], [19, 14, 97], [10, 58, 50], [65, 88, 105], [41, 47, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 29], []]
 b := ![[], [37, 28, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [18, 12, 106, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1661487, 181921, 48069]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15243, 1669, 441]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-8, 52, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-8, 52, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![105, 52, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-8, 52, 1], ![149, -8, 52], ![7748, 149, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -52, 113]], ![![-1, 0, 1], ![-47, -24, 52], ![76, 5, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [39, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 112], [0, 1]]
 g := ![![[68, 50], [36], [7], [30], [8, 87], [60, 1]], ![[17, 63], [36], [7], [30], [30, 26], [7, 112]]]
 h' := ![![[60, 112], [4, 29], [74, 107], [11, 32], [27, 97], [33, 58], [0, 1]], ![[0, 1], [49, 84], [53, 6], [10, 81], [84, 16], [10, 55], [60, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [89, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [39, 53, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-907, 302, -42]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 22, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-52, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-52, 1, 0]] 
 ![![113, 0, 0], ![61, 1, 0], ![8, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-52, 1, 0], ![0, -52, 1], ![149, 0, -52]]]
  hmulB := by decide  
  f := ![![![3745, -72, 0], ![8136, 0, 0]], ![![2029, -39, 0], ![4408, 0, 0]], ![![336, -6, 0], ![730, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 113, 0], ![-8, 0, 113]], ![![-1, 1, 0], ![28, -52, 1], ![5, 0, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-8, 52, 1]] ![![113, 0, 0], ![-52, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5876, 113, 0]], ![![-904, 5876, 113], ![565, -2712, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-52, 1, 0]]], ![![![-8, 52, 1]], ![![5, -24, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [43, 122, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 3, 81], [16, 123, 46], [0, 1]]
 g := ![![[24, 50, 94], [65, 97, 2], [36, 89, 13], [69, 96, 115], [25], [1]], ![[124, 73, 26, 71], [10, 56, 4, 120], [9, 64, 57, 69], [34, 13, 33, 25], [109, 32, 104, 47], [73, 44, 121, 73]], ![[80, 22, 6, 5], [35, 39, 43, 105], [7, 20, 92, 80], [70, 50, 16, 93], [1, 11, 73, 80], [56, 33, 8, 54]]]
 h' := ![![[111, 3, 81], [126, 32, 100], [103, 120, 111], [81, 79, 93], [68, 69, 78], [84, 5], [0, 1]], ![[16, 123, 46], [53, 58, 33], [33, 107, 5], [113, 1, 58], [10, 91, 70], [4, 15, 24], [111, 3, 81]], ![[0, 1], [56, 37, 121], [13, 27, 11], [90, 47, 103], [17, 94, 106], [37, 107, 103], [16, 123, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 25], []]
 b := ![[], [8, 99, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [43, 122, 0, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177800, 1016, 2032]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1400, 8, 16]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96, -3, 4]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-96, -3, 4]] 
 ![![131, 0, 0], ![0, 131, 0], ![107, 32, 1]] where
  M :=![![![-96, -3, 4], ![596, -96, -3], ![-447, 596, -96]]]
  hmulB := by decide  
  f := ![![![84, 16, 3]], ![![447, 84, 16]], ![![196, 37, 7]]]
  g := ![![![-4, -1, 4], ![7, 0, -3], ![75, 28, -96]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [87, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 130], [0, 1]]
 g := ![![[68, 121], [64, 35], [11], [45], [21], [48], [1]], ![[16, 10], [115, 96], [11], [45], [21], [48], [1]]]
 h' := ![![[110, 130], [65, 11], [83, 64], [75, 50], [45, 62], [118, 26], [44, 110], [0, 1]], ![[0, 1], [96, 120], [49, 67], [73, 81], [53, 69], [96, 105], [92, 21], [110, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [87, 21, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5827, 346, 150]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-167, -34, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84, -16, -3]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-84, -16, -3]] 
 ![![131, 0, 0], ![99, 1, 0], ![24, 0, 1]] where
  M :=![![![-84, -16, -3], ![-447, -84, -16], ![-2384, -447, -84]]]
  hmulB := by decide  
  f := ![![![96, 3, -4]], ![![68, 3, -3]], ![![21, -4, 0]]]
  g := ![![![12, -16, -3], ![63, -84, -16], ![335, -447, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-96, -3, 4]] ![![-84, -16, -3]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38801816, -26099954, 6303743]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-38801816, -26099954, 6303743]] 
 ![![137, 0, 0], ![0, 137, 0], ![25, 132, 1]] where
  M :=![![![-38801816, -26099954, 6303743], ![939257707, -38801816, -26099954], ![-3888893146, 939257707, -38801816]]]
  hmulB := by decide  
  f := ![![![-189928203443382, -35825646591101, -6757695436492]], ![![-1006896620037308, -189928203443382, -35825646591101]], ![![-1043770658927615, -196883654301761, -37137634594022]]]
  g := ![![![-1433543, -6264190, 6303743], ![11618661, 24864176, -26099954], ![-21305458, 44241587, -38801816]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [30, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 136], [0, 1]]
 g := ![![[128, 32], [39], [101], [82, 14], [14], [16], [1]], ![[0, 105], [39], [101], [26, 123], [14], [16], [1]]]
 h' := ![![[133, 136], [52, 13], [20, 83], [6, 52], [72, 98], [9, 39], [107, 133], [0, 1]], ![[0, 1], [0, 124], [99, 54], [72, 85], [91, 39], [127, 98], [123, 4], [133, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [58, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [30, 4, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47, 119, 31]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -29, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189928203443382, -35825646591101, -6757695436492]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-189928203443382, -35825646591101, -6757695436492]] 
 ![![137, 0, 0], ![5, 1, 0], ![112, 0, 1]] where
  M :=![![![-189928203443382, -35825646591101, -6757695436492], ![-1006896620037308, -189928203443382, -35825646591101], ![-5338021342074049, -1006896620037308, -189928203443382]]]
  hmulB := by decide  
  f := ![![![-38801816, -26099954, 6303743]], ![![5439771, -1235778, 39553]], ![![-60107274, -14481293, 4870200]]]
  g := ![![![5445707433571, -35825646591101, -6757695436492], ![28870195732722, -189928203443382, -35825646591101], ![153054164553075, -1006896620037308, -189928203443382]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-38801816, -26099954, 6303743]] ![![-189928203443382, -35825646591101, -6757695436492]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB220I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB220I2 : PrimesBelowBoundCertificateInterval O 79 137 220 where
  m := 11
  g := ![2, 2, 3, 2, 1, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB220I2_primes
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
    · exact ![I127N0]
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
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
