
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-27, 64, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-27, 64, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![112, 64, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-27, 64, 1], ![10, 105, 638], ![8776, 269, -150]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -64, 139]], ![![-1, 0, 1], ![-514, -293, 638], ![184, 71, -150]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [42, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 138], [0, 1]]
 g := ![![[58, 96], [66, 36], [44], [46, 64], [125], [47], [1]], ![[0, 43], [79, 103], [44], [100, 75], [125], [47], [1]]]
 h' := ![![[66, 138], [8, 42], [16, 6], [14, 105], [69, 8], [68, 60], [97, 66], [0, 1]], ![[0, 1], [0, 97], [134, 133], [133, 34], [41, 131], [136, 79], [5, 73], [66, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [50, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [42, 73, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1468, 263, -250]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![212, 117, -250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![57, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![57, 1, 0]] 
 ![![139, 0, 0], ![57, 1, 0], ![11, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![57, 1, 0], ![-2, 59, 10], ![138, 4, 55]]]
  hmulB := by decide  
  f := ![![![4059, -129806, -22000], ![834, 305800, 0]], ![![1633, -53221, -9020], ![418, 125378, 0]], ![![288, -10273, -1741], ![147, 24200, 0]]]
  g := ![![![1, 0, 0], ![-57, 139, 0], ![-11, 0, 139]], ![![0, 1, 0], ![-25, 59, 10], ![-5, 4, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-27, 64, 1]] ![![139, 0, 0], ![57, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![7923, 139, 0]], ![![-3753, 8896, 139], ![-1529, 3753, 695]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![57, 1, 0]]], ![![![-27, 64, 1]], ![![-11, 27, 5]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, 43, -28]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-167, 43, -28]] 
 ![![149, 0, 0], ![74, 1, 0], ![93, 0, 1]] where
  M :=![![![-167, 43, -28], ![-3950, -193, 486], ![7502, -192, -393]]]
  hmulB := by decide  
  f := ![![![-169161, -22275, -15494]], ![![-98064, -12913, -8982]], ![![-120391, -15853, -11027]]]
  g := ![![![-5, 43, -28], ![-234, -193, 486], ![391, -192, -393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-53, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-53, 1, 0]] 
 ![![149, 0, 0], ![96, 1, 0], ![102, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-53, 1, 0], ![-2, -51, 10], ![138, 4, -55]]]
  hmulB := by decide  
  f := ![![![18232, 493293, -96720], ![-3129, 1441128, 0]], ![![11774, 317794, -62310], ![-1936, 928419, 0]], ![![12508, 337690, -66211], ![-2066, 986544, 0]]]
  g := ![![![1, 0, 0], ![-96, 149, 0], ![-102, 0, 149]], ![![-1, 1, 0], ![26, -51, 10], ![36, 4, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-21, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-21, 1, 0]] 
 ![![149, 0, 0], ![128, 1, 0], ![94, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-21, 1, 0], ![-2, -19, 10], ![138, 4, -23]]]
  hmulB := by decide  
  f := ![![![-9566, -91889, 48360], ![745, -720564, 0]], ![![-8202, -78931, 41540], ![746, -618946, 0]], ![![-6019, -57971, 30509], ![583, -454584, 0]]]
  g := ![![![1, 0, 0], ![-128, 149, 0], ![-94, 0, 149]], ![![-1, 1, 0], ![10, -19, 10], ![12, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-167, 43, -28]] ![![149, 0, 0], ![-53, 1, 0]]
  ![![149, 0, 0], ![-5, 47, 1]] where
 M := ![![![-24883, 6407, -4172], ![4901, -2472, 1970]]]
 hmul := by decide  
 g := ![![![![-162, -4, -29], ![149, 0, 0]], ![![34, -27, 13], ![33, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-5, 47, 1]] ![![149, 0, 0], ![-21, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3129, 149, 0]], ![![-745, 7003, 149], ![149, -894, 447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-21, 1, 0]]], ![![![-5, 47, 1]], ![![1, -6, 3]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [59, 86, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 113, 80], [72, 37, 71], [0, 1]]
 g := ![![[140, 56, 32], [130, 122, 18], [54, 33, 76], [111, 90], [72, 39, 18], [117, 1], []], ![[142, 22, 100, 43], [9, 126, 26, 19], [114, 50, 105, 127], [134, 145], [42, 106, 69, 148], [129, 10], [102, 58]], ![[81, 61, 112, 117], [92, 6, 105, 107], [134, 36, 54, 13], [46, 100], [0, 20, 126, 111], [24, 85], [111, 58]]]
 h' := ![![[45, 113, 80], [31, 118, 33], [136, 5, 13], [42, 93, 23], [131, 0, 40], [43, 147, 13], [0, 0, 1], [0, 1]], ![[72, 37, 71], [110, 147, 91], [94, 74, 126], [119, 46, 137], [18, 127, 121], [49, 114, 10], [84, 90, 37], [45, 113, 80]], ![[0, 1], [24, 37, 27], [116, 72, 12], [107, 12, 142], [42, 24, 141], [130, 41, 128], [145, 61, 113], [72, 37, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 25], []]
 b := ![[], [112, 112, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [59, 86, 34, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3880096, 384748, -133182]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25696, 2548, -882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![9, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![9, 1, 0]] 
 ![![157, 0, 0], ![9, 1, 0], ![37, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![9, 1, 0], ![-2, 11, 10], ![138, 4, 7]]]
  hmulB := by decide  
  f := ![![![-8810, 48511, 44100], ![-157, -692370, 0]], ![![-504, 2772, 2520], ![1, -39564, 0]], ![![-2081, 11432, 10393], ![46, -163170, 0]]]
  g := ![![![1, 0, 0], ![-9, 157, 0], ![-37, 0, 157]], ![![0, 1, 0], ![-3, 11, 10], ![-1, 4, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349, -46, -32]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-349, -46, -32]] 
 ![![157, 0, 0], ![58, 1, 0], ![60, 0, 1]] where
  M :=![![![-349, -46, -32], ![-4324, -569, -396], ![-4556, -600, -417]]]
  hmulB := by decide  
  f := ![![![327, -18, -8]], ![![114, -5, -4]], ![![112, -8, -1]]]
  g := ![![![27, -46, -32], ![334, -569, -396], ![352, -600, -417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-67, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-67, 1, 0]] 
 ![![157, 0, 0], ![90, 1, 0], ![51, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-67, 1, 0], ![-2, -65, 10], ![138, 4, -69]]]
  hmulB := by decide  
  f := ![![![-6940, -245189, 37720], ![1413, -592204, 0]], ![![-3921, -140536, 21620], ![943, -339434, 0]], ![![-2213, -79648, 12253], ![556, -192372, 0]]]
  g := ![![![1, 0, 0], ![-90, 157, 0], ![-51, 0, 157]], ![![-1, 1, 0], ![34, -65, 10], ![21, 4, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![9, 1, 0]] ![![-349, -46, -32]]
  ![![157, 0, 0], ![52, 54, 1]] where
 M := ![![![-54793, -7222, -5024]], ![![-7465, -983, -684]]]
 hmul := by decide  
 g := ![![![![-349, -46, -32], ![0, 0, 0]]], ![![![-81, -41, -5], ![101, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![52, 54, 1]] ![![157, 0, 0], ![-67, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-10519, 157, 0]], ![![8164, 8478, 157], ![-3454, -3454, 471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-67, 1, 0]]], ![![![52, 54, 1]], ![![-22, -22, 3]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-27, -66, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-27, -66, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![136, 97, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-27, -66, 1], ![270, -155, -662], ![-9164, -251, 110]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -97, 163]], ![![-1, -1, 1], ![554, 393, -662], ![-148, -67, 110]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [64, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 162], [0, 1]]
 g := ![![[87, 135], [91, 85], [24], [33], [21], [96, 24], [1]], ![[0, 28], [0, 78], [24], [33], [21], [124, 139], [1]]]
 h' := ![![[137, 162], [44, 102], [128, 30], [69, 26], [15, 149], [50, 64], [99, 137], [0, 1]], ![[0, 1], [0, 61], [0, 133], [45, 137], [53, 14], [16, 99], [123, 26], [137, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [24, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [64, 26, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![944099, 103621, 45169]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31895, -26244, 45169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![10, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![10, 1, 0]] 
 ![![163, 0, 0], ![10, 1, 0], ![53, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![10, 1, 0], ![-2, 12, 10], ![138, 4, 8]]]
  hmulB := by decide  
  f := ![![![-12043, 72325, 60270], ![-163, -982401, 0]], ![![-738, 4428, 3690], ![1, -60147, 0]], ![![-3923, 23516, 19597], ![64, -319431, 0]]]
  g := ![![![1, 0, 0], ![-10, 163, 0], ![-53, 0, 163]], ![![0, 1, 0], ![-4, 12, 10], ![-2, 4, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-27, -66, 1]] ![![163, 0, 0], ![10, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![1630, 163, 0]], ![![-4401, -10758, 163], ![0, -815, -652]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![10, 1, 0]]], ![![![-27, -66, 1]], ![![0, -5, -4]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [127, 150, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 65, 134], [74, 101, 33], [0, 1]]
 g := ![![[133, 106, 72], [160, 131, 133], [119, 9, 47], [75, 64], [77, 2], [12, 50, 1], []], ![[58, 85, 89, 46], [140, 13, 161, 39], [121, 44, 13, 55], [147, 11], [116, 88], [66, 0, 136, 39], [60, 87]], ![[153, 26, 118, 24], [137, 142, 118, 4], [9, 146, 94, 97], [103, 63], [28, 84], [31, 86, 159, 147], [161, 87]]]
 h' := ![![[143, 65, 134], [54, 153, 89], [84, 73, 48], [23, 78, 61], [14, 3, 8], [146, 33, 154], [0, 0, 1], [0, 1]], ![[74, 101, 33], [58, 0, 99], [65, 10, 101], [162, 72, 80], [36, 46, 41], [78, 70, 103], [137, 44, 101], [143, 65, 134]], ![[0, 1], [94, 14, 146], [135, 84, 18], [42, 17, 26], [40, 118, 118], [151, 64, 77], [59, 123, 65], [74, 101, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141, 56], []]
 b := ![[], [92, 73, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [127, 150, 117, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5429003, 13527, 189378]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32509, 81, 1134]
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

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-164277763, -5267956, 17594506]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-164277763, -5267956, 17594506]] 
 ![![173, 0, 0], ![0, 173, 0], ![140, 4, 1]] where
  M :=![![![-164277763, -5267956, 17594506], ![2438577740, -104435651, -87868572], ![-1712270264, 207656754, -65769321]]]
  hmulB := by decide  
  f := ![![![-145174360084383, -19116463092576, -13297002654406]], ![![-1796753440122876, -236595296887159, -164570625616948]], ![![-169970311736612, -22381577499346, -15568146365641]]]
  g := ![![![-15187911, -437260, 17594506], ![85203340, 1427969, -87868572], ![43326212, 2721006, -65769321]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [103, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 172], [0, 1]]
 g := ![![[119, 139], [23], [164, 113], [156, 118], [31], [110, 157], [1]], ![[100, 34], [23], [161, 60], [110, 55], [31], [40, 16], [1]]]
 h' := ![![[26, 172], [91, 73], [62, 159], [21, 74], [53, 139], [88, 66], [70, 26], [0, 1]], ![[0, 1], [86, 100], [44, 14], [42, 99], [34, 34], [74, 107], [54, 147], [26, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [25, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [103, 147, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1603, 115, -620]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![511, 15, -620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145174360084383, -19116463092576, -13297002654406]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-145174360084383, -19116463092576, -13297002654406]] 
 ![![173, 0, 0], ![135, 1, 0], ![36, 0, 1]] where
  M :=![![![-145174360084383, -19116463092576, -13297002654406], ![-1796753440122876, -236595296887159, -164570625616948], ![-1893439758128752, -249326886877582, -173426447171261]]]
  hmulB := by decide  
  f := ![![![-164277763, -5267956, 17594506]], ![![-114097805, -4714507, 13221906]], ![![-44082484, 104106, 3281115]]]
  g := ![![![16845319381341, -19116463092576, -13297002654406], ![208486440241929, -236595296887159, -164570625616948], ![219705445482718, -249326886877582, -173426447171261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-164277763, -5267956, 17594506]] ![![-145174360084383, -19116463092576, -13297002654406]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-43, -57, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-43, -57, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![136, 122, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-43, -57, 1], ![252, -153, -572], ![-7922, -215, 76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -122, 179]], ![![-1, -1, 1], ![436, 389, -572], ![-102, -53, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [84, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 178], [0, 1]]
 g := ![![[109, 125], [30, 61], [135], [141], [128, 121], [68, 13], [1]], ![[135, 54], [173, 118], [135], [141], [83, 58], [75, 166], [1]]]
 h' := ![![[152, 178], [165, 29], [45, 132], [114, 99], [167, 61], [16, 11], [95, 152], [0, 1]], ![[0, 1], [98, 150], [61, 47], [126, 80], [131, 118], [77, 168], [108, 27], [152, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [168, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [84, 27, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31936, 2883, 4236]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3040, -2871, 4236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![35, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![35, 1, 0]] 
 ![![179, 0, 0], ![35, 1, 0], ![103, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![35, 1, 0], ![-2, 37, 10], ![138, 4, 33]]]
  hmulB := by decide  
  f := ![![![43387, -816908, -220780], ![3938, 3951962, 0]], ![![8457, -159697, -43160], ![896, 772564, 0]], ![![24944, -470065, -127041], ![2377, 2274034, 0]]]
  g := ![![![1, 0, 0], ![-35, 179, 0], ![-103, 0, 179]], ![![0, 1, 0], ![-13, 37, 10], ![-19, 4, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-43, -57, 1]] ![![179, 0, 0], ![35, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![6265, 179, 0]], ![![-7697, -10203, 179], ![-1253, -2148, -537]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![35, 1, 0]]], ![![![-43, -57, 1]], ![![-7, -12, -3]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12899226603, 1698561572, 1181483082]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![12899226603, 1698561572, 1181483082]] 
 ![![181, 0, 0], ![31, 1, 0], ![169, 0, 1]] where
  M :=![![![12899226603, 1698561572, 1181483082], ![159647542172, 21022282075, 14622649556], ![168238444344, 22153526354, 15409518869]]]
  hmulB := by decide  
  f := ![![![574351, -159040, 106882]], ![![181617, -23461, 8338]], ![![381947, -144334, 107679]]]
  g := ![![![-1322800127, 1698561572, 1181483082], ![-16371662857, 21022282075, 14622649556], ![-17252649511, 22153526354, 15409518869]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-945, 89, -12]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-945, 89, -12]] 
 ![![181, 0, 0], ![75, 1, 0], ![92, 0, 1]] where
  M :=![![![-945, 89, -12], ![-1834, -815, 914], ![12954, 200, -1183]]]
  hmulB := by decide  
  f := ![![![781345, 102887, 71566]], ![![377189, 49668, 34548]], ![![453450, 59710, 41533]]]
  g := ![![![-36, 89, -12], ![-137, -815, 914], ![590, 200, -1183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![12899226603, 1698561572, 1181483082]] ![![-945, 89, -12]]
  ![![781345, 102887, 71566]] where
 M := ![![![781345, 102887, 71566]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![781345, 102887, 71566]] ![![-945, 89, -12]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [57, 171, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 179, 150], [48, 11, 41], [0, 1]]
 g := ![![[52, 126, 90], [188, 59, 50], [184, 112, 12], [185, 67, 20], [189, 178, 54], [138, 140, 1], []], ![[56, 101, 104, 15], [115, 13, 171, 120], [124, 89, 67, 17], [86, 121, 119, 163], [180, 86, 104, 36], [111, 144, 142, 5], [57, 153]], ![[189, 112, 59, 101], [188, 179, 170, 57], [82, 24, 165, 38], [24, 106, 111, 29], [110, 148, 22, 143], [130, 131, 104, 174], [166, 153]]]
 h' := ![![[92, 179, 150], [171, 113, 102], [17, 42, 97], [151, 80, 143], [114, 16, 28], [156, 128, 98], [0, 0, 1], [0, 1]], ![[48, 11, 41], [57, 51, 118], [148, 188, 109], [143, 7, 12], [154, 183, 34], [44, 63, 32], [58, 143, 11], [92, 179, 150]], ![[0, 1], [133, 27, 162], [82, 152, 176], [146, 104, 36], [53, 183, 129], [56, 0, 61], [100, 48, 179], [48, 11, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 42], []]
 b := ![[], [87, 77, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [57, 171, 51, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-446940, -5730, 34380]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2340, -30, 180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-90, -64, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-90, -64, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![103, 129, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-90, -64, 1], ![266, -214, -642], ![-8888, -243, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -129, 193]], ![![-1, -1, 1], ![344, 428, -642], ![-69, -30, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [92, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 192], [0, 1]]
 g := ![![[180, 107], [1], [85], [130], [36], [1], [38, 1]], ![[0, 86], [1], [85], [130], [36], [1], [76, 192]]]
 h' := ![![[38, 192], [109, 53], [89, 192], [31, 144], [5, 138], [6, 187], [171, 1], [0, 1]], ![[0, 1], [0, 140], [51, 1], [99, 49], [38, 55], [164, 6], [16, 192], [38, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [169, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [92, 155, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2448, 2011, 1980]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1044, -1313, 1980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![63, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![63, 1, 0]] 
 ![![193, 0, 0], ![63, 1, 0], ![150, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![63, 1, 0], ![-2, 65, 10], ![138, 4, 61]]]
  hmulB := by decide  
  f := ![![![32122, -1095145, -168480], ![4825, 3251664, 0]], ![![10431, -357444, -54990], ![1738, 1061307, 0]], ![![24963, -851149, -130943], ![3757, 2527200, 0]]]
  g := ![![![1, 0, 0], ![-63, 193, 0], ![-150, 0, 193]], ![![0, 1, 0], ![-29, 65, 10], ![-48, 4, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-90, -64, 1]] ![![193, 0, 0], ![63, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![12159, 193, 0]], ![![-17370, -12352, 193], ![-5404, -4246, -579]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![63, 1, 0]]], ![![![-90, -64, 1]], ![![-28, -22, -3]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB202I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB202I3 : PrimesBelowBoundCertificateInterval O 137 193 202 where
  m := 11
  g := ![2, 3, 1, 3, 2, 1, 2, 2, 3, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB202I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N1]
    · exact ![I191N0]
    · exact ![I193N0, I193N1]
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
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![6967871]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N0, I149N1, I149N2, I157N0, I157N1, I157N2, I163N1, I173N1, I179N1, I181N0, I181N1, I193N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [I157N0, I157N1, I157N2], [I163N1], [], [I173N1], [I179N1], [I181N0, I181N1, I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
