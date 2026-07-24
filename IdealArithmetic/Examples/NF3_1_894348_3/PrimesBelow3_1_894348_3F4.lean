
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![47, 76, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![47, 76, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![47, 76, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![47, 76, 1], ![182, 47, 532], ![13832, 26, 47]]]
  hmulB := by decide  
  f := ![![![-46, -76, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -76, 197]], ![![0, 0, 1], ![-126, -205, 532], ![59, -18, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [189, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [185, 196], [0, 1]]
 g := ![![[97, 29], [174], [32, 88], [127], [150], [55], [185, 1]], ![[143, 168], [174], [158, 109], [127], [150], [55], [173, 196]]]
 h' := ![![[185, 196], [145, 134], [59, 119], [169, 65], [27, 179], [3, 100], [101, 152], [0, 1]], ![[0, 1], [113, 63], [10, 78], [177, 132], [46, 18], [182, 97], [50, 45], [185, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [85, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [189, 12, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![553, 14, -5]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 2, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![59, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![59, 1, 0]] 
 ![![197, 0, 0], ![59, 1, 0], ![150, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![59, 1, 0], ![0, 59, 7], ![182, 0, 59]]]
  hmulB := by decide  
  f := ![![![5252, 89, 0], ![-17533, 0, 0]], ![![1534, 26, 0], ![-5121, 0, 0]], ![![3990, 76, 1], ![-13320, -28, 0]]]
  g := ![![![1, 0, 0], ![-59, 197, 0], ![-150, 0, 197]], ![![0, 1, 0], ![-23, 59, 7], ![-44, 0, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![47, 76, 1]] ![![197, 0, 0], ![59, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![11623, 197, 0]], ![![9259, 14972, 197], ![2955, 4531, 591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![59, 1, 0]]], ![![![47, 76, 1]], ![![15, 23, 3]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [130, 95, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 191, 86], [124, 7, 113], [0, 1]]
 g := ![![[27, 146, 155], [14, 174, 50], [121, 105, 115], [121, 196], [143, 172], [145, 9], [1]], ![[148, 136, 132, 26], [174, 126, 50, 161], [151, 52, 68, 106], [5, 145], [90, 112], [109, 29], [137, 52, 47, 52]], ![[116, 197, 167, 154], [40, 175, 153, 68], [39, 61, 126, 73], [106, 180], [171, 64], [80, 31], [28, 37, 53, 147]]]
 h' := ![![[72, 191, 86], [170, 11, 73], [190, 74, 99], [44, 42, 48], [124, 195, 185], [40, 4, 157], [69, 104, 196], [0, 1]], ![[124, 7, 113], [190, 176, 64], [183, 25, 92], [17, 132, 167], [104, 194, 155], [137, 56, 50], [24, 84, 167], [72, 191, 86]], ![[0, 1], [38, 12, 62], [165, 100, 8], [13, 25, 183], [103, 9, 58], [170, 139, 191], [146, 11, 35], [124, 7, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 4], []]
 b := ![[], [195, 137, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [130, 95, 3, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117609, 6368, -9552]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![591, 32, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![30, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![30, 1, 0]] 
 ![![211, 0, 0], ![30, 1, 0], ![203, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![30, 1, 0], ![0, 30, 7], ![182, 0, 30]]]
  hmulB := by decide  
  f := ![![![4441, 148, 0], ![-31228, 0, 0]], ![![630, 21, 0], ![-4430, 0, 0]], ![![4253, 116, -6], ![-29906, 181, 0]]]
  g := ![![![1, 0, 0], ![-30, 211, 0], ![-203, 0, 211]], ![![0, 1, 0], ![-11, 30, 7], ![-28, 0, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-28, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-28, 1, 0]] 
 ![![211, 0, 0], ![183, 1, 0], ![99, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-28, 1, 0], ![0, -28, 7], ![182, 0, -28]]]
  hmulB := by decide  
  f := ![![![3137, -112, 0], ![23632, 0, 0]], ![![2717, -97, 0], ![20468, 0, 0]], ![![1513, -30, -6], ![11398, 181, 0]]]
  g := ![![![1, 0, 0], ![-183, 211, 0], ![-99, 0, 211]], ![![-1, 1, 0], ![21, -28, 7], ![14, 0, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-2, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-2, 1, 0]] 
 ![![211, 0, 0], ![209, 1, 0], ![120, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-2, 1, 0], ![0, -2, 7], ![182, 0, -2]]]
  hmulB := by decide  
  f := ![![![217, -108, 0], ![22788, 0, 0]], ![![215, -107, 0], ![22578, 0, 0]], ![![124, -60, -6], ![13022, 181, 0]]]
  g := ![![![1, 0, 0], ![-209, 211, 0], ![-120, 0, 211]], ![![-1, 1, 0], ![-2, -2, 7], ![2, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![30, 1, 0]] ![![211, 0, 0], ![-28, 1, 0]]
  ![![211, 0, 0], ![91, -60, 1]] where
 M := ![![![44521, 0, 0], ![-5908, 211, 0]], ![![6330, 211, 0], ![-840, 2, 7]]]
 hmul := by decide  
 g := ![![![![120, 60, -1], ![211, 0, 0]], ![![-28, 1, 0], ![0, 0, 0]]], ![![![-61, 61, -1], ![211, 0, 0]], ![![-7, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![91, -60, 1]] ![![211, 0, 0], ![-2, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-422, 211, 0]], ![![19201, -12660, 211], ![0, 211, -422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-2, 1, 0]]], ![![![91, -60, 1]], ![![0, 1, -2]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![4, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![4, 1, 0]] 
 ![![223, 0, 0], ![4, 1, 0], ![157, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![4, 1, 0], ![0, 4, 7], ![182, 0, 4]]]
  hmulB := by decide  
  f := ![![![217, 54, 0], ![-12042, 0, 0]], ![![-4, -1, 0], ![224, 0, 0]], ![![155, 38, -1], ![-8602, 32, 0]]]
  g := ![![![1, 0, 0], ![-4, 223, 0], ![-157, 0, 223]], ![![0, 1, 0], ![-5, 4, 7], ![-2, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![63, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![63, 1, 0]] 
 ![![223, 0, 0], ![63, 1, 0], ![102, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![63, 1, 0], ![0, 63, 7], ![182, 0, 63]]]
  hmulB := by decide  
  f := ![![![6490, 103, 0], ![-22969, 0, 0]], ![![1764, 28, 0], ![-6243, 0, 0]], ![![2964, 38, -1], ![-10490, 32, 0]]]
  g := ![![![1, 0, 0], ![-63, 223, 0], ![-102, 0, 223]], ![![0, 1, 0], ![-21, 63, 7], ![-28, 0, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-67, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-67, 1, 0]] 
 ![![223, 0, 0], ![156, 1, 0], ![187, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-67, 1, 0], ![0, -67, 7], ![182, 0, -67]]]
  hmulB := by decide  
  f := ![![![1073, -16, 0], ![3568, 0, 0]], ![![738, -11, 0], ![2454, 0, 0]], ![![913, -4, -1], ![3036, 32, 0]]]
  g := ![![![1, 0, 0], ![-156, 223, 0], ![-187, 0, 223]], ![![-1, 1, 0], ![41, -67, 7], ![57, 0, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![4, 1, 0]] ![![223, 0, 0], ![63, 1, 0]]
  ![![223, 0, 0], ![36, -86, 1]] where
 M := ![![![49729, 0, 0], ![14049, 223, 0]], ![![892, 223, 0], ![252, 67, 7]]]
 hmul := by decide  
 g := ![![![![187, 86, -1], ![223, 0, 0]], ![![27, 87, -1], ![223, 0, 0]]], ![![![-32, 87, -1], ![223, 0, 0]], ![![0, 3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![36, -86, 1]] ![![223, 0, 0], ![-67, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-14941, 223, 0]], ![![8028, -19178, 223], ![-2230, 5798, -669]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-67, 1, 0]]], ![![![36, -86, 1]], ![![-10, 26, -3]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![53, 99, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![53, 99, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![53, 99, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![53, 99, 1], ![182, 53, 693], ![18018, 26, 53]]]
  hmulB := by decide  
  f := ![![![-52, -99, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -99, 227]], ![![0, 0, 1], ![-161, -302, 693], ![67, -23, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [67, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [140, 226], [0, 1]]
 g := ![![[86, 147], [141, 34], [25], [112], [181], [125, 121], [140, 1]], ![[9, 80], [134, 193], [25], [112], [181], [40, 106], [53, 226]]]
 h' := ![![[140, 226], [87, 104], [11, 48], [209, 222], [26, 148], [24, 194], [154, 11], [0, 1]], ![[0, 1], [119, 123], [148, 179], [190, 5], [89, 79], [171, 33], [105, 216], [140, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [59, 184]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [67, 87, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1769, -15, 48]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -21, 48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-12, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-12, 1, 0]] 
 ![![227, 0, 0], ![215, 1, 0], ![174, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-12, 1, 0], ![0, -12, 7], ![182, 0, -12]]]
  hmulB := by decide  
  f := ![![![253, -21, 0], ![4767, 0, 0]], ![![241, -20, 0], ![4541, 0, 0]], ![![210, -14, -2], ![3958, 65, 0]]]
  g := ![![![1, 0, 0], ![-215, 227, 0], ![-174, 0, 227]], ![![-1, 1, 0], ![6, -12, 7], ![10, 0, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![53, 99, 1]] ![![227, 0, 0], ![-12, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-2724, 227, 0]], ![![12031, 22473, 227], ![-454, -1135, 681]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-12, 1, 0]]], ![![![53, 99, 1]], ![![-2, -5, 3]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [46, 38, 226, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 75, 172], [205, 153, 57], [0, 1]]
 g := ![![[94, 17, 104], [29, 85], [5, 10, 33], [225, 20], [37, 57], [223, 28, 9], [1]], ![[125, 188, 25, 132], [0, 209], [192, 105, 200, 174], [49, 224], [80, 37], [215, 78, 174, 61], [22, 4, 32, 68]], ![[90, 73, 79, 220], [168, 27], [204, 87, 205, 147], [211, 165], [55, 213], [101, 212, 132, 64], [164, 169, 68, 161]]]
 h' := ![![[27, 75, 172], [41, 171, 44], [228, 42, 90], [66, 152, 124], [49, 201, 132], [47, 140, 168], [183, 191, 3], [0, 1]], ![[205, 153, 57], [186, 103, 191], [84, 111, 155], [165, 175, 3], [75, 38, 37], [159, 64, 91], [122, 186, 106], [27, 75, 172]], ![[0, 1], [209, 184, 223], [193, 76, 213], [130, 131, 102], [26, 219, 60], [91, 25, 199], [158, 81, 120], [205, 153, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 61], []]
 b := ![[], [50, 92, 214], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [46, 38, 226, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-376247, 52441, 5038]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1643, 229, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-113, 74, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-113, 74, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![120, 74, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-113, 74, 1], ![182, -113, 518], ![13468, 26, -113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -74, 233]], ![![-1, 0, 1], ![-266, -165, 518], ![116, 36, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [146, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [172, 232], [0, 1]]
 g := ![![[85, 89], [195], [152], [45, 133], [123], [40, 109], [172, 1]], ![[15, 144], [195], [152], [87, 100], [123], [148, 124], [111, 232]]]
 h' := ![![[172, 232], [2, 97], [195, 112], [187, 131], [208, 191], [218, 194], [52, 80], [0, 1]], ![[0, 1], [143, 136], [120, 121], [118, 102], [207, 42], [34, 39], [65, 153], [172, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [62, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [146, 61, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![510, -35, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 17, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-52, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-52, 1, 0]] 
 ![![233, 0, 0], ![181, 1, 0], ![113, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-52, 1, 0], ![0, -52, 7], ![182, 0, -52]]]
  hmulB := by decide  
  f := ![![![7645, -147, 0], ![34251, 0, 0]], ![![5929, -114, 0], ![26563, 0, 0]], ![![3709, -49, -3], ![16617, 100, 0]]]
  g := ![![![1, 0, 0], ![-181, 233, 0], ![-113, 0, 233]], ![![-1, 1, 0], ![37, -52, 7], ![26, 0, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-113, 74, 1]] ![![233, 0, 0], ![-52, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-12116, 233, 0]], ![![-26329, 17242, 233], ![6058, -3961, 466]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-52, 1, 0]]], ![![![-113, 74, 1]], ![![26, -17, 2]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 8, -13]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![131, 8, -13]] 
 ![![239, 0, 0], ![0, 239, 0], ![137, 220, 1]] where
  M :=![![![131, 8, -13], ![-2366, 131, 56], ![1456, -338, 131]]]
  hmulB := by decide  
  f := ![![![-151, -14, -9]], ![![-1638, -151, -98]], ![![-1605, -148, -96]]]
  g := ![![![8, 12, -13], ![-42, -51, 56], ![-69, -122, 131]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [143, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 238], [0, 1]]
 g := ![![[5, 186], [2, 220], [70, 24], [89, 29], [40], [84, 201], [2, 1]], ![[138, 53], [203, 19], [118, 215], [147, 210], [40], [8, 38], [4, 238]]]
 h' := ![![[2, 238], [192, 159], [28, 69], [179, 195], [36, 183], [177, 163], [192, 100], [0, 1]], ![[0, 1], [32, 80], [166, 170], [91, 44], [163, 56], [25, 76], [153, 139], [2, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [154, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [143, 237, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7297, 4567, 2766]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1555, -2527, 2766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 14, 9]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![151, 14, 9]] 
 ![![239, 0, 0], ![133, 1, 0], ![102, 0, 1]] where
  M :=![![![151, 14, 9], ![1638, 151, 98], ![2548, 234, 151]]]
  hmulB := by decide  
  f := ![![![-131, -8, 13]], ![![-63, -5, 7]], ![![-62, -2, 5]]]
  g := ![![![-11, 14, 9], ![-119, 151, 98], ![-184, 234, 151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![131, 8, -13]] ![![151, 14, 9]]
  ![![239, 0, 0]] where
 M := ![![![-239, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [170, 195, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 127, 87], [149, 113, 154], [0, 1]]
 g := ![![[154, 109, 150], [1, 226], [68, 205], [4, 30], [223, 216, 119], [121, 179, 9], [1]], ![[134, 19, 136, 161], [20, 94], [24, 225], [5, 211], [87, 118, 104, 159], [223, 227, 100, 177], [196, 14, 192, 91]], ![[53, 136, 150, 27], [67, 91], [93, 141], [73, 16], [26, 90, 112, 182], [222, 229, 90, 237], [166, 188, 237, 150]]]
 h' := ![![[89, 127, 87], [103, 122, 106], [88, 153, 181], [70, 133, 143], [168, 43, 130], [156, 180, 100], [71, 46, 238], [0, 1]], ![[149, 113, 154], [102, 8, 179], [176, 177, 24], [20, 192, 15], [90, 183, 115], [84, 2, 209], [223, 228, 48], [89, 127, 87]], ![[0, 1], [81, 111, 197], [229, 152, 36], [186, 157, 83], [233, 15, 237], [148, 59, 173], [201, 208, 196], [149, 113, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 147], []]
 b := ![[], [14, 108, 231], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [170, 195, 3, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29643, -4338, 1446]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![123, -18, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-97, 111, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-97, 111, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![154, 111, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-97, 111, 1], ![182, -97, 777], ![20202, 26, -97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -111, 251]], ![![-1, 0, 1], ![-476, -344, 777], ![140, 43, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [198, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 250], [0, 1]]
 g := ![![[240, 161], [107, 155], [197], [220, 27], [16, 52], [178, 214], [170, 1]], ![[0, 90], [102, 96], [197], [41, 224], [71, 199], [163, 37], [89, 250]]]
 h' := ![![[170, 250], [149, 101], [94, 54], [114, 166], [95, 228], [147, 110], [225, 88], [0, 1]], ![[0, 1], [0, 150], [238, 197], [222, 85], [201, 23], [22, 141], [125, 163], [170, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [83, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [198, 81, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![926, 185, 169]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100, -74, 169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-24, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-24, 1, 0]] 
 ![![251, 0, 0], ![227, 1, 0], ![97, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-24, 1, 0], ![0, -24, 7], ![182, 0, -24]]]
  hmulB := by decide  
  f := ![![![3553, -148, 0], ![37148, 0, 0]], ![![3241, -135, 0], ![33886, 0, 0]], ![![1379, -54, -1], ![14418, 36, 0]]]
  g := ![![![1, 0, 0], ![-227, 251, 0], ![-97, 0, 251]], ![![-1, 1, 0], ![19, -24, 7], ![10, 0, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-97, 111, 1]] ![![251, 0, 0], ![-24, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-6024, 251, 0]], ![![-24347, 27861, 251], ![2510, -2761, 753]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-24, 1, 0]]], ![![![-97, 111, 1]], ![![10, -11, 3]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-27, -20, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-27, -20, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![230, 237, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-27, -20, 1], ![182, -27, -140], ![-3640, 26, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-230, -237, 257]], ![![-1, -1, 1], ![126, 129, -140], ![10, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [131, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [200, 256], [0, 1]]
 g := ![![[177, 211], [187], [117], [246], [52], [205], [165], [1]], ![[229, 46], [187], [117], [246], [52], [205], [165], [1]]]
 h' := ![![[200, 256], [83, 89], [57, 207], [96, 84], [222, 195], [159, 56], [172, 132], [126, 200], [0, 1]], ![[0, 1], [150, 168], [80, 50], [191, 173], [158, 62], [51, 201], [101, 125], [34, 57], [200, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [252]]
 b := ![[], [250, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [131, 57, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7031, -506, 822]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-763, -760, 822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-117, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-117, 1, 0]] 
 ![![257, 0, 0], ![140, 1, 0], ![27, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-117, 1, 0], ![0, -117, 7], ![182, 0, -117]]]
  hmulB := by decide  
  f := ![![![21529, -184, 0], ![47288, 0, 0]], ![![11818, -101, 0], ![25958, 0, 0]], ![![2331, 47, -4], ![5120, 147, 0]]]
  g := ![![![1, 0, 0], ![-140, 257, 0], ![-27, 0, 257]], ![![-1, 1, 0], ![63, -117, 7], ![13, 0, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-27, -20, 1]] ![![257, 0, 0], ![-117, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-30069, 257, 0]], ![![-6939, -5140, 257], ![3341, 2313, -257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-117, 1, 0]]], ![![![-27, -20, 1]], ![![13, 9, -1]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB268I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB268I4 : PrimesBelowBoundCertificateInterval O 193 257 268 where
  m := 11
  g := ![2, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB268I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![211, 211, 211]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![63001, 251]
    · exact ![66049, 257]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N1, I211N0, I211N1, I211N2, I223N0, I223N1, I223N2, I227N1, I233N1, I239N1, I251N1, I257N1]
  Il := ![[I197N1], [], [I211N0, I211N1, I211N2], [I223N0, I223N1, I223N2], [I227N1], [], [I233N1], [I239N1], [], [I251N1], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
