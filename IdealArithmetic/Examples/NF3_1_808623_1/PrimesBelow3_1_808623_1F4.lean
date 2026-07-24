
import IdealArithmetic.Examples.NF3_1_808623_1.RI3_1_808623_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [92, 155, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 111, 171], [152, 85, 26], [0, 1]]
 g := ![![[50, 127, 171], [184, 23], [159, 20, 93], [161, 10], [149, 163], [170, 191], [1]], ![[155, 88, 4, 1], [173, 143], [54, 103, 182, 127], [47, 178], [86, 146], [105, 51], [57, 181, 111, 154]], ![[27, 8, 186, 59], [83, 70], [107, 15, 110, 26], [41, 173], [0, 23], [35, 175], [102, 74, 28, 43]]]
 h' := ![![[128, 111, 171], [150, 135, 34], [147, 171, 90], [109, 81, 68], [46, 68, 124], [113, 161, 153], [105, 42, 83], [0, 1]], ![[152, 85, 26], [94, 163, 168], [168, 130, 52], [36, 32, 128], [82, 76, 104], [36, 28, 151], [162, 80, 53], [128, 111, 171]], ![[0, 1], [76, 96, 192], [63, 93, 55], [192, 84, 1], [157, 53, 166], [74, 8, 90], [158, 75, 61], [152, 85, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 27], []]
 b := ![[], [25, 91, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [92, 155, 114, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-727521, 1182, 1970]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3693, 6, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-747, -15, 41]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-747, -15, 41]] 
 ![![199, 0, 0], ![0, 199, 0], ![74, 87, 1]] where
  M :=![![![-747, -15, 41], ![7287, -326, -157], ![-8641, 1106, -184]]]
  hmulB := by decide  
  f := ![![![-1174, -214, -79]], ![![-13555, -2471, -912]], ![![-6495, -1184, -437]]]
  g := ![![![-19, -18, 41], ![95, 67, -157], ![25, 86, -184]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [166, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 198], [0, 1]]
 g := ![![[50, 80], [188, 178], [73, 61], [103], [33], [196], [58, 1]], ![[113, 119], [164, 21], [29, 138], [103], [33], [196], [116, 198]]]
 h' := ![![[58, 198], [35, 105], [21, 24], [44, 85], [174, 74], [105, 86], [123, 14], [0, 1]], ![[0, 1], [155, 94], [20, 175], [198, 114], [88, 125], [118, 113], [139, 185], [58, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [78, 162]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [166, 141, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13050, 5262, 3368]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1318, -1446, 3368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1174, 214, 79]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![1174, 214, 79]] 
 ![![199, 0, 0], ![164, 1, 0], ![87, 0, 1]] where
  M :=![![![1174, 214, 79], ![13555, 2471, 912], ![26344, 4803, 1773]]]
  hmulB := by decide  
  f := ![![![747, 15, -41]], ![![579, 14, -33]], ![![370, 1, -17]]]
  g := ![![![-205, 214, 79], ![-2367, 2471, 912], ![-4601, 4803, 1773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-747, -15, 41]] ![![1174, 214, 79]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-102, 96, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-102, 96, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![109, 96, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-102, 96, 1], ![-15, 101, 478], ![16846, 1087, -281]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -96, 211]], ![![-1, 0, 1], ![-247, -217, 478], ![225, 133, -281]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [169, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 210], [0, 1]]
 g := ![![[106, 5], [138, 114], [43], [64], [138, 5], [134], [21, 1]], ![[0, 206], [0, 97], [43], [64], [32, 206], [134], [42, 210]]]
 h' := ![![[21, 210], [99, 146], [30, 89], [40, 185], [99, 8], [109, 65], [38, 61], [0, 1]], ![[0, 1], [0, 65], [0, 122], [127, 26], [56, 203], [208, 146], [53, 150], [21, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176]]
 b := ![[], [131, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [169, 190, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3313871, 1753909, 422636]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-202623, -183977, 422636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-56, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-56, 1, 0]] 
 ![![211, 0, 0], ![155, 1, 0], ![70, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-56, 1, 0], ![-2, -54, 5], ![177, 11, -58]]]
  hmulB := by decide  
  f := ![![![36945, 1032287, -95580], ![-4853, 4033476, 0]], ![![27133, 758285, -70210], ![-3586, 2962862, 0]], ![![12306, 342464, -31709], ![-1424, 1338120, 0]]]
  g := ![![![1, 0, 0], ![-155, 211, 0], ![-70, 0, 211]], ![![-1, 1, 0], ![38, -54, 5], ![12, 11, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-102, 96, 1]] ![![211, 0, 0], ![-56, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-11816, 211, 0]], ![![-21522, 20256, 211], ![5697, -5275, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-56, 1, 0]]], ![![![-102, 96, 1]], ![![27, -25, 2]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![67, -54, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![67, -54, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![67, 169, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![67, -54, 1], ![285, -30, -272], ![-9704, -563, 188]]]
  hmulB := by decide  
  f := ![![![-66, 54, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -169, 223]], ![![0, -1, 1], ![83, 206, -272], ![-100, -145, 188]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [55, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 222], [0, 1]]
 g := ![![[137, 73], [218, 148], [218, 7], [20, 39], [138, 50], [201], [47, 1]], ![[0, 150], [38, 75], [101, 216], [69, 184], [35, 173], [201], [94, 222]]]
 h' := ![![[47, 222], [52, 127], [52, 51], [15, 197], [215, 183], [125, 75], [91, 147], [0, 1]], ![[0, 1], [0, 96], [219, 172], [131, 26], [119, 40], [82, 148], [87, 76], [47, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [208, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [55, 176, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7338, 4716, -459]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![105, 369, -459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![49, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![49, 1, 0]] 
 ![![223, 0, 0], ![49, 1, 0], ![35, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![49, 1, 0], ![-2, 51, 5], ![177, 11, 47]]]
  hmulB := by decide  
  f := ![![![36871, -962694, -94380], ![4014, 4209348, 0]], ![![8098, -211501, -20735], ![893, 924781, 0]], ![![5761, -151096, -14813], ![748, 660660, 0]]]
  g := ![![![1, 0, 0], ![-49, 223, 0], ![-35, 0, 223]], ![![0, 1, 0], ![-12, 51, 5], ![-9, 11, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![67, -54, 1]] ![![223, 0, 0], ![49, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![10927, 223, 0]], ![![14941, -12042, 223], ![3568, -2676, -223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![49, 1, 0]]], ![![![67, -54, 1]], ![![16, -12, -1]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![3, -56, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![3, -56, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![3, 171, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![3, -56, 1], ![289, -98, -282], ![-10058, -585, 128]]]
  hmulB := by decide  
  f := ![![![-2, 56, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -171, 227]], ![![0, -1, 1], ![5, 212, -282], ![-46, -99, 128]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [106, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 226], [0, 1]]
 g := ![![[63, 33], [51, 87], [9], [100], [186], [156, 43], [132, 1]], ![[106, 194], [185, 140], [9], [100], [186], [157, 184], [37, 226]]]
 h' := ![![[132, 226], [42, 184], [75, 119], [216, 224], [123, 10], [35, 58], [82, 66], [0, 1]], ![[0, 1], [41, 43], [120, 108], [47, 3], [81, 217], [200, 169], [168, 161], [132, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [209]]
 b := ![[], [140, 218]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [106, 95, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1942, 826, -185]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 143, -185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![55, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![55, 1, 0]] 
 ![![227, 0, 0], ![55, 1, 0], ![99, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![55, 1, 0], ![-2, 57, 5], ![177, 11, 53]]]
  hmulB := by decide  
  f := ![![![38089, -1116878, -97970], ![4540, 4447838, 0]], ![![9219, -270584, -23735], ![1136, 1077569, 0]], ![![16588, -487097, -42727], ![2077, 1939806, 0]]]
  g := ![![![1, 0, 0], ![-55, 227, 0], ![-99, 0, 227]], ![![0, 1, 0], ![-16, 57, 5], ![-25, 11, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![3, -56, 1]] ![![227, 0, 0], ![55, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![12485, 227, 0]], ![![681, -12712, 227], ![454, -3178, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![55, 1, 0]]], ![![![3, -56, 1]], ![![2, -14, -1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-65, 114, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-65, 114, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![164, 114, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-65, 114, 1], ![-51, 174, 568], ![20032, 1285, -280]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-164, -114, 229]], ![![-1, 0, 1], ![-407, -282, 568], ![288, 145, -280]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [175, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 228], [0, 1]]
 g := ![![[32, 129], [167], [217, 108], [154], [144], [72, 228], [125, 1]], ![[127, 100], [167], [206, 121], [154], [144], [176, 1], [21, 228]]]
 h' := ![![[125, 228], [5, 154], [39, 25], [68, 197], [15, 29], [224, 217], [109, 107], [0, 1]], ![[0, 1], [19, 75], [187, 204], [190, 32], [205, 200], [98, 12], [202, 122], [125, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [206]]
 b := ![[], [89, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [175, 104, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54606, 9344, 3525]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2286, -1714, 3525]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-110, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-110, 1, 0]] 
 ![![229, 0, 0], ![119, 1, 0], ![51, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-110, 1, 0], ![-2, -108, 5], ![177, 11, -112]]]
  hmulB := by decide  
  f := ![![![-36431, -2181204, 100980], ![8244, -4624884, 0]], ![![-18897, -1133371, 52470], ![4352, -2403126, 0]], ![![-8039, -485771, 22489], ![1991, -1029996, 0]]]
  g := ![![![1, 0, 0], ![-119, 229, 0], ![-51, 0, 229]], ![![-1, 1, 0], ![55, -108, 5], ![20, 11, -112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-65, 114, 1]] ![![229, 0, 0], ![-110, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-25190, 229, 0]], ![![-14885, 26106, 229], ![7099, -12366, 458]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-110, 1, 0]]], ![![![-65, 114, 1]], ![![31, -54, 2]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [217, 176, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 50, 224], [170, 182, 9], [0, 1]]
 g := ![![[109, 21, 51], [66, 133], [175, 224], [152, 223, 110], [181, 207], [142, 220, 170], [1]], ![[27, 154, 189, 141], [46, 85], [32, 204], [78, 121, 169, 110], [186, 4], [8, 88, 42, 81], [67, 51, 165, 203]], ![[7, 151, 212, 142], [225, 7], [227, 148], [133, 180, 153, 205], [138, 19], [71, 201, 43, 207], [192, 113, 58, 30]]]
 h' := ![![[113, 50, 224], [228, 188, 98], [156, 34, 191], [102, 145, 199], [202, 225, 24], [175, 220, 185], [16, 57, 50], [0, 1]], ![[170, 182, 9], [21, 27, 67], [110, 125, 205], [225, 150, 196], [155, 34, 13], [21, 113, 2], [68, 65, 199], [113, 50, 224]], ![[0, 1], [154, 18, 68], [226, 74, 70], [136, 171, 71], [141, 207, 196], [27, 133, 46], [5, 111, 217], [170, 182, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 20], []]
 b := ![[], [177, 37, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [217, 176, 183, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3507582, 17242, 137936]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15054, 74, 592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![4, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![4, 1, 0]] 
 ![![239, 0, 0], ![4, 1, 0], ![186, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![4, 1, 0], ![-2, 6, 5], ![177, 11, 2]]]
  hmulB := by decide  
  f := ![![![-22079, 66240, 55200], ![0, -2638560, 0]], ![![-368, 1104, 920], ![1, -43976, 0]], ![![-17182, 51551, 42959], ![-49, -2053440, 0]]]
  g := ![![![1, 0, 0], ![-4, 239, 0], ![-186, 0, 239]], ![![0, 1, 0], ![-4, 6, 5], ![-1, 11, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![91, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![91, 1, 0]] 
 ![![239, 0, 0], ![91, 1, 0], ![219, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![91, 1, 0], ![-2, 93, 5], ![177, 11, 89]]]
  hmulB := by decide  
  f := ![![![67046, -3324985, -178760], ![11711, 8544728, 0]], ![![25495, -1265935, -68060], ![4542, 3253268, 0]], ![![61397, -3046744, -163801], ![10832, 7829688, 0]]]
  g := ![![![1, 0, 0], ![-91, 239, 0], ![-219, 0, 239]], ![![0, 1, 0], ![-40, 93, 5], ![-85, 11, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-95, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-95, 1, 0]] 
 ![![239, 0, 0], ![144, 1, 0], ![49, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-95, 1, 0], ![-2, -93, 5], ![177, 11, -97]]]
  hmulB := by decide  
  f := ![![![-64384, -3219246, 173075], ![12189, -8272985, 0]], ![![-38764, -1939546, 104275], ![7410, -4984345, 0]], ![![-13179, -660013, 35484], ![2552, -1696135, 0]]]
  g := ![![![1, 0, 0], ![-144, 239, 0], ![-49, 0, 239]], ![![-1, 1, 0], ![55, -93, 5], ![14, 11, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![4, 1, 0]] ![![239, 0, 0], ![91, 1, 0]]
  ![![239, 0, 0], ![-71, 115, 1]] where
 M := ![![![57121, 0, 0], ![21749, 239, 0]], ![![956, 239, 0], ![362, 97, 5]]]
 hmul := by decide  
 g := ![![![![239, 0, 0], ![0, 0, 0]], ![![91, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![3, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-71, 115, 1]] ![![239, 0, 0], ![-95, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-22705, 239, 0]], ![![-16969, 27485, 239], ![6692, -10755, 478]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-95, 1, 0]]], ![![![-71, 115, 1]], ![![28, -45, 2]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![63, -107, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![63, -107, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![63, 134, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![63, -107, 1], ![391, -140, -537], ![-19085, -1146, 290]]]
  hmulB := by decide  
  f := ![![![-62, 107, -1], ![241, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -134, 241]], ![![0, -1, 1], ![142, 298, -537], ![-155, -166, 290]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [210, 224, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 240], [0, 1]]
 g := ![![[226, 143], [217], [24], [134], [4, 229], [178, 216], [17, 1]], ![[6, 98], [217], [24], [134], [41, 12], [235, 25], [34, 240]]]
 h' := ![![[17, 240], [20, 216], [102, 159], [9, 187], [124, 80], [216, 179], [45, 79], [0, 1]], ![[0, 1], [77, 25], [154, 82], [55, 54], [38, 161], [126, 62], [183, 162], [17, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [122, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [210, 224, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2380, 5330, 3385]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-875, -1860, 3385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![55, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![55, 1, 0]] 
 ![![241, 0, 0], ![55, 1, 0], ![192, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![55, 1, 0], ![-2, 57, 5], ![177, 11, 53]]]
  hmulB := by decide  
  f := ![![![48557, -1418353, -124415], ![5302, 5996803, 0]], ![![11081, -323651, -28390], ![1206, 1368398, 0]], ![![38694, -1129974, -99119], ![4182, 4777536, 0]]]
  g := ![![![1, 0, 0], ![-55, 241, 0], ![-192, 0, 241]], ![![0, 1, 0], ![-17, 57, 5], ![-44, 11, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![63, -107, 1]] ![![241, 0, 0], ![55, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![13255, 241, 0]], ![![15183, -25787, 241], ![3856, -6025, -482]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![55, 1, 0]]], ![![![63, -107, 1]], ![![16, -25, -2]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 22, -15]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![83, 22, -15]] 
 ![![251, 0, 0], ![0, 251, 0], ![212, 32, 1]] where
  M :=![![![83, 22, -15], ![-2699, -38, 140], ![6084, -223, -156]]]
  hmulB := by decide  
  f := ![![![148, 27, 10]], ![![1716, 312, 115]], ![![357, 65, 24]]]
  g := ![![![13, 2, -15], ![-129, -18, 140], ![156, 19, -156]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [169, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 250], [0, 1]]
 g := ![![[72, 101], [91, 79], [88], [129, 21], [214, 125], [113, 3], [131, 1]], ![[0, 150], [149, 172], [88], [119, 230], [23, 126], [4, 248], [11, 250]]]
 h' := ![![[131, 250], [183, 58], [229, 62], [36, 29], [229, 71], [230, 80], [200, 175], [0, 1]], ![[0, 1], [0, 193], [68, 189], [70, 222], [243, 180], [168, 171], [33, 76], [131, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [206, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [169, 120, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20844, 9175, 875]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-656, -75, 875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148, 27, 10]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![148, 27, 10]] 
 ![![251, 0, 0], ![93, 1, 0], ![90, 0, 1]] where
  M :=![![![148, 27, 10], ![1716, 312, 115], ![3319, 607, 224]]]
  hmulB := by decide  
  f := ![![![83, 22, -15]], ![![20, 8, -5]], ![![54, 7, -6]]]
  g := ![![![-13, 27, 10], ![-150, 312, 115], ![-292, 607, 224]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![83, 22, -15]] ![![148, 27, 10]]
  ![![251, 0, 0]] where
 M := ![![![251, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB255I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 254 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 254 (by omega)

def PB255I4 : PrimesBelowBoundCertificateInterval O 193 254 255 where
  m := 10
  g := ![1, 2, 2, 2, 2, 2, 1, 3, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB255I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![239, 239, 239]
    · exact ![58081, 241]
    · exact ![63001, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N1, I211N1, I223N1, I227N1, I229N1, I239N0, I239N1, I239N2, I241N1, I251N1]
  Il := ![[], [I199N1], [I211N1], [I223N1], [I227N1], [I229N1], [], [I239N0, I239N1, I239N2], [I241N1], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
