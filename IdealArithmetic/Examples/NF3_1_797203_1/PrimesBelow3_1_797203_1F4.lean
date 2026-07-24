
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![93, -15, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![93, -15, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![93, 182, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![93, -15, 1], ![122, 82, -58], ![-2179, 415, 38]]]
  hmulB := by decide  
  f := ![![![-92, 15, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -182, 197]], ![![0, -1, 1], ![28, 54, -58], ![-29, -33, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [31, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 196], [0, 1]]
 g := ![![[159, 16], [81], [2, 133], [26], [41], [28], [193, 1]], ![[95, 181], [81], [61, 64], [26], [41], [28], [189, 196]]]
 h' := ![![[193, 196], [151, 4], [135, 188], [173, 112], [83, 82], [127, 108], [124, 182], [0, 1]], ![[0, 1], [135, 193], [171, 9], [119, 85], [149, 115], [89, 89], [184, 15], [193, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [73, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [31, 4, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1842, 1209, -908]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![438, 845, -908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![58, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![58, 1, 0]] 
 ![![197, 0, 0], ![58, 1, 0], ![159, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![58, 1, 0], ![2, 57, 4], ![152, -26, 60]]]
  hmulB := by decide  
  f := ![![![1751, 58135, 4080], ![985, -200940, 0]], ![![484, 17098, 1200], ![395, -59100, 0]], ![![1405, 46921, 3293], ![823, -162180, 0]]]
  g := ![![![1, 0, 0], ![-58, 197, 0], ![-159, 0, 197]], ![![0, 1, 0], ![-20, 57, 4], ![-40, -26, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![93, -15, 1]] ![![197, 0, 0], ![58, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![11426, 197, 0]], ![![18321, -2955, 197], ![5516, -788, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![58, 1, 0]]], ![![![93, -15, 1]], ![![28, -4, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14728713, -364450, -482046]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-14728713, -364450, -482046]] 
 ![![199, 0, 0], ![0, 199, 0], ![195, 168, 1]] where
  M :=![![![-14728713, -364450, -482046], ![-73999892, -1831067, -2421892], ![-104083046, -2575450, -3406463]]]
  hmulB := by decide  
  f := ![![![-1179, 350, -82]], ![![-11764, 603, 1236]], ![![-10861, 796, 971]]]
  g := ![![![398343, 405122, -482046], ![2001352, 2035411, -2421892], ![2814961, 2862866, -3406463]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [177, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 198], [0, 1]]
 g := ![![[150, 9], [147, 172], [68, 20], [90], [35], [130], [116, 1]], ![[0, 190], [0, 27], [0, 179], [90], [35], [130], [33, 198]]]
 h' := ![![[116, 198], [50, 3], [103, 42], [120, 47], [54, 182], [105, 154], [164, 145], [0, 1]], ![[0, 1], [0, 196], [0, 157], [0, 152], [72, 17], [59, 45], [69, 54], [116, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [76, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [177, 83, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-982, 2041, -650]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![632, 559, -650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1179, -350, 82]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![1179, -350, 82]] 
 ![![199, 0, 0], ![122, 1, 0], ![91, 0, 1]] where
  M :=![![![1179, -350, 82], ![11764, -603, -1236], ![-44918, 11150, -1571]]]
  hmulB := by decide  
  f := ![![![14728713, 364450, 482046]], ![![9401522, 232633, 307696]], ![![7258271, 179600, 237551]]]
  g := ![![![183, -350, 82], ![994, -603, -1236], ![-6343, 11150, -1571]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-14728713, -364450, -482046]] ![![1179, -350, 82]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-67, -12, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-67, -12, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![144, 199, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-67, -12, 1], ![128, -81, -46], ![-1723, 337, -116]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-144, -199, 211]], ![![-1, -1, 1], ![32, 43, -46], ![71, 111, -116]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [61, 153, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 210], [0, 1]]
 g := ![![[172, 6], [199, 1], [79], [107], [104, 169], [54], [58, 1]], ![[98, 205], [46, 210], [79], [107], [200, 42], [54], [116, 210]]]
 h' := ![![[58, 210], [99, 46], [35, 210], [210, 76], [197, 23], [162, 198], [49, 138], [0, 1]], ![[0, 1], [24, 165], [188, 1], [187, 135], [54, 188], [41, 13], [35, 73], [58, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [130, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [61, 153, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414235, 112354, -110678]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77497, 104916, -110678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![46, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![46, 1, 0]] 
 ![![211, 0, 0], ![46, 1, 0], ![116, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![46, 1, 0], ![2, 45, 4], ![152, -26, 48]]]
  hmulB := by decide  
  f := ![![![-27973, -673877, -59904], ![-9073, 3159936, 0]], ![![-6114, -146871, -13056], ![-1898, 688704, 0]], ![![-15394, -370473, -32933], ![-4917, 1737216, 0]]]
  g := ![![![1, 0, 0], ![-46, 211, 0], ![-116, 0, 211]], ![![0, 1, 0], ![-12, 45, 4], ![-20, -26, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-67, -12, 1]] ![![211, 0, 0], ![46, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![9706, 211, 0]], ![![-14137, -2532, 211], ![-2954, -633, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![46, 1, 0]]], ![![![-67, -12, 1]], ![![-14, -3, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![884, -273, 69]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![884, -273, 69]] 
 ![![223, 0, 0], ![0, 223, 0], ![113, 93, 1]] where
  M :=![![![884, -273, 69], ![9942, -637, -954], ![-34527, 8823, -1387]]]
  hmulB := by decide  
  f := ![![![-41707, -1032, -1365]], ![![-209544, -5185, -6858]], ![![-109844, -2718, -3595]]]
  g := ![![![-31, -30, 69], ![528, 395, -954], ![548, 618, -1387]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [99, 209, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 222], [0, 1]]
 g := ![![[126, 156], [71, 138], [105, 65], [48, 212], [70, 169], [43], [14, 1]], ![[80, 67], [219, 85], [123, 158], [117, 11], [206, 54], [43], [28, 222]]]
 h' := ![![[14, 222], [107, 80], [86, 19], [154, 43], [206, 99], [54, 210], [175, 97], [0, 1]], ![[0, 1], [112, 143], [129, 204], [87, 180], [31, 124], [95, 13], [195, 126], [14, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [20, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [99, 209, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-730, 4023, -3906]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1976, 1647, -3906]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41707, 1032, 1365]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![41707, 1032, 1365]] 
 ![![223, 0, 0], ![72, 1, 0], ![172, 0, 1]] where
  M :=![![![41707, 1032, 1365], ![209544, 5185, 6858], ![294729, 7293, 9646]]]
  hmulB := by decide  
  f := ![![![-884, 273, -69]], ![![-330, 91, -18]], ![![-527, 171, -47]]]
  g := ![![![-1199, 1032, 1365], ![-6024, 5185, 6858], ![-8473, 7293, 9646]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![884, -273, 69]] ![![41707, 1032, 1365]]
  ![![223, 0, 0]] where
 M := ![![![-223, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![43, 1, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![43, 1, 0]] 
 ![![227, 0, 0], ![43, 1, 0], ![3, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![43, 1, 0], ![2, 42, 4], ![152, -26, 45]]]
  hmulB := by decide  
  f := ![![![-34054, -753941, -71808], ![-9761, 4075104, 0]], ![![-6456, -142792, -13600], ![-1815, 771800, 0]], ![![-451, -9964, -949], ![-124, 53856, 0]]]
  g := ![![![1, 0, 0], ![-43, 227, 0], ![-3, 0, 227]], ![![0, 1, 0], ![-8, 42, 4], ![5, -26, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-31, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-31, 1, 0]] 
 ![![227, 0, 0], ![196, 1, 0], ![93, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-31, 1, 0], ![2, -32, 4], ![152, -26, -29]]]
  hmulB := by decide  
  f := ![![![7605, -124634, 15580], ![-1362, -884165, 0]], ![![6541, -107610, 13452], ![-1361, -763401, 0]], ![![3131, -51062, 6383], ![-446, -362235, 0]]]
  g := ![![![1, 0, 0], ![-196, 227, 0], ![-93, 0, 227]], ![![-1, 1, 0], ![26, -32, 4], ![35, -26, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-13, 1, 0]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-13, 1, 0]] 
 ![![227, 0, 0], ![214, 1, 0], ![182, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-13, 1, 0], ![2, -14, 4], ![152, -26, -11]]]
  hmulB := by decide  
  f := ![![![57315, -403178, 115200], ![-4994, -6537600, 0]], ![![54028, -380079, 108600], ![-4766, -6163050, 0]], ![![45955, -323253, 92363], ![-3969, -5241600, 0]]]
  g := ![![![1, 0, 0], ![-214, 227, 0], ![-182, 0, 227]], ![![-1, 1, 0], ![10, -14, 4], ![34, -26, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![43, 1, 0]] ![![227, 0, 0], ![-31, 1, 0]]
  ![![227, 0, 0], ![-49, -54, 1]] where
 M := ![![![51529, 0, 0], ![-7037, 227, 0]], ![![9761, 227, 0], ![-1331, 11, 4]]]
 hmul := by decide  
 g := ![![![![227, 0, 0], ![0, 0, 0]], ![![18, 55, -1], ![227, 0, 0]]], ![![![43, 1, 0], ![0, 0, 0]], ![![-5, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-49, -54, 1]] ![![227, 0, 0], ![-13, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-2951, 227, 0]], ![![-11123, -12258, 227], ![681, 681, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-13, 1, 0]]], ![![![-49, -54, 1]], ![![3, 3, -1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![61, 108, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![61, 108, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![61, 108, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![61, 108, 1], ![368, -73, 434], ![16517, -2783, 252]]]
  hmulB := by decide  
  f := ![![![-60, -108, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -108, 229]], ![![0, 0, 1], ![-114, -205, 434], ![5, -131, 252]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [112, 224, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 228], [0, 1]]
 g := ![![[2, 196], [121], [97, 17], [129], [187], [175, 12], [5, 1]], ![[66, 33], [121], [182, 212], [129], [187], [6, 217], [10, 228]]]
 h' := ![![[5, 228], [84, 215], [128, 11], [133, 186], [29, 75], [94, 88], [127, 142], [0, 1]], ![[0, 1], [14, 14], [183, 218], [147, 43], [175, 154], [76, 141], [150, 87], [5, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [131, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [112, 224, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1263, 1429, -2228]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![599, 1057, -2228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![24, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![24, 1, 0]] 
 ![![229, 0, 0], ![24, 1, 0], ![206, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![24, 1, 0], ![2, 23, 4], ![152, -26, 26]]]
  hmulB := by decide  
  f := ![![![-34937, -408112, -70980], ![-5267, 4063605, 0]], ![![-3670, -42755, -7436], ![-457, 425711, 0]], ![![-31414, -367122, -63851], ![-4872, 3655470, 0]]]
  g := ![![![1, 0, 0], ![-24, 229, 0], ![-206, 0, 229]], ![![0, 1, 0], ![-6, 23, 4], ![-20, -26, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![61, 108, 1]] ![![229, 0, 0], ![24, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![5496, 229, 0]], ![![13969, 24732, 229], ![1832, 2519, 458]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![24, 1, 0]]], ![![![61, 108, 1]], ![![8, 11, 2]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [5, 38, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 153, 52], [69, 79, 181], [0, 1]]
 g := ![![[20, 49, 19], [49, 100], [71, 162], [39, 2, 141], [113, 16], [221, 59, 29], [1]], ![[223, 228, 159, 30], [128, 8], [101, 33], [12, 35, 16, 171], [76, 131], [97, 1, 172, 208], [226, 126, 61, 109]], ![[148, 157, 108, 133], [17, 13], [120, 76], [66, 80, 52, 131], [225, 92], [131, 161, 134, 72], [184, 213, 215, 124]]]
 h' := ![![[133, 153, 52], [172, 221, 187], [157, 6, 10], [38, 175, 167], [6, 5, 181], [60, 186, 229], [228, 195, 202], [0, 1]], ![[69, 79, 181], [10, 180, 169], [157, 34, 170], [14, 36, 158], [114, 96, 113], [93, 106, 36], [71, 2, 2], [133, 153, 52]], ![[0, 1], [72, 65, 110], [200, 193, 53], [69, 22, 141], [90, 132, 172], [41, 174, 201], [224, 36, 29], [69, 79, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 50], []]
 b := ![[], [114, 196, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [5, 38, 31, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![139077933, -100684426, 57029779]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![596901, -432122, 244763]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [213, 220, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 211, 65], [55, 27, 174], [0, 1]]
 g := ![![[189, 217, 51], [23, 56, 225], [80, 164, 93], [111, 38, 34], [150, 5], [118, 9, 110], [1]], ![[29, 152, 11, 130], [14, 188, 198, 114], [136, 180, 62, 114], [57, 94, 187, 224], [31, 20], [150, 95, 215, 181], [61, 136, 32, 14]], ![[174, 128, 81, 12], [86, 30, 107, 109], [67, 55, 158, 88], [72, 43, 104, 102], [224, 5], [182, 8, 85, 170], [38, 73, 199, 225]]]
 h' := ![![[134, 211, 65], [120, 3, 23], [168, 133, 224], [18, 30, 136], [163, 187, 89], [200, 45, 31], [26, 19, 189], [0, 1]], ![[55, 27, 174], [145, 196, 99], [155, 146, 114], [115, 161, 125], [70, 4, 218], [69, 63, 177], [4, 179, 124], [134, 211, 65]], ![[0, 1], [3, 40, 117], [154, 199, 140], [146, 48, 217], [15, 48, 171], [40, 131, 31], [63, 41, 165], [55, 27, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230, 235], []]
 b := ![[], [157, 89, 217], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [213, 220, 50, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11950, 0, 0]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 0, 0]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![32, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![32, 1, 0]] 
 ![![241, 0, 0], ![32, 1, 0], ![114, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![32, 1, 0], ![2, 31, 4], ![152, -26, 34]]]
  hmulB := by decide  
  f := ![![![-24251, -385311, -49720], ![-4579, 2995630, 0]], ![![-3236, -51148, -6600], ![-481, 397650, 0]], ![![-11462, -182263, -23519], ![-2237, 1417020, 0]]]
  g := ![![![1, 0, 0], ![-32, 241, 0], ![-114, 0, 241]], ![![0, 1, 0], ![-6, 31, 4], ![-12, -26, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![69, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![69, 1, 0]] 
 ![![241, 0, 0], ![69, 1, 0], ![153, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![69, 1, 0], ![2, 68, 4], ![152, -26, 71]]]
  hmulB := by decide  
  f := ![![![2218, 87103, 5124], ![1205, -308721, 0]], ![![594, 24886, 1464], ![483, -88206, 0]], ![![1425, 55298, 3253], ![706, -195993, 0]]]
  g := ![![![1, 0, 0], ![-69, 241, 0], ![-153, 0, 241]], ![![0, 1, 0], ![-22, 68, 4], ![-37, -26, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-102, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-102, 1, 0]] 
 ![![241, 0, 0], ![139, 1, 0], ![25, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-102, 1, 0], ![2, -103, 4], ![152, -26, -100]]]
  hmulB := by decide  
  f := ![![![62707, -4185223, 162540], ![-43862, -9793035, 0]], ![![36163, -2413803, 93744], ![-25304, -5648076, 0]], ![![6529, -434152, 16861], ![-4493, -1015875, 0]]]
  g := ![![![1, 0, 0], ![-139, 241, 0], ![-25, 0, 241]], ![![-1, 1, 0], ![59, -103, 4], ![26, -26, -100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![32, 1, 0]] ![![241, 0, 0], ![69, 1, 0]]
  ![![241, 0, 0], ![-50, 25, 1]] where
 M := ![![![58081, 0, 0], ![16629, 241, 0]], ![![7712, 241, 0], ![2210, 100, 4]]]
 hmul := by decide  
 g := ![![![![241, 0, 0], ![0, 0, 0]], ![![69, 1, 0], ![0, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![10, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-50, 25, 1]] ![![241, 0, 0], ![-102, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-24582, 241, 0]], ![![-12050, 6025, 241], ![5302, -2651, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-102, 1, 0]]], ![![![-50, 25, 1]], ![![22, -11, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![11, 27, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![11, 27, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![11, 27, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![11, 27, 1], ![206, -42, 110], ![4205, -677, 40]]]
  hmulB := by decide  
  f := ![![![-10, -27, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -27, 251]], ![![0, 0, 1], ![-4, -12, 110], ![15, -7, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [42, 180, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 250], [0, 1]]
 g := ![![[76, 35], [145, 149], [205], [111, 68], [15, 243], [182, 190], [71, 1]], ![[51, 216], [182, 102], [205], [170, 183], [200, 8], [118, 61], [142, 250]]]
 h' := ![![[71, 250], [185, 81], [78, 20], [107, 74], [123, 90], [137, 69], [30, 230], [0, 1]], ![[0, 1], [163, 170], [243, 231], [90, 177], [238, 161], [16, 182], [45, 21], [71, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [222]]
 b := ![[], [201, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [42, 180, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4995, 3156, -664]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 84, -664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-110, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-110, 1, 0]] 
 ![![251, 0, 0], ![141, 1, 0], ![211, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-110, 1, 0], ![2, -111, 4], ![152, -26, -108]]]
  hmulB := by decide  
  f := ![![![3761, -269720, 9720], ![-2510, -609930, 0]], ![![2071, -151509, 5460], ![-1505, -342615, 0]], ![![3191, -226737, 8171], ![-2043, -512730, 0]]]
  g := ![![![1, 0, 0], ![-141, 251, 0], ![-211, 0, 251]], ![![-1, 1, 0], ![59, -111, 4], ![106, -26, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![11, 27, 1]] ![![251, 0, 0], ![-110, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-27610, 251, 0]], ![![2761, 6777, 251], ![-1004, -3012, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-110, 1, 0]]], ![![![11, 27, 1]], ![![-4, -12, 0]]]]
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


lemma PB253I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 252 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 252 (by omega)

def PB253I4 : PrimesBelowBoundCertificateInterval O 193 252 253 where
  m := 10
  g := ![2, 2, 2, 2, 3, 2, 1, 1, 3, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB253I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0]
    · exact ![I241N0, I241N1, I241N2]
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
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![227, 227, 227]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![13651919]
    · exact ![241, 241, 241]
    · exact ![63001, 251]
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
      exact NI227N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I197N1, I199N1, I211N1, I223N1, I227N0, I227N1, I227N2, I229N1, I241N0, I241N1, I241N2, I251N1]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N1], [I227N0, I227N1, I227N2], [I229N1], [], [], [I241N0, I241N1, I241N2], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
