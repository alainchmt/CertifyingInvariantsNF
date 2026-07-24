
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![40, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![40, 1, 0]] 
 ![![197, 0, 0], ![40, 1, 0], ![165, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![40, 1, 0], ![0, 41, 2], ![246, 48, 40]]]
  hmulB := by decide  
  f := ![![![3401, 85, 0], ![-16745, 0, 0]], ![![680, 17, 0], ![-3348, 0, 0]], ![![2825, 50, -1], ![-13909, 99, 0]]]
  g := ![![![1, 0, 0], ![-40, 197, 0], ![-165, 0, 197]], ![![0, 1, 0], ![-10, 41, 2], ![-42, 48, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![75, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![75, 1, 0]] 
 ![![197, 0, 0], ![75, 1, 0], ![105, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![75, 1, 0], ![0, 76, 2], ![246, 48, 75]]]
  hmulB := by decide  
  f := ![![![9901, 132, 0], ![-26004, 0, 0]], ![![3675, 49, 0], ![-9652, 0, 0]], ![![5265, 32, -1], ![-13828, 99, 0]]]
  g := ![![![1, 0, 0], ![-75, 197, 0], ![-105, 0, 197]], ![![0, 1, 0], ![-30, 76, 2], ![-57, 48, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![81, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![81, 1, 0]] 
 ![![197, 0, 0], ![81, 1, 0], ![28, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![81, 1, 0], ![0, 82, 2], ![246, 48, 81]]]
  hmulB := by decide  
  f := ![![![2269, 28, 0], ![-5516, 0, 0]], ![![891, 11, 0], ![-2166, 0, 0]], ![![260, -38, -1], ![-632, 99, 0]]]
  g := ![![![1, 0, 0], ![-81, 197, 0], ![-28, 0, 197]], ![![0, 1, 0], ![-34, 82, 2], ![-30, 48, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![40, 1, 0]] ![![197, 0, 0], ![75, 1, 0]]
  ![![197, 0, 0], ![-76, 58, 1]] where
 M := ![![![38809, 0, 0], ![14775, 197, 0]], ![![7880, 197, 0], ![3000, 116, 2]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![75, 1, 0], ![0, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![16, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-76, 58, 1]] ![![197, 0, 0], ![81, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![15957, 197, 0]], ![![-14972, 11426, 197], ![-5910, 4728, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![81, 1, 0]]], ![![![-76, 58, 1]], ![![-30, 24, 1]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1271183, -383822, -62982]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-1271183, -383822, -62982]] 
 ![![199, 0, 0], ![0, 199, 0], ![152, 99, 1]] where
  M :=![![![-1271183, -383822, -62982], ![-15493572, -4678141, -767644], ![-86673426, -26170242, -4294319]]]
  hmulB := by decide  
  f := ![![![-2669, -374, 106]], ![![26076, 2045, -748]], ![![10406, 707, -279]]]
  g := ![![![41719, 29404, -62982], ![508484, 358385, -767644], ![2844538, 2004861, -4294319]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [115, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 198], [0, 1]]
 g := ![![[70, 45], [40, 111], [86, 169], [31], [29], [28], [109, 1]], ![[0, 154], [0, 88], [0, 30], [31], [29], [28], [19, 198]]]
 h' := ![![[109, 198], [176, 170], [60, 67], [175, 13], [77, 35], [167, 167], [2, 25], [0, 1]], ![[0, 1], [0, 29], [0, 132], [0, 186], [111, 164], [62, 32], [140, 174], [109, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [106, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [115, 90, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1960, 1507, 170]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-120, -77, 170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2669, 374, -106]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![2669, 374, -106]] 
 ![![199, 0, 0], ![1, 1, 0], ![198, 0, 1]] where
  M :=![![![2669, 374, -106], ![-26076, -2045, 748], ![105042, 4914, -2419]]]
  hmulB := by decide  
  f := ![![![1271183, 383822, 62982]], ![![84245, 25437, 4174]], ![![1700340, 513402, 84245]]]
  g := ![![![117, 374, -106], ![-865, -2045, 748], ![2910, 4914, -2419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-1271183, -383822, -62982]] ![![2669, 374, -106]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [37, 183, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 0, 27], [37, 210, 184], [0, 1]]
 g := ![![[42, 137, 43], [157, 46, 5], [162, 134], [42, 126], [65, 160, 184], [14, 123], [1]], ![[5, 150, 39, 77], [184, 123, 55, 28], [84, 109], [157, 184], [43, 203, 205, 29], [22, 194], [93, 177, 132, 60]], ![[47, 191, 74, 52], [144, 41, 118, 123], [56, 103], [50, 122], [74, 188, 37, 208], [43, 148], [21, 164, 2, 151]]]
 h' := ![![[134, 0, 27], [99, 155, 185], [170, 89, 146], [16, 194, 61], [127, 169, 45], [7, 99, 87], [174, 28, 171], [0, 1]], ![[37, 210, 184], [175, 126, 202], [29, 104, 147], [129, 29, 113], [175, 139, 87], [66, 114, 54], [6, 64, 163], [134, 0, 27]], ![[0, 1], [141, 141, 35], [97, 18, 129], [108, 199, 37], [108, 114, 79], [167, 209, 70], [80, 119, 88], [37, 210, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 145], []]
 b := ![[], [173, 41, 190], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [37, 183, 40, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2125825, 957096, 181460]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10075, 4536, 860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![76, -60, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![76, -60, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![76, 163, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![76, -60, 1], ![246, 64, -120], ![-14883, -2757, 124]]]
  hmulB := by decide  
  f := ![![![-75, 60, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -163, 223]], ![![0, -1, 1], ![42, 88, -120], ![-109, -103, 124]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [175, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 222], [0, 1]]
 g := ![![[128, 144], [198, 146], [219, 128], [51, 25], [16, 105], [169], [123, 1]], ![[0, 79], [93, 77], [130, 95], [4, 198], [220, 118], [169], [23, 222]]]
 h' := ![![[123, 222], [138, 211], [31, 102], [218, 103], [99, 5], [170, 128], [106, 13], [0, 1]], ![[0, 1], [0, 12], [89, 121], [176, 120], [45, 218], [81, 95], [144, 210], [123, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [169]]
 b := ![[], [211, 196]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [175, 100, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2252, 123, 76]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -55, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-103, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-103, 1, 0]] 
 ![![223, 0, 0], ![120, 1, 0], ![99, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-103, 1, 0], ![0, -102, 2], ![246, 48, -103]]]
  hmulB := by decide  
  f := ![![![10816, -105, 0], ![23415, 0, 0]], ![![5872, -57, 0], ![12712, 0, 0]], ![![4968, 3, -1], ![10755, 112, 0]]]
  g := ![![![1, 0, 0], ![-120, 223, 0], ![-99, 0, 223]], ![![-1, 1, 0], ![54, -102, 2], ![21, 48, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![76, -60, 1]] ![![223, 0, 0], ![-103, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-22969, 223, 0]], ![![16948, -13380, 223], ![-7582, 6244, -223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-103, 1, 0]]], ![![![76, -60, 1]], ![![-34, 28, -1]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![69, 61, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![69, 61, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![69, 61, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![69, 61, 1], ![246, 178, 122], ![14883, 3051, 117]]]
  hmulB := by decide  
  f := ![![![-68, -61, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -61, 227]], ![![0, 0, 1], ![-36, -32, 122], ![30, -18, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [221, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 226], [0, 1]]
 g := ![![[96, 189], [31, 210], [176], [57], [89], [135, 65], [122, 1]], ![[0, 38], [0, 17], [176], [57], [89], [120, 162], [17, 226]]]
 h' := ![![[122, 226], [186, 125], [109, 94], [142, 67], [150, 114], [129, 166], [51, 135], [0, 1]], ![[0, 1], [0, 102], [0, 133], [144, 160], [211, 113], [178, 61], [177, 92], [122, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [164, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [221, 105, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2172, 3825, 673]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-195, -164, 673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![105, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![105, 1, 0]] 
 ![![227, 0, 0], ![105, 1, 0], ![110, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![105, 1, 0], ![0, 106, 2], ![246, 48, 105]]]
  hmulB := by decide  
  f := ![![![7771, 74, 0], ![-16798, 0, 0]], ![![3675, 35, 0], ![-7944, 0, 0]], ![![3700, -18, -1], ![-7998, 114, 0]]]
  g := ![![![1, 0, 0], ![-105, 227, 0], ![-110, 0, 227]], ![![0, 1, 0], ![-50, 106, 2], ![-72, 48, 105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![69, 61, 1]] ![![227, 0, 0], ![105, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![23835, 227, 0]], ![![15663, 13847, 227], ![7491, 6583, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![105, 1, 0]]], ![![![69, 61, 1]], ![![33, 29, 1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![55, 98, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![55, 98, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![55, 98, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![55, 98, 1], ![246, 201, 196], ![23985, 4827, 103]]]
  hmulB := by decide  
  f := ![![![-54, -98, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -98, 229]], ![![0, 0, 1], ![-46, -83, 196], ![80, -23, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [173, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 228], [0, 1]]
 g := ![![[175, 184], [187], [22, 111], [187], [95], [91, 167], [182, 1]], ![[0, 45], [187], [72, 118], [187], [95], [28, 62], [135, 228]]]
 h' := ![![[182, 228], [179, 111], [87, 88], [33, 180], [211, 88], [58, 211], [116, 204], [0, 1]], ![[0, 1], [0, 118], [73, 141], [46, 49], [197, 141], [217, 18], [146, 25], [182, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [147, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [173, 47, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2018, 1593, 299]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, -121, 299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![33, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![33, 1, 0]] 
 ![![229, 0, 0], ![33, 1, 0], ![126, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![33, 1, 0], ![0, 34, 2], ![246, 48, 33]]]
  hmulB := by decide  
  f := ![![![3235, 98, 0], ![-22442, 0, 0]], ![![429, 13, 0], ![-2976, 0, 0]], ![![1752, 36, -1], ![-12154, 115, 0]]]
  g := ![![![1, 0, 0], ![-33, 229, 0], ![-126, 0, 229]], ![![0, 1, 0], ![-6, 34, 2], ![-24, 48, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![55, 98, 1]] ![![229, 0, 0], ![33, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![7557, 229, 0]], ![![12595, 22442, 229], ![2061, 3435, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![33, 1, 0]]], ![![![55, 98, 1]], ![![9, 15, 1]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [158, 116, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 103, 84], [155, 129, 149], [0, 1]]
 g := ![![[109, 95, 15], [195, 187], [138, 135], [228, 51, 210], [55, 187], [168, 84, 102], [1]], ![[223, 70, 40, 108], [14, 56], [145, 142], [114, 195, 170, 47], [218, 92], [166, 150, 126, 68], [96, 87, 111, 185]], ![[81, 112, 67, 137], [135, 129], [199, 60], [153, 146, 177, 189], [101, 55], [93, 140, 193, 12], [57, 174, 157, 48]]]
 h' := ![![[20, 103, 84], [27, 194, 134], [224, 146, 120], [91, 229, 169], [22, 65, 207], [18, 126, 120], [75, 117, 175], [0, 1]], ![[155, 129, 149], [176, 13, 30], [161, 0, 17], [2, 28, 29], [15, 175, 9], [21, 37, 201], [55, 159, 16], [20, 103, 84]], ![[0, 1], [98, 26, 69], [218, 87, 96], [111, 209, 35], [105, 226, 17], [174, 70, 145], [150, 190, 42], [155, 129, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 82], []]
 b := ![[], [37, 66, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [158, 116, 58, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![551214624, 184299971, 30487584]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2365728, 790987, 130848]
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [146, 231, 144, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 62, 148], [4, 176, 91], [0, 1]]
 g := ![![[204, 56, 87], [92, 88, 110], [132, 133, 15], [94, 37, 176], [225, 127], [17, 168, 182], [1]], ![[93, 235, 223, 221], [14, 232, 58, 94], [21, 76, 81, 41], [213, 44, 11, 41], [101, 218], [178, 215, 59, 21], [69, 155, 9, 235]], ![[23, 191, 162, 51], [80, 161, 160, 90], [102, 183, 233, 197], [63, 103, 136, 186], [49, 145], [210, 180, 199, 1], [117, 32, 4, 4]]]
 h' := ![![[91, 62, 148], [191, 237, 200], [87, 204, 189], [138, 194, 179], [231, 20, 43], [147, 31, 102], [93, 8, 95], [0, 1]], ![[4, 176, 91], [12, 216, 10], [68, 135, 121], [129, 215, 227], [7, 142, 12], [37, 40, 74], [207, 60, 218], [91, 62, 148]], ![[0, 1], [106, 25, 29], [26, 139, 168], [5, 69, 72], [114, 77, 184], [215, 168, 63], [190, 171, 165], [4, 176, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 4], []]
 b := ![[], [175, 90, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [146, 231, 144, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220597, 74807, 12667]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![923, 313, 53]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [225, 56, 240, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 212, 24], [67, 28, 217], [0, 1]]
 g := ![![[26, 213, 108], [41, 54], [30, 188], [231, 24], [154, 199, 177], [109, 130, 1], [1]], ![[169, 153, 94, 166], [36, 150], [222, 113], [202, 12], [122, 104, 50, 9], [53, 61, 19, 238], [124, 57, 103, 87]], ![[94, 26, 41, 75], [212, 24], [202, 48], [188, 82], [71, 53, 149, 161], [72, 191, 129, 5], [153, 191, 97, 154]]]
 h' := ![![[175, 212, 24], [46, 158, 146], [178, 171, 81], [105, 14, 46], [54, 219, 187], [57, 88, 211], [16, 185, 1], [0, 1]], ![[67, 28, 217], [92, 52, 168], [203, 220, 106], [5, 24, 178], [151, 238, 129], [30, 91, 67], [73, 114, 130], [175, 212, 24]], ![[0, 1], [99, 31, 168], [9, 91, 54], [174, 203, 17], [145, 25, 166], [128, 62, 204], [33, 183, 110], [67, 28, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 211], []]
 b := ![[], [136, 8, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [225, 56, 240, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6747759, 3122637, 633589]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27999, 12957, 2629]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [212, 102, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [230, 17, 131], [196, 233, 120], [0, 1]]
 g := ![![[96, 159, 207], [104, 175, 15], [22, 81], [42, 129, 113], [228, 78, 196], [53, 216, 3], [1]], ![[216, 191, 40, 211], [100, 23, 39, 152], [111, 161], [86, 17, 192, 208], [174, 109, 141, 69], [238, 37, 17, 225], [59, 196, 5, 135]], ![[24, 136, 233, 129], [77, 236, 98, 42], [6, 181], [46, 108, 11, 133], [14, 212, 181, 228], [14, 68, 55, 99], [62, 105, 218, 116]]]
 h' := ![![[230, 17, 131], [40, 157, 61], [210, 78, 39], [132, 148, 9], [107, 84, 149], [59, 21, 237], [39, 149, 175], [0, 1]], ![[196, 233, 120], [120, 154, 142], [155, 39, 229], [131, 211, 150], [111, 25, 39], [28, 66, 242], [68, 21, 54], [230, 17, 131]], ![[0, 1], [114, 191, 48], [52, 134, 234], [128, 143, 92], [165, 142, 63], [53, 164, 23], [197, 81, 22], [196, 233, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 231], []]
 b := ![[], [94, 100, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [212, 102, 76, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14140336, -4186680, -645572]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56336, -16680, -2572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![2, -67, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![2, -67, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![2, 190, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![2, -67, 1], ![246, -17, -134], ![-16605, -3093, 50]]]
  hmulB := by decide  
  f := ![![![-1, 67, -1], ![257, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -190, 257]], ![![0, -1, 1], ![2, 99, -134], ![-65, -49, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [123, 185, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 256], [0, 1]]
 g := ![![[200, 140], [68], [36], [213], [207], [231], [44], [1]], ![[0, 117], [68], [36], [213], [207], [231], [44], [1]]]
 h' := ![![[72, 256], [121, 59], [2, 140], [33, 251], [180, 133], [202, 174], [208, 105], [134, 72], [0, 1]], ![[0, 1], [0, 198], [59, 117], [115, 6], [247, 124], [137, 83], [58, 152], [178, 185], [72, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218]]
 b := ![[], [188, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [123, 185, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2574, 123, 259]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -191, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-123, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-123, 1, 0]] 
 ![![257, 0, 0], ![134, 1, 0], ![207, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-123, 1, 0], ![0, -122, 2], ![246, 48, -123]]]
  hmulB := by decide  
  f := ![![![24109, -196, 0], ![50372, 0, 0]], ![![12670, -103, 0], ![26472, 0, 0]], ![![19587, -98, -1], ![40924, 129, 0]]]
  g := ![![![1, 0, 0], ![-134, 257, 0], ![-207, 0, 257]], ![![-1, 1, 0], ![62, -122, 2], ![75, 48, -123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![2, -67, 1]] ![![257, 0, 0], ![-123, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-31611, 257, 0]], ![![514, -17219, 257], ![0, 8224, -257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-123, 1, 0]]], ![![![2, -67, 1]], ![![0, 32, -1]]]]
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


lemma PB278I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB278I4 : PrimesBelowBoundCertificateInterval O 193 257 278 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB278I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0]
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
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![15813251]
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
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N0, I197N1, I197N2, I199N1, I223N1, I227N1, I229N1, I257N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [], [I223N1], [I227N1], [I229N1], [], [], [], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
