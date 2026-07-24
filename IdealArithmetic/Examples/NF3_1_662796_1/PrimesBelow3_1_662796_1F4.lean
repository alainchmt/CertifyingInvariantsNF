
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![20, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![20, 1, 0]] 
 ![![197, 0, 0], ![20, 1, 0], ![74, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![20, 1, 0], ![-2, 22, 10], ![84, -23, 18]]]
  hmulB := by decide  
  f := ![![![-24877, 274763, 124890], ![-985, -2460333, 0]], ![![-2534, 27874, 12670], ![1, -249599, 0]], ![![-9354, 103210, 46913], ![-278, -924186, 0]]]
  g := ![![![1, 0, 0], ![-20, 197, 0], ![-74, 0, 197]], ![![0, 1, 0], ![-6, 22, 10], ![-4, -23, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![66, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![66, 1, 0]] 
 ![![197, 0, 0], ![66, 1, 0], ![142, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![66, 1, 0], ![-2, 68, 10], ![84, -23, 64]]]
  hmulB := by decide  
  f := ![![![-47, 1632, 240], ![0, -4728, 0]], ![![-16, 544, 80], ![1, -1576, 0]], ![![-58, 1176, 173], ![72, -3408, 0]]]
  g := ![![![1, 0, 0], ![-66, 197, 0], ![-142, 0, 197]], ![![0, 1, 0], ![-30, 68, 10], ![-38, -23, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-86, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-86, 1, 0]] 
 ![![197, 0, 0], ![111, 1, 0], ![26, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-86, 1, 0], ![-2, -84, 10], ![84, -23, -88]]]
  hmulB := by decide  
  f := ![![![-2155, -101391, 12070], ![591, -237779, 0]], ![![-1187, -57122, 6800], ![395, -133960, 0]], ![![-246, -13382, 1593], ![166, -31382, 0]]]
  g := ![![![1, 0, 0], ![-111, 197, 0], ![-26, 0, 197]], ![![-1, 1, 0], ![46, -84, 10], ![25, -23, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![20, 1, 0]] ![![197, 0, 0], ![66, 1, 0]]
  ![![197, 0, 0], ![53, -70, 1]] where
 M := ![![![38809, 0, 0], ![13002, 197, 0]], ![![3940, 197, 0], ![1318, 88, 10]]]
 hmul := by decide  
 g := ![![![![144, 70, -1], ![197, 0, 0]], ![![13, 71, -1], ![197, 0, 0]]], ![![![-33, 71, -1], ![197, 0, 0]], ![![4, 4, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![53, -70, 1]] ![![197, 0, 0], ![-86, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-16942, 197, 0]], ![![10441, -13790, 197], ![-4334, 5910, -788]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-86, 1, 0]]], ![![![53, -70, 1]], ![![-22, 30, -4]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![108, -24, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![108, -24, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![108, 175, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![108, -24, 1], ![132, 37, -242], ![-2045, 565, 134]]]
  hmulB := by decide  
  f := ![![![-107, 24, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -175, 199]], ![![0, -1, 1], ![132, 213, -242], ![-83, -115, 134]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [19, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 198], [0, 1]]
 g := ![![[83, 5], [43, 196], [66, 32], [115], [66], [49], [15, 1]], ![[158, 194], [197, 3], [148, 167], [115], [66], [49], [30, 198]]]
 h' := ![![[15, 198], [178, 123], [139, 185], [20, 119], [195, 151], [97, 128], [113, 7], [0, 1]], ![[0, 1], [33, 76], [128, 14], [14, 80], [72, 48], [27, 71], [19, 192], [15, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [139, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [19, 184, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1151, -499, -1480]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![809, 1299, -1480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![43, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![43, 1, 0]] 
 ![![199, 0, 0], ![43, 1, 0], ![65, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![43, 1, 0], ![-2, 45, 10], ![84, -23, 41]]]
  hmulB := by decide  
  f := ![![![47850, -1100815, -244620], ![4975, 4867938, 0]], ![![10312, -237831, -52850], ![1195, 1051715, 0]], ![![15616, -359563, -79901], ![1687, 1590030, 0]]]
  g := ![![![1, 0, 0], ![-43, 199, 0], ![-65, 0, 199]], ![![0, 1, 0], ![-13, 45, 10], ![-8, -23, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![108, -24, 1]] ![![199, 0, 0], ![43, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![8557, 199, 0]], ![![21492, -4776, 199], ![4776, -995, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![43, 1, 0]]], ![![![108, -24, 1]], ![![24, -5, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-89, -65, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-89, -65, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![122, 146, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-89, -65, 1], ![214, -242, -652], ![-5489, 1508, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -146, 211]], ![![-1, -1, 1], ![378, 450, -652], ![-37, -6, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [96, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [153, 210], [0, 1]]
 g := ![![[5, 11], [203, 109], [81], [203], [132, 101], [59], [153, 1]], ![[0, 200], [0, 102], [81], [203], [182, 110], [59], [95, 210]]]
 h' := ![![[153, 210], [135, 86], [13, 113], [68, 9], [199, 186], [5, 177], [82, 103], [0, 1]], ![[0, 1], [0, 125], [0, 98], [179, 202], [172, 25], [78, 34], [16, 108], [153, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [14, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [96, 58, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5753, 2548, -3584]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2045, 2492, -3584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![19, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![19, 1, 0]] 
 ![![211, 0, 0], ![19, 1, 0], ![192, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![19, 1, 0], ![-2, 21, 10], ![84, -23, 17]]]
  hmulB := by decide  
  f := ![![![4182, -44101, -21000], ![211, 443100, 0]], ![![359, -3970, -1890], ![212, 39879, 0]], ![![3802, -40130, -19109], ![230, 403200, 0]]]
  g := ![![![1, 0, 0], ![-19, 211, 0], ![-192, 0, 211]], ![![0, 1, 0], ![-11, 21, 10], ![-13, -23, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-89, -65, 1]] ![![211, 0, 0], ![19, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![4009, 211, 0]], ![![-18779, -13715, 211], ![-1477, -1477, -633]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![19, 1, 0]]], ![![![-89, -65, 1]], ![![-7, -7, -3]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-109, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-109, 1, 0]] 
 ![![223, 0, 0], ![114, 1, 0], ![60, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-109, 1, 0], ![-2, -107, 10], ![84, -23, -111]]]
  hmulB := by decide  
  f := ![![![8579, 505583, -47250], ![-1784, 1053675, 0]], ![![4395, 258409, -24150], ![-891, 538545, 0]], ![![2341, 136031, -12713], ![-413, 283500, 0]]]
  g := ![![![1, 0, 0], ![-114, 223, 0], ![-60, 0, 223]], ![![-1, 1, 0], ![52, -107, 10], ![42, -23, -111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-84, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-84, 1, 0]] 
 ![![223, 0, 0], ![139, 1, 0], ![203, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-84, 1, 0], ![-2, -82, 10], ![84, -23, -86]]]
  hmulB := by decide  
  f := ![![![-32771, -1436667, 175200], ![6021, -3906960, 0]], ![![-20411, -895457, 109200], ![3792, -2435160, 0]], ![![-29827, -1307818, 159487], ![5494, -3556560, 0]]]
  g := ![![![1, 0, 0], ![-139, 223, 0], ![-203, 0, 223]], ![![-1, 1, 0], ![42, -82, 10], ![93, -23, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-30, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-30, 1, 0]] 
 ![![223, 0, 0], ![193, 1, 0], ![5, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-30, 1, 0], ![-2, -28, 10], ![84, -23, -32]]]
  hmulB := by decide  
  f := ![![![-18435, -260630, 93080], ![1338, -2075684, 0]], ![![-15929, -225546, 80550], ![1339, -1796265, 0]], ![![-405, -5844, 2087], ![92, -46540, 0]]]
  g := ![![![1, 0, 0], ![-193, 223, 0], ![-5, 0, 223]], ![![-1, 1, 0], ![24, -28, 10], ![21, -23, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-109, 1, 0]] ![![223, 0, 0], ![-84, 1, 0]]
  ![![223, 0, 0], ![68, -86, 1]] where
 M := ![![![49729, 0, 0], ![-18732, 223, 0]], ![![-24307, 223, 0], ![9154, -191, 10]]]
 hmul := by decide  
 g := ![![![![155, 86, -1], ![223, 0, 0]], ![![-84, 1, 0], ![0, 0, 0]]], ![![![-109, 1, 0], ![0, 0, 0]], ![![-30, 89, -1], ![233, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![68, -86, 1]] ![![223, 0, 0], ![-30, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-6690, 223, 0]], ![![15164, -19178, 223], ![-1784, 2453, -892]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-30, 1, 0]]], ![![![68, -86, 1]], ![![-8, 11, -4]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [163, 92, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 80, 93], [62, 146, 134], [0, 1]]
 g := ![![[154, 21, 160], [63, 50, 1], [109, 161], [137, 48], [161, 23], [7, 165, 133], [1]], ![[182, 63, 62, 32], [135, 161, 216, 138], [178, 110], [2, 161], [218, 131], [32, 123, 170, 215], [86, 21, 162, 96]], ![[184, 42, 100, 133], [67, 63, 68, 44], [166, 40], [144, 81], [152, 188], [139, 226, 64, 172], [87, 6, 223, 131]]]
 h' := ![![[95, 80, 93], [173, 33, 29], [86, 167, 226], [104, 173, 191], [125, 116, 200], [221, 165, 134], [64, 135, 157], [0, 1]], ![[62, 146, 134], [198, 43, 39], [43, 127, 176], [1, 78, 164], [217, 207, 36], [148, 159, 178], [52, 208, 65], [95, 80, 93]], ![[0, 1], [218, 151, 159], [67, 160, 52], [148, 203, 99], [100, 131, 218], [70, 130, 142], [98, 111, 5], [62, 146, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 3], []]
 b := ![[], [27, 25, 205], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [163, 92, 70, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1072494415, -288800750, -114328550]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4724645, -1272250, -503650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![21, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![21, 1, 0]] 
 ![![229, 0, 0], ![21, 1, 0], ![66, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![21, 1, 0], ![-2, 23, 10], ![84, -23, 19]]]
  hmulB := by decide  
  f := ![![![24136, -278765, -121200], ![1145, 2775480, 0]], ![![2201, -25554, -11110], ![230, 254419, 0]], ![![6951, -80343, -34931], ![387, 799920, 0]]]
  g := ![![![1, 0, 0], ![-21, 229, 0], ![-66, 0, 229]], ![![0, 1, 0], ![-5, 23, 10], ![-3, -23, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![81, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![81, 1, 0]] 
 ![![229, 0, 0], ![81, 1, 0], ![129, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![81, 1, 0], ![-2, 83, 10], ![84, -23, 79]]]
  hmulB := by decide  
  f := ![![![13787, -605744, -72980], ![2290, 1671242, 0]], ![![4838, -214227, -25810], ![917, 591049, 0]], ![![7764, -341227, -41111], ![1297, 941442, 0]]]
  g := ![![![1, 0, 0], ![-81, 229, 0], ![-129, 0, 229]], ![![0, 1, 0], ![-35, 83, 10], ![-36, -23, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-102, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-102, 1, 0]] 
 ![![229, 0, 0], ![127, 1, 0], ![79, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-102, 1, 0], ![-2, -100, 10], ![84, -23, -104]]]
  hmulB := by decide  
  f := ![![![-4211, -231004, 23100], ![916, -528990, 0]], ![![-2255, -128103, 12810], ![688, -293349, 0]], ![![-1385, -79692, 7969], ![468, -182490, 0]]]
  g := ![![![1, 0, 0], ![-127, 229, 0], ![-79, 0, 229]], ![![-1, 1, 0], ![52, -100, 10], ![49, -23, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![21, 1, 0]] ![![229, 0, 0], ![81, 1, 0]]
  ![![229, 0, 0], ![-82, 102, 1]] where
 M := ![![![52441, 0, 0], ![18549, 229, 0]], ![![4809, 229, 0], ![1699, 104, 10]]]
 hmul := by decide  
 g := ![![![![229, 0, 0], ![0, 0, 0]], ![![81, 1, 0], ![0, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![11, -4, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-82, 102, 1]] ![![229, 0, 0], ![-102, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-23358, 229, 0]], ![![-18778, 23358, 229], ![8244, -10305, 916]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-102, 1, 0]]], ![![![-82, 102, 1]], ![![36, -45, 4]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)


lemma PB231I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 230 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 230 (by omega)

def PB231I4 : PrimesBelowBoundCertificateInterval O 193 230 231 where
  m := 6
  g := ![3, 2, 2, 3, 1, 3]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB231I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![11697083]
    · exact ![229, 229, 229]
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
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1, I223N0, I223N1, I223N2, I229N0, I229N1, I229N2]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [I223N0, I223N1, I223N2], [], [I229N0, I229N1, I229N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
