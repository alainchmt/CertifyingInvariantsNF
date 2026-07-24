
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15893202417548, -2193930337690, 510992070687]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-15893202417548, -2193930337690, 510992070687]] 
 ![![197, 0, 0], ![0, 197, 0], ![133, 166, 1]] where
  M :=![![![-15893202417548, -2193930337690, 510992070687], ![107819326914957, 4546480409932, -2193930337690], ![-462919301252590, 20062113407357, 4546480409932]]]
  hmulB := by decide  
  f := ![![![-328352098276514042155482, -102671280068253101318687, -12640177094555960170928]], ![![-2667077366951307596065808, -833959182058752448992602, -102671280068253101318687]], ![![-2579032041010633669704803, -806428594114274115010003, -99281904705404619140244]]]
  g := ![![![-425660648827, -441718853156, 510992070687], ![2028487623491, 1871771149576, -2193930337690], ![-5419295410018, -3729206267215, 4546480409932]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [78, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 196], [0, 1]]
 g := ![![[176, 104], [190], [156, 168], [163], [51], [135], [62, 1]], ![[123, 93], [190], [131, 29], [163], [51], [135], [124, 196]]]
 h' := ![![[62, 196], [101, 164], [46, 105], [42, 103], [99, 44], [149, 53], [89, 23], [0, 1]], ![[0, 1], [25, 33], [55, 92], [124, 94], [69, 153], [86, 144], [136, 174], [62, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [80, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [78, 135, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![500, 156, -94]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 80, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![328352098276514042155482, 102671280068253101318687, 12640177094555960170928]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![328352098276514042155482, 102671280068253101318687, 12640177094555960170928]] 
 ![![197, 0, 0], ![31, 1, 0], ![24, 0, 1]] where
  M :=![![![328352098276514042155482, 102671280068253101318687, 12640177094555960170928], ![2667077366951307596065808, 833959182058752448992602, 102671280068253101318687], ![21663640094401404378242957, 6773928569681431648813288, 833959182058752448992602]]]
  hmulB := by decide  
  f := ![![![15893202417548, 2193930337690, -510992070687]], ![![1953654558523, 322159188114, -69273217531]], ![![4286071874486, 165442714199, -85331421860]]]
  g := ![![![-16029552457404442349371, 102671280068253101318687, 12640177094555960170928], ![-130201868012731435301286, 833959182058752448992602, 102671280068253101318687], ![-1057579522513365662491327, 6773928569681431648813288, 833959182058752448992602]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-15893202417548, -2193930337690, 510992070687]] ![![328352098276514042155482, 102671280068253101318687, 12640177094555960170928]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [193, 49, 161, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 153, 80], [113, 45, 119], [0, 1]]
 g := ![![[87, 175, 50], [118, 21, 90], [10, 195, 32], [47, 18], [2, 13], [5, 51], [1]], ![[95, 20, 17, 18], [50, 178, 10, 51], [98, 193, 110, 10], [183, 2], [167, 144], [112, 43], [41, 50, 130, 172]], ![[192, 111, 99, 30], [12, 20, 64, 170], [141, 55, 172, 95], [65, 32], [0, 175], [39, 90], [190, 99, 172, 27]]]
 h' := ![![[124, 153, 80], [111, 133, 99], [60, 140, 17], [183, 67, 80], [189, 66, 60], [66, 70, 150], [6, 150, 38], [0, 1]], ![[113, 45, 119], [84, 3, 170], [175, 167, 25], [55, 21, 5], [56, 137, 20], [192, 36, 12], [52, 131, 178], [124, 153, 80]], ![[0, 1], [141, 63, 129], [88, 91, 157], [92, 111, 114], [10, 195, 119], [127, 93, 37], [93, 117, 182], [113, 45, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 142], []]
 b := ![[], [186, 94, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [193, 49, 161, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![344867, 601378, 89948]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1733, 3022, 452]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![211, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![211, 40, 0]]]
  hmulB := by decide  
  f := ![![![-40, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 40, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, 0, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-40, 0, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![171, 0, 1]] where
  M :=![![![-40, 0, 1], ![211, 0, 0], ![0, 211, 0]]]
  hmulB := by decide  
  f := ![![![0, 1, 0]], ![![0, 0, 1]], ![![1, 1, 0]]]
  g := ![![![-1, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [15, 208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 210], [0, 1]]
 g := ![![[42, 139], [176, 193], [83], [58], [71, 14], [36], [3, 1]], ![[37, 72], [122, 18], [83], [58], [113, 197], [36], [6, 210]]]
 h' := ![![[3, 210], [103, 75], [11, 68], [74, 100], [201, 67], [8, 15], [166, 205], [0, 1]], ![[0, 1], [117, 136], [4, 143], [163, 111], [191, 144], [53, 196], [148, 6], [3, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [62, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [15, 208, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9623, 211, -39]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 1, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![-40, 0, 1]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1309471, 117084, -34262]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![1309471, 117084, -34262]] 
 ![![223, 0, 0], ![0, 223, 0], ![42, 159, 1]] where
  M :=![![![1309471, 117084, -34262], ![-7229282, -61009, 117084], ![24704724, -2545922, -61009]]]
  hmulB := by decide  
  f := ![![![-1353402823, -423190840, -52100326]], ![![-10993168786, -3437415863, -423190840]], ![![-8493497860, -2655802421, -326964005]]]
  g := ![![![12325, 24954, -34262], ![-54470, -83755, 117084], ![122274, 32083, -61009]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [120, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 222], [0, 1]]
 g := ![![[44, 210], [37, 128], [143, 211], [123, 132], [125, 83], [211], [72, 1]], ![[0, 13], [110, 95], [171, 12], [38, 91], [80, 140], [211], [144, 222]]]
 h' := ![![[72, 222], [20, 136], [11, 120], [181, 65], [164, 191], [6, 200], [57, 158], [0, 1]], ![[0, 1], [0, 87], [177, 103], [178, 158], [90, 32], [134, 23], [60, 65], [72, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [99, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [120, 151, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-994, 1812, -98]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 78, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1353402823, -423190840, -52100326]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-1353402823, -423190840, -52100326]] 
 ![![223, 0, 0], ![64, 1, 0], ![141, 0, 1]] where
  M :=![![![-1353402823, -423190840, -52100326], ![-10993168786, -3437415863, -423190840], ![-89293267240, -27920802386, -3437415863]]]
  hmulB := by decide  
  f := ![![![1309471, 117084, -34262]], ![![343394, 33329, -9308]], ![![938745, 62614, -21937]]]
  g := ![![![148327161, -423190840, -52100326], ![1204804282, -3437415863, -423190840], ![9786160189, -27920802386, -3437415863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![1309471, 117084, -34262]] ![![-1353402823, -423190840, -52100326]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [199, 19, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 192, 193], [131, 34, 34], [0, 1]]
 g := ![![[33, 193, 181], [208, 10, 214], [48, 209], [17, 182], [215, 219], [76, 201, 44], [1]], ![[10, 67, 148, 13], [73, 24, 51, 226], [98, 103], [113, 171], [65, 26], [189, 85, 159, 14], [57, 104, 208, 194]], ![[165, 115, 59, 29], [177, 159, 3, 213], [8, 108], [212, 167], [171, 77], [221, 92, 149, 99], [140, 122, 183, 33]]]
 h' := ![![[16, 192, 193], [149, 212, 33], [5, 111, 206], [134, 76, 182], [79, 124, 78], [85, 201, 30], [28, 208, 147], [0, 1]], ![[131, 34, 34], [35, 112, 43], [215, 113, 52], [167, 70, 199], [194, 8, 25], [155, 225, 88], [17, 146, 196], [16, 192, 193]], ![[0, 1], [72, 130, 151], [96, 3, 196], [107, 81, 73], [46, 95, 124], [5, 28, 109], [171, 100, 111], [131, 34, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [173, 200], []]
 b := ![[], [90, 191, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [199, 19, 80, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36093, 908, 908]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-159, 4, 4]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65105076209, -20357480730, -2506272070]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-65105076209, -20357480730, -2506272070]] 
 ![![229, 0, 0], ![140, 1, 0], ![94, 0, 1]] where
  M :=![![![-65105076209, -20357480730, -2506272070], ![-528823406770, -165355959009, -20357480730], ![-4295428434030, -1343122635970, -165355959009]]]
  hmulB := by decide  
  f := ![![![-8403981, -961330, 245730]], ![![-4911390, -581489, 146030]], ![![-4335436, -336110, 107091]]]
  g := ![![![13190095199, -20357480730, -2506272070], ![107138052590, -165355959009, -20357480730], ![870241051304, -1343122635970, -165355959009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![854971086458227662460, 267337947065861697220, 32912796964848576149]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![854971086458227662460, 267337947065861697220, 32912796964848576149]] 
 ![![229, 0, 0], ![144, 1, 0], ![103, 0, 1]] where
  M :=![![![854971086458227662460, 267337947065861697220, 32912796964848576149], ![6944600159583049567439, 2171482965052170708420, 267337947065861697220], ![56408306830896818113420, 17638118042217517456239, 2171482965052170708420]]]
  hmulB := by decide  
  f := ![![![1167040940820, 40622051211, -22689746180]], ![![712953532900, 26676971476, -14090399121]], ![![562342662489, 4460335717, -9072457480]]]
  g := ![![![-179177778945001135723, 267337947065861697220, 32912796964848576149], ![-1455391944784774180169, 2171482965052170708420, 267337947065861697220], ![-11821587059601743574464, 17638118042217517456239, 2171482965052170708420]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8182092200311923440032921334346, -2558430064104700522422768130912, -314976194636138462981373711405]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-8182092200311923440032921334346, -2558430064104700522422768130912, -314976194636138462981373711405]] 
 ![![229, 0, 0], ![174, 1, 0], ![181, 0, 1]] where
  M :=![![![-8182092200311923440032921334346, -2558430064104700522422768130912, -314976194636138462981373711405], ![-66459977068225215689069853106455, -20781139985757461959287869790546, -2558430064104700522422768130912], ![-539828743526091810231204075622432, -168797179632413236585980578342935, -20781139985757461959287869790546]]]
  hmulB := by decide  
  f := ![![![-94691581800671396, -10709324462715723, 2753682031425386]], ![![-69411826745354002, -8069723829939702, 2045551742381229]], ![![-84711108155260001, -7797964181787853, 2243983175302790]]]
  g := ![![![2157185284642126765332564957243, -2558430064104700522422768130912, -314976194636138462981373711405], ![17521983502430235632251268655649, -20781139985757461959287869790546, -2558430064104700522422768130912], ![142324309388366427818168213921996, -168797179632413236585980578342935, -20781139985757461959287869790546]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-65105076209, -20357480730, -2506272070]] ![![854971086458227662460, 267337947065861697220, 32912796964848576149]]
  ![![-338412085592888204552839144544010, -105816902650426207246402035130310, -13027444366229891525712189139141]] where
 M := ![![![-338412085592888204552839144544010, -105816902650426207246402035130310, -13027444366229891525712189139141]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-338412085592888204552839144544010, -105816902650426207246402035130310, -13027444366229891525712189139141]] ![![-8182092200311923440032921334346, -2558430064104700522422768130912, -314976194636138462981373711405]]
  ![![229, 0, 0]] where
 M := ![![![16834096733176753177166134726230626292376428056186996678977529422, 5263795387512771991489654656085627244159791381042715769670805215, 648042041001508656163624618811002821412005449772697126840937756]]]
 hmul := by decide  
 g := ![![![![73511339446186695096795348149478717433958201118720509515185718, 22986006059007737954103295441421953031265464546038060129566835, 2829877908303531249622814929305689176471639518658066056073964]]]]
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
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80061, 25034, 3082]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![80061, 25034, 3082]] 
 ![![233, 0, 0], ![0, 233, 0], ![95, 169, 1]] where
  M :=![![![80061, 25034, 3082], ![650302, 203341, 25034], ![5282174, 1651662, 203341]]]
  hmulB := by decide  
  f := ![![![-619, -70, 18]], ![![3798, 101, -70]], ![![2439, 49, -43]]]
  g := ![![![-913, -2128, 3082], ![-7416, -17285, 25034], ![-60237, -140399, 203341]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [164, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [231, 232], [0, 1]]
 g := ![![[54, 37], [55], [31], [181, 204], [31], [183, 203], [231, 1]], ![[213, 196], [55], [31], [6, 29], [31], [10, 30], [229, 232]]]
 h' := ![![[231, 232], [74, 152], [70, 145], [140, 168], [203, 196], [45, 65], [95, 73], [0, 1]], ![[0, 1], [3, 81], [13, 88], [37, 65], [44, 37], [148, 168], [182, 160], [231, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [223]]
 b := ![[], [228, 228]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [164, 2, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8185, 1807, 405]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -286, 405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-619, -70, 18]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-619, -70, 18]] 
 ![![233, 0, 0], ![64, 1, 0], ![98, 0, 1]] where
  M :=![![![-619, -70, 18], ![3798, 101, -70], ![-14770, 998, 101]]]
  hmulB := by decide  
  f := ![![![80061, 25034, 3082]], ![![24782, 7749, 954]], ![![56344, 17618, 2169]]]
  g := ![![![9, -70, 18], ![18, 101, -70], ![-380, 998, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![80061, 25034, 3082]] ![![-619, -70, 18]]
  ![![233, 0, 0]] where
 M := ![![![233, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [205, 195, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [219, 141, 150], [176, 97, 89], [0, 1]]
 g := ![![[140, 14, 127], [136, 79, 3], [73, 224, 165], [37, 211, 20], [226, 161], [160, 6, 197], [1]], ![[50, 87, 51, 66], [86, 30, 116, 66], [107, 52, 56, 49], [151, 87, 121, 232], [210, 161], [37, 144, 20, 91], [220, 96, 11, 81]], ![[89, 201, 202, 69], [26, 45, 4, 217], [114, 74, 90, 41], [192, 235, 179, 39], [155, 166], [172, 33, 165, 203], [3, 180, 126, 158]]]
 h' := ![![[219, 141, 150], [83, 165, 137], [92, 218, 106], [63, 95, 72], [178, 195, 177], [182, 35, 20], [34, 44, 156], [0, 1]], ![[176, 97, 89], [210, 132, 38], [231, 5, 201], [60, 46, 202], [95, 106, 53], [155, 178, 20], [197, 26, 222], [219, 141, 150]], ![[0, 1], [211, 181, 64], [119, 16, 171], [34, 98, 204], [105, 177, 9], [136, 26, 199], [49, 169, 100], [176, 97, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 106], []]
 b := ![[], [134, 196, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [205, 195, 83, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64052, -9321, 3107]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-268, -39, 13]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56320495668040, -6528120086252, 1657337091223]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-56320495668040, -6528120086252, 1657337091223]] 
 ![![241, 0, 0], ![0, 241, 0], ![119, 20, 1]] where
  M :=![![![-56320495668040, -6528120086252, 1657337091223], ![349698126248053, 9972987980880, -6528120086252], ![-1377433338199172, 88573322797973, 9972987980880]]]
  hmulB := by decide  
  f := ![![![-2811940983113305717744156, -879256084331456051565779, -108247921035241579998304]], ![![-22840311338435973379642144, -7141857824522968917676316, -879256084331456051565779]], ![![-4053735425531701555538493, -1267548486463057526689325, -156051793005584389911992]]]
  g := ![![![-1052048172297, -164625983032, 1657337091223], ![4674458159801, 583134397120, -6528120086252], ![-10639912481012, -460109696347, 9972987980880]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [188, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 240], [0, 1]]
 g := ![![[224, 50], [94], [169], [47], [152, 49], [53, 82], [63, 1]], ![[0, 191], [94], [169], [47], [106, 192], [158, 159], [126, 240]]]
 h' := ![![[63, 240], [182, 131], [206, 217], [86, 228], [103, 23], [158, 234], [206, 166], [0, 1]], ![[0, 1], [0, 110], [140, 24], [231, 13], [106, 218], [199, 7], [60, 75], [63, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218]]
 b := ![[], [61, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [188, 178, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1032, 1182, 517]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -38, 517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2811940983113305717744156, 879256084331456051565779, 108247921035241579998304]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![2811940983113305717744156, 879256084331456051565779, 108247921035241579998304]] 
 ![![241, 0, 0], ![221, 1, 0], ![82, 0, 1]] where
  M :=![![![2811940983113305717744156, 879256084331456051565779, 108247921035241579998304], ![22840311338435973379642144, 7141857824522968917676316, 879256084331456051565779], ![185523033793937226880379369, 58010554711694215442273304, 7141857824522968917676316]]]
  hmulB := by decide  
  f := ![![![56320495668040, 6528120086252, -1657337091223]], ![![50195566043107, 5944985689132, -1492711108191]], ![![24878481257172, 1853661926451, -605288918926]]]
  g := ![![![-831452212361113241652091, 879256084331456051565779, 108247921035241579998304], ![-6753565422391367442552770, 7141857824522968917676316, 879256084331456051565779], ![-54856605390462107207931447, 58010554711694215442273304, 7141857824522968917676316]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-56320495668040, -6528120086252, 1657337091223]] ![![2811940983113305717744156, 879256084331456051565779, 108247921035241579998304]]
  ![![241, 0, 0]] where
 M := ![![![-241, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45180508, 35879554, -3732449]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-45180508, 35879554, -3732449]] 
 ![![251, 0, 0], ![0, 251, 0], ![178, 59, 1]] where
  M :=![![![-45180508, 35879554, -3732449], ![-787546739, -194478468, 35879554], ![7570585894, 647635421, -194478468]]]
  hmulB := by decide  
  f := ![![![-58107587472290, -18169460218993, -2236898134784]], ![![-471985506439424, -147583512863650, -18169460218993]], ![![-167426500223909, -52352012323248, -6445217266039]]]
  g := ![![![2466914, 1020295, -3732449], ![-28582101, -9208654, 35879554], ![168078698, 48294283, -194478468]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [43, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 250], [0, 1]]
 g := ![![[86, 196], [133, 45], [201], [127, 174], [43, 190], [156, 164], [67, 1]], ![[166, 55], [136, 206], [201], [239, 77], [223, 61], [100, 87], [134, 250]]]
 h' := ![![[67, 250], [54, 14], [98, 203], [61, 204], [159, 225], [69, 230], [131, 179], [0, 1]], ![[0, 1], [239, 237], [145, 48], [175, 47], [174, 26], [168, 21], [76, 72], [67, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [167, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [43, 184, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8025, -2636, 636]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-483, -160, 636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58107587472290, 18169460218993, 2236898134784]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![58107587472290, 18169460218993, 2236898134784]] 
 ![![251, 0, 0], ![192, 1, 0], ![33, 0, 1]] where
  M :=![![![58107587472290, 18169460218993, 2236898134784], ![471985506439424, 147583512863650, 18169460218993], ![3833756106207523, 1198763915199144, 147583512863650]]]
  hmulB := by decide  
  f := ![![![45180508, -35879554, 3732449]], ![![37698025, -26670900, 2712154]], ![![-24221630, -7297453, 1265535]]]
  g := ![![![-13961141087738, 18169460218993, 2236898134784], ![-113400960759395, 147583512863650, 18169460218993], ![-921112237197325, 1198763915199144, 147583512863650]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-45180508, 35879554, -3732449]] ![![58107587472290, 18169460218993, 2236898134784]]
  ![![251, 0, 0]] where
 M := ![![![-251, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [170, 154, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 138, 76], [37, 118, 181], [0, 1]]
 g := ![![[190, 144, 31], [148, 144], [180, 226], [145, 98], [108, 70], [102, 193], [119, 1], []], ![[221, 8, 3, 214], [168, 84], [92, 26], [149, 137], [60, 25], [251, 22], [11, 46], [28, 122]], ![[227, 5, 27, 91], [171, 111], [204, 168], [156, 26], [147, 62], [85, 111], [244, 26], [180, 122]]]
 h' := ![![[82, 138, 76], [57, 255, 51], [51, 151, 245], [140, 234, 212], [142, 44, 94], [68, 195, 29], [73, 8, 129], [0, 0, 1], [0, 1]], ![[37, 118, 181], [84, 178, 212], [173, 20, 37], [81, 99, 138], [242, 126, 44], [26, 163, 252], [169, 151, 153], [165, 150, 118], [82, 138, 76]], ![[0, 1], [59, 81, 251], [208, 86, 232], [129, 181, 164], [101, 87, 119], [231, 156, 233], [17, 98, 232], [67, 107, 138], [37, 118, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 43], []]
 b := ![[], [208, 20, 226], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [170, 154, 138, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28013, 31611, 12593]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-109, 123, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB276I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB276I4 : PrimesBelowBoundCertificateInterval O 193 257 276 where
  m := 11
  g := ![2, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB276I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1]
    · exact ![I257N0]
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
    · exact ![211, 44521]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![229, 229, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![58081, 241]
    · exact ![63001, 251]
    · exact ![16974593]
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
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N1, I211N0, I223N1, I229N0, I229N1, I229N2, I233N1, I241N1, I251N1]
  Il := ![[I197N1], [], [I211N0], [I223N1], [], [I229N0, I229N1, I229N2], [I233N1], [], [I241N1], [I251N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
