
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![134035426, 12963993, -14795454]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![134035426, 12963993, -14795454]] 
 ![![197, 0, 0], ![0, 197, 0], ![63, 12, 1]] where
  M :=![![![134035426, 12963993, -14795454], ![-2655712110, 34130170, 98217561], ![1114797129, -201498207, 84154681]]]
  hmulB := by decide  
  f := ![![![115039979727101, 9595313489085, 9026716413849]], ![![1690270357690707, 140982934818176, 132628597621482]], ![![152558255222211, 12724657007742, 11970621950293]]]
  g := ![![![5411924, 967053, -14795454], ![-44890449, -5809546, 98217561], ![-21253542, -6149007, 84154681]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [116, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 196], [0, 1]]
 g := ![![[101, 107], [23], [168, 158], [26], [143], [101], [104, 1]], ![[0, 90], [23], [52, 39], [26], [143], [101], [11, 196]]]
 h' := ![![[104, 196], [118, 86], [15, 107], [136, 143], [0, 82], [146, 145], [150, 62], [0, 1]], ![[0, 1], [0, 111], [111, 90], [36, 54], [57, 115], [57, 52], [97, 135], [104, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [125, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [116, 93, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6023, 2151, -264]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![115, 27, -264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115039979727101, -9595313489085, -9026716413849]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-115039979727101, -9595313489085, -9026716413849]] 
 ![![197, 0, 0], ![62, 1, 0], ![92, 0, 1]] where
  M :=![![![-115039979727101, -9595313489085, -9026716413849], ![-1690270357690707, -140982934818176, -132628597621482], ![-2523213263679720, -210457462894707, -197986218677450]]]
  hmulB := by decide  
  f := ![![![-134035426, -12963993, 14795454]], ![![-28702966, -4253288, 4157871]], ![![-68254093, -5031417, 6482371]]]
  g := ![![![6651407952641, -9595313489085, -9026716413849], ![97728439503617, -140982934818176, -132628597621482], ![145887723624962, -210457462894707, -197986218677450]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![134035426, 12963993, -14795454]] ![![-115039979727101, -9595313489085, -9026716413849]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [109, 130, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 187, 56], [163, 11, 143], [0, 1]]
 g := ![![[28, 9, 62], [23, 188, 126], [165, 122, 187], [106, 117], [172, 33], [96, 62], [1]], ![[73, 31, 100, 160], [124, 74, 150, 63], [158, 70, 46, 28], [], [152, 158], [3, 40], [154, 34, 191, 98]], ![[46, 111, 169, 84], [198, 135, 31, 176], [87, 36, 181, 164], [180, 117], [12, 102], [46, 89], [66, 49, 152, 101]]]
 h' := ![![[132, 187, 56], [80, 53, 96], [124, 9, 46], [176, 27, 171], [136, 4, 52], [24, 147, 113], [90, 69, 96], [0, 1]], ![[163, 11, 143], [122, 131, 44], [144, 131, 15], [47, 41, 10], [131, 127], [111, 82, 122], [55, 138, 144], [132, 187, 56]], ![[0, 1], [48, 15, 59], [19, 59, 138], [83, 131, 18], [179, 68, 147], [33, 169, 163], [79, 191, 158], [163, 11, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188, 49], []]
 b := ![[], [190, 72, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [109, 130, 103, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44100191, 3932837, 607547]
  a := ![9, -7, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![221609, 19763, 3053]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6697906, 66136, -349679]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![6697906, 66136, -349679]] 
 ![![211, 0, 0], ![0, 211, 0], ![107, 124, 1]] where
  M :=![![![6697906, 66136, -349679], ![-63726713, 4817239, -321541], ![-17619827, -5963542, 4798240]]]
  hmulB := by decide  
  f := ![![![-100458509958, -8379094798, -7882568155]], ![![-1476026351557, -123113161137, -115817747243]], ![![-928813842653, -77470980214, -72880221109]]]
  g := ![![![209069, 205812, -349679], ![-138966, 211793, -321541], ![-2516737, -2848082, 4798240]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [205, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 210], [0, 1]]
 g := ![![[45, 107], [173, 185], [103], [154], [113, 188], [83], [59, 1]], ![[28, 104], [116, 26], [103], [154], [22, 23], [83], [118, 210]]]
 h' := ![![[59, 210], [194, 23], [10, 117], [206, 174], [45, 187], [58, 140], [143, 111], [0, 1]], ![[0, 1], [74, 188], [161, 94], [133, 37], [106, 24], [89, 71], [151, 100], [59, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [7, 175]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [205, 152, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10451744, 4548054, 1605827]
  a := ![-196, 67, -523]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-764795, -922154, 1605827]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100458509958, 8379094798, 7882568155]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![100458509958, 8379094798, 7882568155]] 
 ![![211, 0, 0], ![110, 1, 0], ![148, 0, 1]] where
  M :=![![![100458509958, 8379094798, 7882568155], ![1476026351557, 123113161137, 115817747243], ![2203392641209, 183781700780, 172891203282]]]
  hmulB := by decide  
  f := ![![![-6697906, -66136, 349679]], ![![-3189777, -57309, 183821]], ![![-4614551, -18126, 222532]]]
  g := ![![![-9421146942, 8379094798, 7882568155], ![-138423924007, 123113161137, 115817747243], ![-206637405357, 183781700780, 172891203282]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![6697906, 66136, -349679]] ![![100458509958, 8379094798, 7882568155]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [205, 58, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 133, 120], [75, 89, 103], [0, 1]]
 g := ![![[190, 55, 81], [142, 16, 156], [208, 64, 112], [89, 207, 139], [85, 73, 89], [112, 200], [1]], ![[208, 91, 160, 36], [109, 137, 222, 175], [52, 27, 173, 100], [114, 65, 100, 148], [172, 60, 132, 148], [22, 131], [187, 123, 192, 196]], ![[18, 166, 126, 24], [117, 190, 101, 12], [41, 32, 178, 157], [144, 61, 141, 79], [96, 173, 155, 107], [122, 200], [61, 93, 93, 27]]]
 h' := ![![[75, 133, 120], [103, 59, 9], [176, 135, 143], [41, 194, 104], [192, 10, 94], [110, 145, 138], [18, 165, 150], [0, 1]], ![[75, 89, 103], [184, 60, 76], [3, 178, 160], [148, 142, 201], [97, 180, 200], [127, 160, 23], [203, 168, 146], [75, 133, 120]], ![[0, 1], [39, 104, 138], [53, 133, 143], [83, 110, 141], [94, 33, 152], [208, 141, 62], [165, 113, 150], [75, 89, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 6], []]
 b := ![[], [31, 111, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [205, 58, 73, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47448379, -2259882, -300158]
  a := ![-9, 6, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212773, -10134, -1346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-51, 89, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-51, 89, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![176, 89, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-51, 89, 1], ![539, -224, 982], ![16372, 463, 222]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-176, -89, 227]], ![![-1, 0, 1], ![-759, -386, 982], ![-100, -85, 222]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [110, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [197, 226], [0, 1]]
 g := ![![[186, 97], [170, 169], [23], [59], [112], [224, 77], [197, 1]], ![[0, 130], [94, 58], [23], [59], [112], [184, 150], [167, 226]]]
 h' := ![![[197, 226], [141, 209], [219, 13], [222, 134], [105, 115], [103, 148], [122, 109], [0, 1]], ![[0, 1], [0, 18], [56, 214], [61, 93], [60, 112], [203, 79], [30, 118], [197, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [222, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [110, 30, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6269, 2088, 429]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-305, -159, 429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-74, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-74, 1, 0]] 
 ![![227, 0, 0], ![153, 1, 0], ![5, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-74, 1, 0], ![4, -76, 11], ![183, 5, -71]]]
  hmulB := by decide  
  f := ![![![8937, -192264, 27830], ![-3632, -574310, 0]], ![![6007, -129569, 18755], ![-2496, -387035, 0]], ![![205, -4235, 613], ![-55, -12650, 0]]]
  g := ![![![1, 0, 0], ![-153, 227, 0], ![-5, 0, 227]], ![![-1, 1, 0], ![51, -76, 11], ![-1, 5, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-51, 89, 1]] ![![227, 0, 0], ![-74, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-16798, 227, 0]], ![![-11577, 20203, 227], ![4313, -6810, 908]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-74, 1, 0]]], ![![![-51, 89, 1]], ![![19, -30, 4]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-106, -75, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-106, -75, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![123, 154, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-106, -75, 1], ![-117, 49, -822], ![-13640, -357, -325]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-123, -154, 229]], ![![-1, -1, 1], ![441, 553, -822], ![115, 217, -325]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [70, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 228], [0, 1]]
 g := ![![[28, 36], [132], [41, 215], [103], [173], [23, 48], [101, 1]], ![[0, 193], [132], [1, 14], [103], [173], [62, 181], [202, 228]]]
 h' := ![![[101, 228], [148, 223], [107, 19], [169, 131], [76, 65], [222, 33], [29, 55], [0, 1]], ![[0, 1], [0, 6], [194, 210], [118, 98], [0, 164], [120, 196], [88, 174], [101, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [153, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [70, 128, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![143988, 11298, 9504]
  a := ![7, 16, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4476, -6342, 9504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-94, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-94, 1, 0]] 
 ![![229, 0, 0], ![135, 1, 0], ![96, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-94, 1, 0], ![4, -96, 11], ![183, 5, -91]]]
  hmulB := by decide  
  f := ![![![27711, -811615, 93005], ![-14885, -1936195, 0]], ![![16365, -478426, 54824], ![-8701, -1141336, 0]], ![![11678, -340241, 38989], ![-6091, -811680, 0]]]
  g := ![![![1, 0, 0], ![-135, 229, 0], ![-96, 0, 229]], ![![-1, 1, 0], ![52, -96, 11], ![36, 5, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-106, -75, 1]] ![![229, 0, 0], ![-94, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-21526, 229, 0]], ![![-24274, -17175, 229], ![9847, 7099, -916]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-94, 1, 0]]], ![![![-106, -75, 1]], ![![43, 31, -4]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![90, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![90, 1, 0]] 
 ![![233, 0, 0], ![90, 1, 0], ![170, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![90, 1, 0], ![4, 88, 11], ![183, 5, 93]]]
  hmulB := by decide  
  f := ![![![138169, 3625480, 453222], ![68968, -9600066, 0]], ![![53306, 1400317, 175054], ![26796, -3707962, 0]], ![![100810, 2645200, 330677], ![50320, -7004340, 0]]]
  g := ![![![1, 0, 0], ![-90, 233, 0], ![-170, 0, 233]], ![![0, 1, 0], ![-42, 88, 11], ![-69, 5, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-72, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-72, 1, 0]] 
 ![![233, 0, 0], ![161, 1, 0], ![215, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-72, 1, 0], ![4, -74, 11], ![183, 5, -69]]]
  hmulB := by decide  
  f := ![![![8233, -170926, 25410], ![-3262, -538230, 0]], ![![5737, -118095, 17556], ![-2096, -371868, 0]], ![![7639, -157722, 23447], ![-2874, -496650, 0]]]
  g := ![![![1, 0, 0], ![-161, 233, 0], ![-215, 0, 233]], ![![-1, 1, 0], ![41, -74, 11], ![61, 5, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-19, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-19, 1, 0]] 
 ![![233, 0, 0], ![214, 1, 0], ![70, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-19, 1, 0], ![4, -21, 11], ![183, 5, -16]]]
  hmulB := by decide  
  f := ![![![-25447, 134787, -70609], ![2796, 1495627, 0]], ![![-23370, 123784, -64845], ![2564, 1373535, 0]], ![![-7646, 40494, -21213], ![828, 449330, 0]]]
  g := ![![![1, 0, 0], ![-214, 233, 0], ![-70, 0, 233]], ![![-1, 1, 0], ![16, -21, 11], ![1, 5, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![90, 1, 0]] ![![233, 0, 0], ![-72, 1, 0]]
  ![![233, 0, 0], ![-38, 65, 1]] where
 M := ![![![54289, 0, 0], ![-16776, 233, 0]], ![![20970, 233, 0], ![-6476, 16, 11]]]
 hmul := by decide  
 g := ![![![![233, 0, 0], ![0, 0, 0]], ![![-34, -64, -1], ![233, 0, 0]]], ![![![90, 1, 0], ![0, 0, 0]], ![![-26, -3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-38, 65, 1]] ![![233, 0, 0], ![-19, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-4427, 233, 0]], ![![-8854, 15145, 233], ![1165, -1398, 699]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-19, 1, 0]]], ![![![-38, 65, 1]], ![![5, -6, 3]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [36, 196, 224, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 104, 219], [50, 134, 20], [0, 1]]
 g := ![![[74, 132, 96], [166, 214, 24], [43, 40, 25], [36, 224, 169], [88, 40], [115, 124, 225], [1]], ![[89, 87, 2, 194], [0, 119, 119, 228], [233, 107, 139, 140], [217, 115, 186, 130], [155, 128], [110, 168, 77, 130], [229, 210, 20, 126]], ![[85, 187, 101, 75], [207, 115, 142, 155], [99, 8, 34, 202], [201, 54, 43, 121], [50, 96], [32, 90, 179, 75], [174, 141, 214, 113]]]
 h' := ![![[204, 104, 219], [238, 2, 151], [125, 94, 195], [138, 153, 234], [132, 190, 226], [162, 104, 163], [203, 43, 15], [0, 1]], ![[50, 134, 20], [67, 99, 118], [11, 42, 111], [76, 216, 94], [26, 78, 194], [161, 195, 164], [27, 175, 194], [204, 104, 219]], ![[0, 1], [78, 138, 209], [154, 103, 172], [223, 109, 150], [1, 210, 58], [75, 179, 151], [192, 21, 30], [50, 134, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 27], []]
 b := ![[], [95, 132, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [36, 196, 224, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21425872, -160608, 508592]
  a := ![-7, 6, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-89648, -672, 2128]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [229, 18, 219, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 17, 201], [191, 223, 40], [0, 1]]
 g := ![![[6, 156, 141], [151, 53], [121, 106], [229, 24], [12, 89, 50], [25, 216, 2], [1]], ![[0, 132, 167, 154], [176, 64], [13, 2], [75, 232], [60, 121, 143, 166], [193, 193, 200, 144], [14, 12, 64, 106]], ![[0, 221, 236, 188], [235, 8], [35, 141], [59, 25], [203, 5, 237, 214], [201, 178, 24, 211], [92, 91, 197, 135]]]
 h' := ![![[72, 17, 201], [121, 221, 158], [128, 25, 52], [107, 28, 180], [144, 236, 54], [59, 117, 110], [12, 223, 22], [0, 1]], ![[191, 223, 40], [214, 234, 125], [111, 77, 233], [227, 50, 219], [131, 221, 192], [14, 122, 88], [107, 140, 83], [72, 17, 201]], ![[0, 1], [0, 27, 199], [132, 139, 197], [26, 163, 83], [139, 25, 236], [143, 2, 43], [219, 119, 136], [191, 223, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230, 232], []]
 b := ![[], [35, 201, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [229, 18, 219, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39843084, 3815271, 1675432]
  a := ![8, -3, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![165324, 15831, 6952]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10338562524664, -1469576770675, 513089420230]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![10338562524664, -1469576770675, 513089420230]] 
 ![![251, 0, 0], ![0, 251, 0], ![187, 92, 1]] where
  M :=![![![10338562524664, -1469576770675, 513089420230], ![88017056819390, 15843163167164, -14626076216735], ![-225319948313975, 1887725710765, 9008368734019]]]
  hmulB := by decide  
  f := ![![![-678609863924226108419141, -56601838739756806987525, -53247738845364045254655]], ![![-9970743563660647509551965, -831644880671532720717366, -782363442673417012626740]], ![![-4219492616341997181986147, -351941599039963625745762, -331086317542841125199961]]]
  g := ![![![-341072346846, -193919535585, 513089420230], ![11247383702585, 5424072410784, -14626076216735], ![-7609103193528, -3294351385733, 9008368734019]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [18, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 250], [0, 1]]
 g := ![![[158, 240], [235, 241], [101], [32, 1], [52, 125], [37, 51], [168, 1]], ![[67, 11], [61, 10], [101], [200, 250], [219, 126], [71, 200], [85, 250]]]
 h' := ![![[168, 250], [37, 156], [144, 201], [177, 193], [68, 250], [87, 171], [239, 94], [0, 1]], ![[0, 1], [141, 95], [27, 50], [222, 58], [151, 1], [201, 80], [218, 157], [168, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [205, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [18, 83, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61898, 27015, 6555]
  a := ![-15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4637, -2295, 6555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-519786561, 36247777, -583505]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-519786561, 36247777, -583505]] 
 ![![251, 0, 0], ![240, 1, 0], ![33, 0, 1]] where
  M :=![![![-519786561, 36247777, -583505], ![38209693, -595199640, 396975032], ![6583745266, 170735795, -414544260]]]
  hmulB := by decide  
  f := ![![![-178958746632395960, -14926682703048545, -14042160468565664]], ![![-181591718280218092, -15146294949405490, -14248758978466097]], ![![-39166554634880605, -3266824028486162, -3073239255042241]]]
  g := ![![![-36653376, 36247777, -583505], ![517075487, -595199640, 396975032], ![-82521454, 170735795, -414544260]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![10338562524664, -1469576770675, 513089420230]] ![![-519786561, 36247777, -583505]]
  ![![251, 0, 0]] where
 M := ![![![-2051947896152054262099, 1337044203821758361778, -802116162514193233720]]]
 hmul := by decide  
 g := ![![![![-8175091219729299849, 5326869337935292278, -3195681922367303720]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![15, 1, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![15, 1, 0]] 
 ![![257, 0, 0], ![15, 1, 0], ![6, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![15, 1, 0], ![4, 13, 11], ![183, 5, 18]]]
  hmulB := by decide  
  f := ![![![83641, 272976, 231000], ![6168, -5397000, 0]], ![![4870, 15923, 13475], ![515, -314825, 0]], ![![1953, 6373, 5393], ![139, -126000, 0]]]
  g := ![![![1, 0, 0], ![-15, 257, 0], ![-6, 0, 257]], ![![0, 1, 0], ![-1, 13, 11], ![0, 5, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N0)

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := prime_ideal_of_norm_prime hp257.out _ NI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![106, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![106, 1, 0]] 
 ![![257, 0, 0], ![106, 1, 0], ![143, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![106, 1, 0], ![4, 104, 11], ![183, 5, 109]]]
  hmulB := by decide  
  f := ![![![137375, 4362409, 461439], ![73759, -10780893, 0]], ![![56590, 1799185, 190311], ![30584, -4446357, 0]], ![![76371, 2427332, 256754], ![41204, -5998707, 0]]]
  g := ![![![1, 0, 0], ![-106, 257, 0], ![-143, 0, 257]], ![![0, 1, 0], ![-49, 104, 11], ![-62, 5, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-122, 1, 0]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-122, 1, 0]] 
 ![![257, 0, 0], ![135, 1, 0], ![97, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-122, 1, 0], ![4, -124, 11], ![183, 5, -119]]]
  hmulB := by decide  
  f := ![![![65225, -2626904, 233046], ![-41120, -5444802, 0]], ![![34265, -1379788, 122408], ![-21587, -2859896, 0]], ![![24693, -991478, 87959], ![-15362, -2055042, 0]]]
  g := ![![![1, 0, 0], ![-135, 257, 0], ![-97, 0, 257]], ![![-1, 1, 0], ![61, -124, 11], ![43, 5, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![15, 1, 0]] ![![257, 0, 0], ![106, 1, 0]]
  ![![257, 0, 0], ![-42, -106, 1]] where
 M := ![![![66049, 0, 0], ![27242, 257, 0]], ![![3855, 257, 0], ![1594, 119, 11]]]
 hmul := by decide  
 g := ![![![![257, 0, 0], ![0, 0, 0]], ![![106, 1, 0], ![0, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![8, 5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-42, -106, 1]] ![![257, 0, 0], ![-122, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-31354, 257, 0]], ![![-10794, -27242, 257], ![4883, 13107, -1285]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-122, 1, 0]]], ![![![-42, -106, 1]], ![![19, 51, -5]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)


lemma PB269I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB269I4 : PrimesBelowBoundCertificateInterval O 193 257 269 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB269I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1, I257N2]
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
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![233, 233, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![63001, 251]
    · exact ![257, 257, 257]
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
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
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
      exact NI257N2
  β := ![I197N1, I211N1, I227N1, I229N1, I233N0, I233N1, I233N2, I251N1, I257N0, I257N1, I257N2]
  Il := ![[I197N1], [], [I211N1], [], [I227N1], [I229N1], [I233N0, I233N1, I233N2], [], [], [I251N1], [I257N0, I257N1, I257N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
