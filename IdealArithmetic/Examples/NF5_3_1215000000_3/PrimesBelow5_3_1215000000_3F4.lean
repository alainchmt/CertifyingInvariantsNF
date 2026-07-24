
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -7, 17, 2, -6]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-77, -7, 17, 2, -6]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![3, 69, 78, 1, 0], ![40, 155, 154, 0, 1]] where
  M :=![![![-77, -7, 17, 2, -6], ![72, -68, -35, 22, 8], ![-96, 23, -80, -54, 88], ![-564, 17, 259, -3, -112], ![306, -109, -155, 52, 43]]]
  hmulB := by decide  
  f := ![![![-197, -47, 23, 46, 54]], ![![-648, -166, 77, 154, 184]], ![![-2208, -541, 262, 522, 616]], ![![-1407, -348, 167, 333, 394]], ![![-2882, -713, 342, 682, 807]]]
  g := ![![![1, 5, 5, 2, -6], ![-2, -18, -19, 22, 8], ![-22, -63, -60, -54, 88], ![25, 112, 113, -3, -112], ![-10, -66, -69, 52, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [113, 49, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 88, 91], [32, 68, 66], [0, 1]]
 g := ![![[3, 9, 130], [43, 132], [105, 36, 35], [53, 34, 10], [68], [7, 1], []], ![[40, 119, 69, 95], [53, 36], [36, 149, 25, 70], [107, 75, 50, 6], [23, 41, 50, 69], [10, 71], [36, 117]], ![[60, 39, 34, 133], [3, 121], [144, 56, 130, 6], [72, 51, 62, 112], [101, 97, 103, 88], [36, 51], [61, 117]]]
 h' := ![![[132, 88, 91], [101, 118, 82], [67, 108, 17], [134, 79, 105], [9, 1, 139], [151, 15], [0, 0, 1], [0, 1]], ![[32, 68, 66], [94, 77, 143], [66, 82, 151], [99, 124, 42], [100, 7, 123], [90, 64, 109], [11, 83, 68], [132, 88, 91]], ![[0, 1], [56, 119, 89], [148, 124, 146], [130, 111, 10], [22, 149, 52], [3, 78, 48], [97, 74, 88], [32, 68, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 35], []]
 b := ![[], [124, 152, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [113, 49, 150, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5448761, 2871708, -121740, -2543270, -2315750]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![673303, 3422284, 3534260, -2543270, -2315750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, -47, 23, 46, 54]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-197, -47, 23, 46, 54]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![16, 1, 1, 0, 0], ![149, 8, 0, 1, 0], ![133, 114, 0, 0, 1]] where
  M :=![![![-197, -47, 23, 46, 54], ![-648, -166, 77, 154, 184], ![-2208, -541, 262, 522, 616], ![-3372, -843, 401, 801, 952], ![-4122, -1017, 491, 976, 1155]]]
  hmulB := by decide  
  f := ![![![-77, -7, 17, 2, -6]], ![![72, -68, -35, 22, 8]], ![![-8, -1, 1, 0, 0]], ![![-73, -10, 16, 3, -6]], ![![-11, -56, -12, 18, 1]]]
  g := ![![![-93, -42, 23, 46, 54], ![-314, -143, 77, 154, 184], ![-1058, -479, 262, 522, 616], ![-1629, -740, 401, 801, 952], ![-1981, -898, 491, 976, 1155]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [60, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 156], [0, 1]]
 g := ![![[79, 25], [67], [108, 138], [123, 19], [142, 49], [115], [1]], ![[114, 132], [67], [50, 19], [24, 138], [85, 108], [115], [1]]]
 h' := ![![[127, 156], [27, 152], [114, 99], [156, 74], [115, 31], [154, 150], [97, 127], [0, 1]], ![[0, 1], [20, 5], [127, 58], [134, 83], [127, 126], [50, 7], [55, 30], [127, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [107, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [60, 30, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2236533, -314512, 370897, 368679, 504550]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-829358, -389513, 370897, 368679, 504550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-77, -7, 17, 2, -6]] ![![-197, -47, 23, 46, 54]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-976, -931, -18, 239, -59]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-976, -931, -18, 239, -59]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![116, 118, 97, 7, 1]] where
  M :=![![![-976, -931, -18, 239, -59], ![708, -1292, -1645, -154, 956], ![-11472, 173, 2840, -1378, -616], ![3342, -3289, 1055, 2301, -3234], ![4143, -521, -4198, -1817, 2232]]]
  hmulB := by decide  
  f := ![![![8253146, -5021505, -722284, -606153, 1291339]], ![![-15496068, 9428354, 1356157, 1138110, -2424612]], ![![29095344, -17702633, -2546314, -2136910, 4552440]], ![![-19566606, 11905013, 1712395, 1437071, -3061514]], ![![11251345, -6845715, -984675, -826356, 1760456]]]
  g := ![![![36, 37, 35, 4, -59], ![-676, -700, -579, -42, 956], ![368, 447, 384, 18, -616], ![2322, 2321, 1931, 153, -3234], ![-1563, -1619, -1354, -107, 2232]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [41, 29, 83, 42, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 54, 152, 69], [53, 139, 93, 46], [120, 132, 81, 48], [0, 1]]
 g := ![![[45, 142, 24, 6], [151, 141, 5, 111], [87, 8, 133], [59, 87, 132], [136, 13, 156], [121, 1], []], ![[69, 131, 120, 27, 53, 57], [35, 119, 119, 0, 24, 155], [45, 102, 96], [122, 117, 40], [124, 69, 60], [9, 27, 160, 21, 54, 61], [39, 151, 34]], ![[97, 92, 131, 160, 90, 43], [148, 59, 6, 23, 88, 60], [4, 63, 93], [118, 141, 133], [120, 89, 15], [153, 143, 158, 4, 135, 65], [157, 43, 160]], ![[37, 117, 33, 74, 50, 89], [94, 13, 150, 20, 94, 76], [82, 95, 132], [161, 77, 69], [101, 50, 156], [109, 53, 49, 46, 12, 149], [40, 6, 22]]]
 h' := ![![[111, 54, 152, 69], [3, 4, 136, 13], [59, 7, 75, 130], [23, 133, 89, 123], [117, 28, 86, 28], [92, 36, 34, 51], [0, 0, 1], [0, 1]], ![[53, 139, 93, 46], [1, 96, 107, 34], [93, 138, 130, 66], [109, 43, 162, 52], [59, 71, 7, 140], [47, 135, 114, 95], [127, 102, 103, 114], [111, 54, 152, 69]], ![[120, 132, 81, 48], [37, 29, 92, 84], [134, 143, 13, 59], [61, 42, 68, 16], [3, 101, 94, 40], [14, 37, 11, 129], [121, 105, 28, 116], [53, 139, 93, 46]], ![[0, 1], [60, 34, 154, 32], [151, 38, 108, 71], [116, 108, 7, 135], [69, 126, 139, 118], [61, 118, 4, 51], [46, 119, 31, 96], [120, 132, 81, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [62, 115, 58], []]
 b := ![[], [], [72, 71, 99, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [41, 29, 83, 42, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1775738348, -470597939, 173970984, 441042761, 550444755]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-402621656, -401368583, -326497977, -20932948, 550444755]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8253146, -5021505, -722284, -606153, 1291339]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![8253146, -5021505, -722284, -606153, 1291339]] 
 ![![163, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![122, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![8253146, -5021505, -722284, -606153, 1291339], ![-15496068, 9428354, 1356157, 1138110, -2424612], ![29095344, -17702633, -2546314, -2136910, 4552440], ![-19566606, 11905013, 1712395, 1437071, -3061514], ![19858197, -12082427, -1737914, -1458487, 3107138]]]
  hmulB := by decide  
  f := ![![![-976, -931, -18, 239, -59]], ![![-804, -779, -25, 197, -43]], ![![-256, -176, 14, 37, -15]], ![![-710, -717, -7, 193, -64]], ![![-747, -740, -40, 178, -33]]]
  g := ![![![3778620, -5021505, -722284, -606153, 1291339], ![-7094719, 9428354, 1356157, 1138110, -2424612], ![13321011, -17702633, -2546314, -2136910, 4552440], ![-8958374, 11905013, 1712395, 1437071, -3061514], ![9091876, -12082427, -1737914, -1458487, 3107138]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-976, -931, -18, 239, -59]] ![![8253146, -5021505, -722284, -606153, 1291339]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-901, -504, -64, 64, 138]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-901, -504, -64, 64, 138]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![97, 52, 1, 0, 0], ![150, 33, 0, 1, 0], ![125, 10, 0, 0, 1]] where
  M :=![![![-901, -504, -64, 64, 138], ![-1656, -891, -80, 148, 256], ![-3072, -1628, -163, 352, 592], ![-2724, -1052, 58, 355, 576], ![-3678, -1648, 34, 530, 715]]]
  hmulB := by decide  
  f := ![![![12199753, -7422760, -1067676, -896012, 1908850]], ![![-22906200, 13936939, 2004664, 1682348, -3584048]], ![![211151, -128472, -18479, -15508, 33038]], ![![6258294, -3807767, -547702, -459641, 979212]], ![![7935697, -4828358, -694502, -582838, 1241669]]]
  g := ![![![-129, -4, -64, 64, 138], ![-288, -25, -80, 148, 256], ![-683, -64, -163, 352, 592], ![-800, -129, 58, 355, 576], ![-1053, -168, 34, 530, 715]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [139, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 166], [0, 1]]
 g := ![![[53, 137], [18, 137], [47, 150], [38], [93], [93, 27], [1]], ![[122, 30], [87, 30], [36, 17], [38], [93], [81, 140], [1]]]
 h' := ![![[148, 166], [3, 53], [147, 114], [100, 22], [47, 47], [99, 107], [28, 148], [0, 1]], ![[0, 1], [165, 114], [152, 53], [16, 145], [156, 120], [70, 60], [55, 19], [148, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [114, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [139, 19, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448860, -55476, 92083, 68259, 78723]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-176408, -47207, 92083, 68259, 78723]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95525, 58120, 8360, 7016, -14946]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-95525, 58120, 8360, 7016, -14946]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![9, 7, 1, 0, 0], ![52, 64, 0, 1, 0], ![111, 113, 0, 0, 1]] where
  M :=![![![-95525, 58120, 8360, 7016, -14946], ![179352, -109127, -15696, -13172, 28064], ![-336768, 204892, 29473, 24736, -52688], ![226452, -137796, -19818, -16629, 35440], ![-229866, 139840, 20118, 16886, -35957]]]
  hmulB := by decide  
  f := ![![![1001, 664, 140, -68, -170]], ![![2040, 1039, 120, -60, -272]], ![![159, 91, 13, -8, -22]], ![![1096, 612, 94, -45, -160]], ![![2067, 1153, 174, -86, -299]]]
  g := ![![![6727, 7422, 8360, 7016, -14946], ![-12632, -13937, -15696, -13172, 28064], ![23713, 26163, 29473, 24736, -52688], ![-15954, -17602, -19818, -16629, 35440], ![16181, 17853, 20118, 16886, -35957]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [8, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 166], [0, 1]]
 g := ![![[117, 21], [79, 57], [160, 33], [57], [98], [35, 14], [1]], ![[0, 146], [0, 110], [0, 134], [57], [98], [124, 153], [1]]]
 h' := ![![[66, 166], [36, 45], [56, 70], [63, 37], [128, 97], [54, 91], [159, 66], [0, 1]], ![[0, 1], [0, 122], [0, 97], [0, 130], [17, 70], [48, 76], [6, 101], [66, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [52, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [8, 101, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42032, -4363, 16929, 7062, -4688]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-247, -270, 16929, 7062, -4688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -32, -4, -4, 8]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![53, -32, -4, -4, 8]] 
 ![![167, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![53, -32, -4, -4, 8], ![-96, 61, 8, 8, -16], ![192, -112, -19, -16, 32], ![-144, 80, 20, 9, -24], ![144, -80, -16, -8, 21]]]
  hmulB := by decide  
  f := ![![![811, 224, -84, -180, -216]], ![![540, 149, -56, -120, -144]], ![![178, 48, -19, -40, -48]], ![![297, 80, -32, -67, -80]], ![![877, 240, -92, -196, -235]]]
  g := ![![![15, -32, -4, -4, 8], ![-28, 61, 8, 8, -16], ![50, -112, -19, -16, 32], ![-35, 80, 20, 9, -24], ![37, -80, -16, -8, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-901, -504, -64, 64, 138]] ![![-95525, 58120, 8360, 7016, -14946]]
  ![![-811, -224, 84, 180, 216]] where
 M := ![![![-811, -224, 84, 180, 216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-811, -224, 84, 180, 216]] ![![53, -32, -4, -4, 8]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [29, 104, 45, 118, 111, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 105, 5, 24, 117], [71, 7, 0, 102, 104], [35, 120, 161, 111, 170], [166, 113, 7, 109, 128], [0, 1]]
 g := ![![[49, 82, 69, 124, 47], [1, 148, 66, 23], [69, 120, 74, 55, 25], [136, 98, 56, 140, 144], [13, 142, 7, 38], [1], []], ![[157, 59, 24, 105, 153, 15, 80, 13], [43, 52, 111, 160], [33, 55, 157, 57, 168, 140, 136, 56], [136, 67, 172, 143, 137, 37, 98, 55], [120, 163, 6, 124], [18, 65, 144, 86, 117, 139, 161, 56], [55, 102, 60, 22]], ![[110, 69, 139, 131, 160, 53, 5, 71], [150, 10, 64, 160], [160, 166, 52, 129, 24, 90, 149, 115], [25, 169, 101, 22, 133, 119, 98, 153], [136, 0, 27, 67], [58, 164, 14, 108, 44, 157, 94, 98], [66, 163, 154, 90]], ![[5, 63, 114, 96, 122, 12, 38, 17], [49, 95, 53, 90], [135, 166, 121, 6, 81, 81, 122, 46], [123, 170, 15, 79, 164, 0, 105, 134], [47, 131, 0, 36], [156, 141, 19, 110, 114, 44, 66, 71], [149, 137, 65, 9]], ![[8, 112, 47, 98, 49, 78, 116, 165], [14, 97, 68, 84], [94, 22, 108, 78, 25, 88, 103, 12], [16, 139, 99, 96, 13, 160, 53, 27], [14, 111, 82, 144], [94, 152, 64, 67, 140, 91, 59, 123], [139, 155, 3, 122]]]
 h' := ![![[136, 105, 5, 24, 117], [60, 73, 149, 99, 96], [75, 84, 95, 75, 14], [35, 52, 170, 110, 5], [118, 43, 119, 49, 161], [144, 69, 128, 55, 62], [0, 0, 1], [0, 1]], ![[71, 7, 0, 102, 104], [42, 106, 94, 33, 115], [50, 92, 15, 162, 92], [36, 0, 169, 81, 80], [138, 156, 48, 50, 129], [37, 78, 134, 54, 41], [120, 160, 157, 0, 93], [136, 105, 5, 24, 117]], ![[35, 120, 161, 111, 170], [171, 9, 88, 133, 170], [159, 118, 162, 31, 81], [54, 169, 37, 146, 70], [25, 27, 145, 22, 108], [110, 169, 76, 40, 76], [13, 129, 54, 111, 161], [71, 7, 0, 102, 104]], ![[166, 113, 7, 109, 128], [93, 57, 65, 13, 158], [87, 123, 115, 109, 104], [12, 29, 132, 29, 163], [111, 124, 14, 24, 79], [69, 30, 149, 160, 6], [18, 3, 64, 72, 42], [35, 120, 161, 111, 170]], ![[0, 1], [53, 101, 123, 68, 153], [74, 102, 132, 142, 55], [130, 96, 11, 153, 28], [35, 169, 20, 28, 42], [152, 0, 32, 37, 161], [170, 54, 70, 163, 50], [166, 113, 7, 109, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 102, 8, 1], [], [], []]
 b := ![[], [150, 128, 11, 131, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [29, 104, 45, 118, 111, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3408129357581, -585685449152, -1399312342796, 273428724780, 457051411256]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19700169697, -3385465024, -8088510652, 1580512860, 2641915672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 154963892093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45443, -28388, -3944, -3190, 7496]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![45443, -28388, -3944, -3190, 7496]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![58, 135, 163, 145, 1]] where
  M :=![![![45443, -28388, -3944, -3190, 7496], ![-89952, 52185, 7976, 7104, -12760], ![153120, -101840, -13063, -9568, 28416], ![-125520, 62928, 11492, 11801, -12756], ![92340, -72520, -7462, -3640, 22819]]]
  hmulB := by decide  
  f := ![![![241, -28, -112, 6, 48]], ![![-576, 171, 152, -128, 24]], ![![-288, -272, 523, 352, -512]], ![![3360, -400, -1588, 75, 692]], ![![2090, -449, -727, 285, 127]]]
  g := ![![![-2175, -5812, -6848, -6090, 7496], ![3632, 9915, 11664, 10376, -12760], ![-8352, -22000, -25949, -23072, 28416], ![3432, 9972, 11680, 10399, -12756], ![-6878, -17615, -20821, -18505, 22819]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [117, 110, 95, 156, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 15, 62, 88], [76, 5, 153, 63], [124, 158, 143, 28], [0, 1]]
 g := ![![[52, 132, 120, 76], [91, 118, 5, 67], [19, 43, 147], [163, 174, 169], [128, 63, 61, 48], [23, 1], []], ![[44, 3, 37, 5, 145, 80], [3, 26, 147, 125, 90, 67], [64, 82, 87], [131, 173, 4], [149, 52, 69, 134, 139, 158], [34, 50, 136, 145, 106, 51], [50, 0, 47]], ![[66, 113, 18, 126, 155, 23], [65, 8, 161, 70, 87, 91], [99, 46, 12], [150, 43, 1], [2, 94, 65, 167, 152, 134], [0, 109, 65, 121, 162, 26], [93, 122, 31]], ![[66, 71, 0, 12, 170, 69], [118, 74, 28, 96, 152, 178], [28, 122, 1], [84, 23, 100], [157, 107, 121, 82, 124, 165], [56, 104, 112, 65, 120, 37], [90, 85, 68]]]
 h' := ![![[2, 15, 62, 88], [93, 115, 87, 75], [126, 21, 122, 70], [102, 121, 118, 133], [60, 65, 167, 13], [173, 38, 32, 76], [0, 0, 1], [0, 1]], ![[76, 5, 153, 63], [105, 139, 68, 31], [7, 48, 32, 146], [131, 91, 65, 83], [171, 178, 114, 177], [63, 147, 60, 67], [61, 109, 69, 161], [2, 15, 62, 88]], ![[124, 158, 143, 28], [159, 127, 177, 139], [11, 157, 121, 9], [73, 50, 36, 141], [170, 64, 169, 178], [36, 19, 79, 75], [86, 63, 84, 35], [76, 5, 153, 63]], ![[0, 1], [135, 156, 26, 113], [62, 132, 83, 133], [37, 96, 139, 1], [60, 51, 87, 169], [84, 154, 8, 140], [13, 7, 25, 162], [124, 158, 143, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 122, 152], []]
 b := ![[], [], [120, 55, 141, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [117, 110, 95, 156, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4321596067, 180268180, 857927818, -33074630, 644564514]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-232996301, -485116990, -582156916, -522318040, 644564514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, -28, -112, 6, 48]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![241, -28, -112, 6, 48]] 
 ![![179, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![241, -28, -112, 6, 48], ![-576, 171, 152, -128, 24], ![-288, -272, 523, 352, -512], ![3360, -400, -1588, 75, 692], ![-2364, 504, 854, -304, -175]]]
  hmulB := by decide  
  f := ![![![45443, -28388, -3944, -3190, 7496]], ![![34024, -21277, -2952, -2384, 5624]], ![![31320, -19600, -2717, -2192, 5184]], ![![822, -600, -68, -41, 180]], ![![18033, -11348, -1562, -1250, 3017]]]
  g := ![![![79, -28, -112, 6, 48], ![-240, 171, 152, -128, 24], ![40, -272, 523, 352, -512], ![1118, -400, -1588, 75, 692], ![-891, 504, 854, -304, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![45443, -28388, -3944, -3190, 7496]] ![![241, -28, -112, 6, 48]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4528, -2901, -430, 277, 699]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-4528, -2901, -430, 277, 699]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![42, 51, 13, 1, 0], ![89, 44, 154, 0, 1]] where
  M :=![![![-4528, -2901, -430, 277, 699], ![-8388, -4536, -659, 538, 1108], ![-13296, -8477, -1180, 898, 2152], ![-8718, -4343, -503, 703, 1242], ![-12471, -7543, -950, 953, 2056]]]
  hmulB := by decide  
  f := ![![![-358, 151, 36, -133, 83]], ![![-996, -106, 749, 238, -532]], ![![6384, -1017, -2710, 434, 952]], ![![66, -56, 28, 57, -56]], ![![5011, -822, -2098, 368, 713]]]
  g := ![![![-433, -264, -617, 277, 699], ![-716, -446, -985, 538, 1108], ![-1340, -823, -1902, 898, 2152], ![-822, -524, -1110, 703, 1242], ![-1301, -810, -1823, 953, 2056]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [17, 97, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 105, 24], [24, 75, 157], [0, 1]]
 g := ![![[100, 144, 4], [132, 167], [132, 121, 166], [175, 16], [132, 171, 42], [121, 134, 1], []], ![[93, 57, 22, 61], [140, 178], [170, 112, 34, 23], [171, 16], [0, 138, 134, 85], [89, 72, 52, 155], [50, 33]], ![[52, 2, 161, 8], [48, 101], [106, 33, 51, 123], [149, 64], [61, 112, 41, 95], [144, 136, 43, 22], [98, 33]]]
 h' := ![![[110, 105, 24], [44, 98, 179], [109, 83, 23], [37, 95, 96], [109, 48, 4], [115, 103, 122], [0, 0, 1], [0, 1]], ![[24, 75, 157], [89, 71, 30], [109, 167, 97], [143, 22, 68], [71, 138, 4], [19, 131, 38], [28, 132, 75], [110, 105, 24]], ![[0, 1], [51, 12, 153], [18, 112, 61], [123, 64, 17], [159, 176, 173], [108, 128, 21], [177, 49, 105], [24, 75, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178, 146], []]
 b := ![[], [63, 90, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [17, 97, 47, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73112, -8580, -36624, -6848, 23111]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9371, -3736, -19374, -6848, 23111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5819, -3464, -520, 352, 824]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-5819, -3464, -520, 352, 824]] 
 ![![181, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![-5819, -3464, -520, 352, 824], ![-9888, -5867, -872, 608, 1408], ![-16896, -9960, -1451, 1072, 2432], ![-9648, -5560, -752, 677, 1440], ![-15240, -8856, -1232, 1032, 2245]]]
  hmulB := by decide  
  f := ![![![-2063, 1000, 296, -160, -88]], ![![-849, 405, 128, -64, -40]], ![![-1861, 928, 245, -144, -72]], ![![-457, 208, 72, -51, -8]], ![![-1942, 936, 288, -136, -99]]]
  g := ![![![1041, -3464, -520, 352, 824], ![1741, -5867, -872, 608, 1408], ![2881, -9960, -1451, 1072, 2432], ![1461, -5560, -752, 677, 1440], ![2414, -8856, -1232, 1032, 2245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27367, 16651, 2395, 2010, -4282]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-27367, 16651, 2395, 2010, -4282]] 
 ![![181, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![-27367, 16651, 2395, 2010, -4282], ![51384, -31264, -4497, -3774, 8040], ![-96480, 58701, 8444, 7086, -15096], ![64884, -39477, -5679, -4765, 10152], ![-65850, 40065, 5763, 4836, -10303]]]
  hmulB := by decide  
  f := ![![![-31, -229, -115, -90, -86]], ![![-8, -102, -53, -42, -40]], ![![4, -143, -78, -66, -64]], ![![46, -23, -23, -25, -28]], ![![43, -116, -74, -66, -65]]]
  g := ![![![-6945, 16651, 2395, 2010, -4282], ![13040, -31264, -4497, -3774, 8040], ![-24484, 58701, 8444, 7086, -15096], ![16466, -39477, -5679, -4765, 10152], ![-16711, 40065, 5763, 4836, -10303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-4528, -2901, -430, 277, 699]] ![![-5819, -3464, -520, 352, 824]]
  ![![48973544, 29257495, 4438690, -2909727, -6893305]] where
 M := ![![![48973544, 29257495, 4438690, -2909727, -6893305]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![48973544, 29257495, 4438690, -2909727, -6893305]] ![![-27367, 16651, 2395, 2010, -4282]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-7259186, -5272892, -795857, 420825, 1253063]]]
 hmul := by decide  
 g := ![![![![-40106, -29132, -4397, 2325, 6923]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5713, -181, -3163, 36, 1420]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![5713, -181, -3163, 36, 1420]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![9, 152, 169, 127, 1]] where
  M :=![![![5713, -181, -3163, 36, 1420], ![-17040, 3934, 5427, -3486, 144], ![-1728, -7983, 11482, 11142, -13944], ![92184, -9633, -45735, -719, 22212], ![-71760, 14337, 27261, -7062, -7655]]]
  hmulB := by decide  
  f := ![![![4607, 2465, 245, -420, -764]], ![![9168, 4508, 249, -1038, -1680]], ![![20160, 8775, -136, -2862, -4152]], ![![20328, 7113, -1179, -3769, -4884]], ![![39009, 16250, -701, -5909, -8327]]]
  g := ![![![-37, -1131, -1273, -944, 1420], ![-96, -94, -99, -114, 144], ![648, 11055, 12398, 9330, -13944], ![-564, -17727, -19893, -14773, 22212], ![-15, 6167, 6916, 5053, -7655]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [161, 139, 155, 71, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 19, 91, 18], [57, 128, 36, 137], [186, 43, 64, 36], [0, 1]]
 g := ![![[15, 148, 0, 180], [82, 139, 134, 133], [59, 98, 112, 15], [172, 82, 21, 68], [97, 61, 102, 97], [120, 1], []], ![[49, 118, 173, 95, 151, 102], [75, 32, 174, 46, 142, 77], [30, 113, 26, 175, 181, 136], [78, 36, 113, 108, 17, 4], [66, 43, 18, 170, 108, 78], [21, 97, 24, 171, 25, 65], [86, 136, 133]], ![[122, 130, 129, 72, 12, 157], [100, 68, 171, 60, 65, 58], [169, 85, 52, 74, 31, 7], [5, 183, 38, 34, 45, 111], [183, 46, 142, 190, 47, 74], [132, 41, 95, 11, 99, 188], [62, 131, 51]], ![[102, 152, 178, 4, 172, 9], [20, 26, 44, 59, 90, 144], [18, 87, 102, 62, 81, 172], [169, 77, 115, 162, 110, 13], [159, 185, 5, 125, 18, 79], [49, 12, 22, 58, 97, 5], [173, 70, 150]]]
 h' := ![![[68, 19, 91, 18], [168, 148, 117, 84], [51, 96, 47, 173], [3, 59, 73, 46], [45, 75, 178, 100], [162, 158, 170, 111], [0, 0, 1], [0, 1]], ![[57, 128, 36, 137], [10, 115, 90, 18], [48, 129, 113, 180], [27, 121, 59, 97], [17, 105, 1, 19], [87, 174, 34, 91], [137, 58, 155, 152], [68, 19, 91, 18]], ![[186, 43, 64, 36], [87, 175, 22, 185], [55, 117, 8, 31], [6, 57, 26, 92], [17, 24, 165, 54], [60, 114, 128, 15], [143, 163, 120, 105], [57, 128, 36, 137]], ![[0, 1], [109, 135, 153, 95], [99, 40, 23, 189], [94, 145, 33, 147], [134, 178, 38, 18], [121, 127, 50, 165], [58, 161, 106, 125], [186, 43, 64, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [139, 14, 184], []]
 b := ![[], [], [167, 0, 169, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [161, 139, 155, 71, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26931213493, -5080253912, 2726862196, 4835795744, 8027345904]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-519253019, -6414852520, -7088453380, -5312236304, 8027345904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4607, -2465, -245, 420, 764]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-4607, -2465, -245, 420, 764]] 
 ![![191, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-4607, -2465, -245, 420, 764], ![-9168, -4508, -249, 1038, 1680], ![-20160, -8775, 136, 2862, 4152], ![-20328, -7113, 1179, 3769, 4884], ![-27024, -10023, 1227, 4722, 6265]]]
  hmulB := by decide  
  f := ![![![-5713, 181, 3163, -36, -1420]], ![![-1855, 41, 1048, 6, -484]], ![![-5016, 201, 2722, -90, -1176]], ![![-4730, 185, 2591, -23, -1172]], ![![-731, -40, 470, 30, -235]]]
  g := ![![![570, -2465, -245, 420, 764], ![608, -4508, -249, 1038, 1680], ![-171, -8775, 136, 2862, 4152], ![-2471, -7113, 1179, 3769, 4884], ![-2534, -10023, 1227, 4722, 6265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![5713, -181, -3163, 36, 1420]] ![![-4607, -2465, -245, 420, 764]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1084, 530, 99, 105, -103]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-1084, 530, 99, 105, -103]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![38, 139, 98, 1, 0], ![68, 26, 9, 0, 1]] where
  M :=![![![-1084, 530, 99, 105, -103], ![1236, -1193, -92, -8, 420], ![-5040, 1572, 503, 656, -32], ![-426, -2016, 112, 475, 1102], ![-5517, 566, 589, 933, 564]]]
  hmulB := by decide  
  f := ![![![5810, 3470, 527, -345, -819]], ![![9828, 5863, 884, -584, -1380]], ![![16560, 9916, 1511, -992, -2336]], ![![16678, 9969, 1512, -995, -2348]], ![![4219, 2520, 382, -251, -594]]]
  g := ![![![10, -59, -48, 105, -103], ![-140, -57, -16, -8, 420], ![-144, -460, -329, 656, -32], ![-484, -501, -292, 475, 1102], ![-411, -745, -497, 933, 564]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [67, 133, 177, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 54, 177], [159, 138, 16], [0, 1]]
 g := ![![[126, 130, 3], [44, 162], [27, 97], [183, 95], [10, 97], [33, 63], [1]], ![[88, 145, 8, 190], [175, 36], [32, 75], [78, 31], [32, 21], [28, 187], [124, 83, 61, 150]], ![[37, 50, 146, 27], [24, 179], [153, 6], [125, 67], [181, 31], [161, 42], [62, 131, 136, 43]]]
 h' := ![![[50, 54, 177], [168, 127, 14], [75, 8, 82], [95, 108, 26], [2, 176, 45], [155, 141, 167], [126, 60, 16], [0, 1]], ![[159, 138, 16], [76, 73, 93], [75, 146, 187], [176, 69, 123], [34, 116, 113], [172, 60, 139], [120, 35, 90], [50, 54, 177]], ![[0, 1], [29, 186, 86], [155, 39, 117], [131, 16, 44], [20, 94, 35], [145, 185, 80], [160, 98, 87], [159, 138, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 138], []]
 b := ![[], [106, 80, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [67, 133, 177, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3457380, -1574390, 442240, 1401968, 1083079]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-675552, -1163772, -760095, 1401968, 1083079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5810, 3470, 527, -345, -819]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![5810, 3470, 527, -345, -819]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![113, 190, 1, 0, 0], ![73, 149, 0, 1, 0], ![45, 80, 0, 0, 1]] where
  M :=![![![5810, 3470, 527, -345, -819], ![9828, 5863, 884, -584, -1380], ![16560, 9916, 1511, -992, -2336], ![9102, 5432, 836, -533, -1294], ![14619, 8718, 1307, -871, -2046]]]
  hmulB := by decide  
  f := ![![![-1084, 530, 99, 105, -103]], ![![1236, -1193, -92, -8, 420]], ![![556, -856, -30, 57, 353]], ![![542, -731, -33, 36, 291]], ![![231, -368, -12, 26, 153]]]
  g := ![![![43, 105, 527, -345, -819], ![76, 183, 884, -584, -1380], ![121, 298, 1511, -992, -2336], ![61, 153, 836, -533, -1294], ![117, 279, 1307, -871, -2046]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [165, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 192], [0, 1]]
 g := ![![[69, 62], [95], [172], [107], [67], [59], [2, 1]], ![[0, 131], [95], [172], [107], [67], [59], [4, 192]]]
 h' := ![![[2, 192], [21, 86], [177, 148], [46, 65], [157, 53], [156, 35], [56, 32], [0, 1]], ![[0, 1], [0, 107], [87, 45], [176, 128], [70, 140], [33, 158], [120, 161], [2, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [173]]
 b := ![[], [10, 183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [165, 191, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291, 192, 872, 426, -1236]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-385, -674, 872, 426, -1236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-1084, 530, 99, 105, -103]] ![![5810, 3470, 527, -345, -819]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [131, 89, 150, 133, 137, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 63, 51, 43, 151], [109, 165, 85, 151, 116], [60, 107, 64, 17, 19], [50, 58, 194, 183, 108], [0, 1]]
 g := ![![[114, 17, 36, 167, 112], [35, 111, 107, 164], [149, 69, 120, 114, 49], [131, 24, 154, 142], [186, 125, 63, 134], [60, 1], []], ![[94, 21, 44, 117, 177, 10, 114, 166], [148, 17, 176, 156], [39, 190, 69, 178, 86, 56, 52, 38], [6, 79, 76, 190], [88, 74, 58, 105], [22, 116, 162, 178], [56, 44, 87, 126, 116, 121, 24, 179]], ![[89, 22, 58, 32, 7, 24, 59, 142], [55, 143, 99, 144], [85, 45, 42, 38, 64, 83, 27, 55], [112, 118, 28, 88], [124, 155, 34, 196], [105, 140, 69, 154], [52, 137, 55, 82, 7, 134, 151, 65]], ![[1, 45, 81, 92, 190, 78, 176, 156], [100, 15, 145, 34], [137, 37, 79, 48, 63, 19, 145, 148], [116, 75, 100, 182], [100, 134, 61, 190], [96, 192, 184, 169], [113, 46, 47, 67, 191, 60, 97, 161]], ![[150, 135, 77, 129, 177, 188, 124, 21], [16, 11, 35, 15], [10, 176, 67, 61, 36, 85, 53, 75], [33, 47, 139, 144], [131, 132, 52, 196], [144, 160, 193, 59], [7, 123, 154, 17, 178, 63, 175, 94]]]
 h' := ![![[38, 63, 51, 43, 151], [5, 171, 79, 14, 167], [181, 77, 60, 168, 178], [71, 155, 161, 164, 7], [68, 194, 159, 115, 39], [20, 45, 170, 144, 118], [0, 0, 0, 1], [0, 1]], ![[109, 165, 85, 151, 116], [164, 145, 155, 89, 39], [190, 128, 70, 76, 64], [67, 177, 3, 167, 150], [159, 10, 134, 23, 105], [8, 111, 51, 153, 156], [59, 158, 176, 7, 93], [38, 63, 51, 43, 151]], ![[60, 107, 64, 17, 19], [93, 182, 161, 196, 192], [194, 103, 155, 85, 185], [184, 7, 181, 182, 127], [188, 174, 28, 196, 65], [9, 142, 42, 130, 14], [34, 134, 125, 57, 101], [109, 165, 85, 151, 116]], ![[50, 58, 194, 183, 108], [115, 129, 118, 130, 145], [4, 143, 28, 100, 25], [54, 90, 94, 173, 142], [9, 19, 168, 12, 173], [86, 194, 39, 160, 92], [60, 69, 112, 95, 184], [60, 107, 64, 17, 19]], ![[0, 1], [183, 161, 78, 162, 48], [167, 140, 81, 162, 139], [159, 162, 152, 102, 165], [99, 194, 102, 48, 12], [186, 99, 92, 4, 14], [170, 33, 178, 37, 16], [50, 58, 194, 183, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144, 38, 99, 100], [], [], []]
 b := ![[], [162, 128, 94, 8, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [131, 89, 150, 133, 137, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14832885694745195, 3454735206342947, -1945364730289727, -3355096663470282, -3924325008650030]
  a := ![7, 23, 45, -23, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![75293836013935, 17536726935751, -9874947869491, -17030947530306, -19920431515990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 296709280757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB1705I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1705I4 : PrimesBelowBoundCertificateInterval O 151 197 1705 where
  m := 9
  g := ![2, 2, 3, 1, 2, 3, 2, 2, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1705I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
    · exact ![I197N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 24649]
    · exact ![705911761, 163]
    · exact ![27889, 27889, 167]
    · exact ![154963892093]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![1330863361, 191]
    · exact ![7189057, 37249]
    · exact ![296709280757]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![I163N1, I167N2, I179N1, I181N1, I181N2, I191N1]
  Il := ![[], [I163N1], [I167N2], [], [I179N1], [I181N1, I181N2], [I191N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
