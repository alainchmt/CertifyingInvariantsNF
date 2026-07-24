
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -380, 475, 183, 1135]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-24, -380, 475, 183, 1135]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![160, 149, 47, 24, 1]] where
  M :=![![![-24, -380, 475, 183, 1135], ![148, 1514, -1737, -662, -4252], ![-1120, -6019, 7446, 2942, 17720], ![62, 9897, -11205, -4127, -27838], ![385, 446, -713, -331, -1504]]]
  hmulB := by decide  
  f := ![![![14, -8, 3, 3, 13]], ![![-20, 12, 9, 2, 20]], ![![32, 31, -56, -30, -168]], ![![34, -69, 59, 39, 194]], ![![5, 1, 2, 1, 6]]]
  g := ![![![-584, -545, -170, -87, 1135], ![2188, 2042, 637, 326, -4252], ![-9120, -8509, -2654, -1358, 17720], ![14322, 13369, 4171, 2135, -27838], ![775, 722, 225, 115, -1504]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [271, 156, 48, 281, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 77, 67, 43], [301, 136, 206, 158], [13, 97, 38, 110], [0, 1]]
 g := ![![[24, 303, 50, 135], [4, 37, 268, 75], [49, 28, 281, 268], [265, 10, 267], [138, 163, 29, 100], [162, 29, 173, 278], [1], []], ![[219, 84, 76, 53, 230, 246], [109, 215, 42, 281, 204, 171], [0, 16, 77, 132, 82, 133], [18, 257, 80], [73, 72, 229, 288, 224, 285], [133, 155, 14, 30, 157, 17], [193, 101, 112], [303, 276, 294]], ![[134, 294, 5, 227, 88, 208], [276, 94, 96, 286, 302, 210], [279, 142, 66, 124, 216, 14], [122, 308, 126], [23, 120, 271, 166, 299, 134], [262, 79, 274, 115, 272, 16], [263, 206, 187], [36, 129, 84]], ![[261, 161, 239, 11, 188, 287], [21, 56, 66, 212, 52, 246], [126, 114, 200, 160, 68, 99], [282, 274, 36], [301, 16, 209, 162, 84, 118], [63, 59, 10, 193, 107, 171], [32, 118, 42], [76, 26, 282]]]
 h' := ![![[27, 77, 67, 43], [160, 51, 309, 67], [94, 289, 304, 186], [201, 251, 284, 184], [233, 33, 8, 122], [260, 191, 178, 10], [40, 155, 263, 30], [0, 0, 1], [0, 1]], ![[301, 136, 206, 158], [246, 9, 55, 123], [156, 308, 53, 151], [299, 200, 215, 101], [123, 198, 196, 154], [287, 219, 58, 122], [219, 268, 186, 127], [98, 274, 94, 249], [27, 77, 67, 43]], ![[13, 97, 38, 110], [95, 237, 90, 79], [95, 151, 176, 158], [113, 160, 23, 290], [42, 67, 299, 41], [147, 230, 253, 76], [171, 292, 55, 229], [296, 245, 238, 135], [301, 136, 206, 158]], ![[0, 1], [130, 14, 168, 42], [71, 185, 89, 127], [165, 11, 100, 47], [302, 13, 119, 305], [285, 293, 133, 103], [196, 218, 118, 236], [99, 103, 289, 238], [13, 97, 38, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [145, 184, 74], []]
 b := ![[], [], [73, 179, 131, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [271, 156, 48, 281, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9447933712896, -4643209248260, 10089909005489, 5419072738035, 18978634447313]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9794306898016, -9107587594527, -2835710321602, -1447164482307, 18978634447313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, -8, 3, 3, 13]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![14, -8, 3, 3, 13]] 
 ![![311, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![184, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![14, -8, 3, 3, 13], ![-20, 12, 9, 2, 20], ![32, 31, -56, -30, -168], ![34, -69, 59, 39, 194], ![-25, 2, 17, 7, 46]]]
  hmulB := by decide  
  f := ![![![-24, -380, 475, 183, 1135]], ![![-4, -66, 83, 32, 198]], ![![-8, -89, 111, 43, 265]], ![![-14, -193, 245, 95, 582]], ![![-1, -34, 42, 16, 101]]]
  g := ![![![-2, -8, 3, 3, 13], ![-7, 12, 9, 2, 20], ![38, 31, -56, -30, -168], ![-39, -69, 59, 39, 194], ![-12, 2, 17, 7, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-24, -380, 475, 183, 1135]] ![![14, -8, 3, 3, 13]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![832, 639, -312, -201, -899]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![832, 639, -312, -201, -899]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![146, 149, 180, 128, 1]] where
  M :=![![![832, 639, -312, -201, -899], ![1228, 743, -304, -244, -892], ![2288, 1992, -1797, -944, -4272], ![2170, 298, -892, -683, -1250], ![-821, -497, 660, 365, 1360]]]
  hmulB := by decide  
  f := ![![![-18, 19, -8, -7, -31]], ![![44, -17, -16, -4, -36]], ![![-48, -40, 91, 48, 272]], ![![-54, 118, -100, -67, -334]], ![![-37, 26, 0, -5, -12]]]
  g := ![![![422, 430, 516, 367, -899], ![420, 427, 512, 364, -892], ![2000, 2040, 2451, 1744, -4272], ![590, 596, 716, 509, -1250], ![-637, -649, -780, -555, 1360]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 4 2 8 [105, 200, 86, 310, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100, 149, 20], [288, 177, 270, 131], [285, 35, 207, 162], [0, 1]]
 g := ![![[229, 227, 101, 139], [248, 263, 304], [204, 266, 151], [94, 129, 25, 144], [311, 133, 48, 291], [127, 199, 137, 9], [1], []], ![[134, 288, 79, 127, 44, 250], [264, 83, 176], [139, 113, 166], [235, 250, 65, 15, 98, 186], [159, 262, 11, 101, 307, 135], [115, 198, 72, 98, 301, 262], [261, 288, 242], [135, 274, 87]], ![[141, 238, 224, 287, 190, 111], [9, 192, 36], [74, 78, 304], [255, 156, 312, 191, 257, 47], [273, 238, 127, 97, 285, 28], [203, 134, 13, 90, 42, 262], [61, 199, 36], [116, 153, 259]], ![[303, 154, 35, 116, 54, 99], [261, 76, 81], [160, 51, 115], [291, 133, 198, 63, 92, 79], [174, 0, 163, 37, 245, 274], [247, 261, 312, 3, 163, 291], [292, 83, 88], [238, 255, 265]]]
 h' := ![![[56, 100, 149, 20], [113, 42, 44, 96], [209, 232, 165, 238], [146, 174, 142, 82], [210, 246, 283, 12], [124, 99, 55, 149], [208, 113, 227, 3], [0, 0, 1], [0, 1]], ![[288, 177, 270, 131], [277, 277, 70, 13], [80, 261, 286, 72], [163, 182, 293, 127], [262, 146, 289, 149], [89, 109, 159, 32], [309, 53, 241, 67], [229, 189, 284, 245], [56, 100, 149, 20]], ![[285, 35, 207, 162], [32, 27, 131, 157], [254, 2, 306, 307], [271, 84, 281, 238], [105, 207, 63, 84], [17, 146, 81, 19], [218, 225, 36, 193], [26, 87, 138, 6], [288, 177, 270, 131]], ![[0, 1], [140, 280, 68, 47], [312, 131, 182, 9], [264, 186, 223, 179], [56, 27, 304, 68], [292, 272, 18, 113], [84, 235, 122, 50], [208, 37, 203, 62], [285, 35, 207, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 154, 238], []]
 b := ![[], [], [222, 162, 83, 218], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 4
  hpos := by decide
  P := [105, 200, 86, 310, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-354821916425827234, -176060388083572326, 380834089087470500, 204216805428185015, 717483009371555626]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-335806202187453510, -342111913049346200, -411393315008921860, -292759132249619601, 717483009371555626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 9597924961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, 19, -8, -7, -31]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-18, 19, -8, -7, -31]] 
 ![![313, 0, 0, 0, 0], ![304, 1, 0, 0, 0], ![232, 0, 1, 0, 0], ![266, 0, 0, 1, 0], ![279, 0, 0, 0, 1]] where
  M :=![![![-18, 19, -8, -7, -31], ![44, -17, -16, -4, -36], ![-48, -40, 91, 48, 272], ![-54, 118, -100, -67, -334], ![43, -7, -28, -11, -74]]]
  hmulB := by decide  
  f := ![![![832, 639, -312, -201, -899]], ![![812, 623, -304, -196, -876]], ![![624, 480, -237, -152, -680]], ![![714, 544, -268, -173, -768]], ![![739, 568, -276, -178, -797]]]
  g := ![![![21, 19, -8, -7, -31], ![64, -17, -16, -4, -36], ![-312, -40, 91, 48, 272], ![314, 118, -100, -67, -334], ![103, -7, -28, -11, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![832, 639, -312, -201, -899]] ![![-18, 19, -8, -7, -31]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76, -495, 676, 389, 2097]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-76, -495, 676, 389, 2097]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![279, 270, 299, 1, 0], ![290, 166, 41, 0, 1]] where
  M :=![![![-76, -495, 676, 389, 2097], ![-948, 1597, -1170, -812, -3988], ![3536, -2642, 281, 620, 2096], ![-2774, -588, 3088, 1455, 8786], ![-1349, 1721, -990, -755, -3572]]]
  hmulB := by decide  
  f := ![![![-2158, -1571, 656, 459, 2001]], ![![-3012, -2219, 946, 652, 2868]], ![![-4176, -2982, 1177, 852, 3664]], ![![-8408, -6089, 2495, 1764, 7665]], ![![-4089, -2983, 1247, 871, 3804]]]
  g := ![![![-2261, -1431, -636, 389, 2097], ![4360, 2785, 1278, -812, -3988], ![-2452, -1634, -855, 620, 2096], ![-9327, -5842, -2499, 1455, 8786], ![3928, 2519, 1171, -755, -3572]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [142, 222, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [312, 59, 28], [193, 257, 289], [0, 1]]
 g := ![![[163, 90, 277], [273, 173], [212, 105, 268], [220, 280, 90], [164, 162, 82], [169, 197, 104], [188, 1], []], ![[231, 259, 142, 204], [219, 218], [292, 107, 276, 283], [285, 237, 158, 306], [81, 54, 76, 95], [85, 74, 127, 51], [10, 113], [121, 150]], ![[61, 219, 24, 307], [121, 24], [128, 44, 214, 124], [176, 2, 211, 268], [61, 53, 109, 186], [79, 34, 173, 160], [277, 311], [177, 150]]]
 h' := ![![[312, 59, 28], [29, 145, 223], [11, 2, 100], [143, 213, 164], [170, 144, 224], [94, 313, 84], [249, 283, 252], [0, 0, 1], [0, 1]], ![[193, 257, 289], [117, 132, 190], [222, 61, 79], [290, 250, 245], [224, 139, 102], [8, 236, 237], [101, 44, 95], [278, 66, 257], [312, 59, 28]], ![[0, 1], [289, 40, 221], [6, 254, 138], [263, 171, 225], [306, 34, 308], [46, 85, 313], [297, 307, 287], [69, 251, 59], [193, 257, 289]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 166], []]
 b := ![[], [53, 210, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [142, 222, 129, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1543421716, 788448412, -1682295106, -897583652, -3185115872]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3708684112, 2434906212, 1253264882, -897583652, -3185115872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2158, -1571, 656, 459, 2001]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-2158, -1571, 656, 459, 2001]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![98, 36, 1, 0, 0], ![138, 194, 0, 1, 0], ![258, 223, 0, 0, 1]] where
  M :=![![![-2158, -1571, 656, 459, 2001], ![-3012, -2219, 946, 652, 2868], ![-4176, -2982, 1177, 852, 3664], ![-1390, -1156, 548, 339, 1630], ![815, 595, -234, -167, -734]]]
  hmulB := by decide  
  f := ![![![-76, -495, 676, 389, 2097]], ![![-948, 1597, -1170, -812, -3988]], ![![-120, 20, 77, 30, 202]], ![![-622, 760, -412, -323, -1500]], ![![-733, 726, -276, -257, -1110]]]
  g := ![![![-2038, -1768, 656, 459, 2001], ![-2920, -2531, 946, 652, 2868], ![-3730, -3242, 1177, 852, 3664], ![-1648, -1420, 548, 339, 1630], ![745, 647, -234, -167, -734]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [229, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [200, 316], [0, 1]]
 g := ![![[204, 1], [66], [85, 49], [144, 181], [67, 73], [202, 142], [58], [1]], ![[87, 316], [66], [58, 268], [206, 136], [85, 244], [72, 175], [58], [1]]]
 h' := ![![[200, 316], [2, 1], [189, 137], [309, 310], [190, 112], [24, 285], [168, 201], [88, 200], [0, 1]], ![[0, 1], [202, 316], [10, 180], [177, 7], [83, 205], [281, 32], [109, 116], [146, 117], [200, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [101, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [229, 117, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16564424, -11115127, 21037012, 10772793, 41561503]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45071624, -38254210, 21037012, 10772793, 41561503]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-76, -495, 676, 389, 2097]] ![![-2158, -1571, 656, 459, 2001]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27389, 19985, -8405, -5854, -25570]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![27389, 19985, -8405, -5854, -25570]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![5, 162, 189, 246, 1]] where
  M :=![![![27389, 19985, -8405, -5854, -25570], ![38216, 27930, -11769, -8194, -35784], ![53520, 38997, -16566, -11506, -50200], ![18564, 13419, -6025, -4117, -17736], ![-10690, -7743, 3379, 2328, 10109]]]
  hmulB := by decide  
  f := ![![![3, -9, 7, 2, 14]], ![![8, 28, -35, -10, -72]], ![![-48, -125, 172, 58, 392]], ![![84, 281, -373, -143, -896]], ![![39, 151, -196, -78, -477]]]
  g := ![![![469, 12575, 14575, 18986, -25570], ![656, 17598, 20397, 26570, -35784], ![920, 24687, 28614, 37274, -50200], ![324, 8721, 10109, 13169, -17736], ![-185, -4971, -5762, -7506, 10109]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [100, 317, 233, 162, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [247, 174, 140, 244], [106, 148, 238, 33], [147, 8, 284, 54], [0, 1]]
 g := ![![[120, 120, 90, 143], [243, 1, 120, 287], [285, 46, 24], [102, 37, 309, 19], [293, 171, 104], [296, 229, 177], [169, 1], []], ![[64, 71, 231, 23, 224, 160], [36, 177, 185, 22, 256, 298], [188, 267, 180], [163, 243, 122, 10, 48, 142], [106, 89, 234], [275, 282, 127], [222, 265, 121, 1, 6, 264], [168, 311, 287]], ![[194, 236, 24, 96, 310, 232], [60, 81, 17, 64, 15, 149], [95, 66, 156], [74, 62, 305, 282, 20, 280], [96, 151, 184], [273, 196, 233], [170, 241, 50, 298, 157, 256], [236, 156, 96]], ![[37, 311, 322, 149, 94, 77], [136, 281, 252, 73, 255, 214], [86, 318, 324], [164, 60, 15, 49, 269, 21], [47, 286, 127], [142, 130, 266], [267, 304, 52, 114, 148, 284], [290, 165, 268]]]
 h' := ![![[247, 174, 140, 244], [194, 122, 217, 229], [46, 194, 188, 87], [61, 50, 282, 149], [233, 158, 85, 201], [220, 63, 239, 82], [312, 280, 26, 193], [0, 0, 1], [0, 1]], ![[106, 148, 238, 33], [5, 290, 156, 317], [162, 166, 45, 50], [162, 179, 295, 74], [248, 147, 94, 326], [16, 226, 264, 208], [93, 4, 295, 262], [186, 276, 198, 113], [247, 174, 140, 244]], ![[147, 8, 284, 54], [15, 126, 248, 268], [116, 195, 169, 128], [103, 327, 218, 90], [131, 58, 320, 29], [146, 172, 243, 110], [142, 217, 37, 137], [214, 213, 26, 236], [106, 148, 238, 33]], ![[0, 1], [88, 124, 41, 179], [101, 107, 260, 66], [162, 106, 198, 18], [47, 299, 163, 106], [160, 201, 247, 262], [262, 161, 304, 70], [222, 173, 106, 313], [147, 8, 284, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 105, 244], []]
 b := ![[], [], [252, 20, 259, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [100, 317, 233, 162, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13409900834211, -6748444375747, 14499819907646, 7757508807429, 27381709980836]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-454134292261, -13421708342209, -15591067572418, -20326716454617, 27381709980836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -9, 7, 2, 14]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![3, -9, 7, 2, 14]] 
 ![![331, 0, 0, 0, 0], ![187, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![221, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![3, -9, 7, 2, 14], ![8, 28, -35, -10, -72], ![-48, -125, 172, 58, 392], ![84, 281, -373, -143, -896], ![6, -11, 9, 8, 35]]]
  hmulB := by decide  
  f := ![![![27389, 19985, -8405, -5854, -25570]], ![![15589, 11375, -4784, -3332, -14554]], ![![9843, 7182, -3021, -2104, -9190]], ![![18343, 13384, -5630, -3921, -17126]], ![![4436, 3237, -1361, -948, -4141]]]
  g := ![![![-1, -9, 7, 2, 14], ![15, 28, -35, -10, -72], ![-93, -125, 172, 58, 392], ![215, 281, -373, -143, -896], ![-8, -11, 9, 8, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![27389, 19985, -8405, -5854, -25570]] ![![3, -9, 7, 2, 14]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68, 568, -679, -267, -1659]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![68, 568, -679, -267, -1659]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![54, 107, 50, 1, 0], ![272, 330, 267, 0, 1]] where
  M :=![![![68, 568, -679, -267, -1659], ![-228, -2174, 2569, 1006, 6252], ![864, 8235, -9722, -3774, -23576], ![-1750, -14641, 17417, 6735, 42070], ![11, -446, 489, 199, 1228]]]
  hmulB := by decide  
  f := ![![![874, 636, -265, -185, -807]], ![![1212, 896, -375, -262, -1148]], ![![1696, 1223, -500, -350, -1544]], ![![778, 569, -236, -165, -724]], ![![3235, 2359, -977, -683, -2998]]]
  g := ![![![1382, 1711, 1352, -267, -1659], ![-5208, -6448, -5095, 1006, 6252], ![19636, 24309, 19210, -3774, -23576], ![-35040, -43378, -34279, 6735, 42070], ![-1023, -1267, -1001, 199, 1228]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [163, 275, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [186, 58, 118], [26, 278, 219], [0, 1]]
 g := ![![[187, 209, 168], [122, 27], [242, 311], [293, 282], [314, 278, 323], [175, 145], [185, 212, 1], []], ![[144, 248, 96, 320], [224, 72], [290, 263], [98, 144], [195, 247, 80, 186], [6, 179], [275, 33, 119, 292], [313, 107]], ![[315, 170, 103, 186], [78, 104], [132, 189], [10, 285], [132, 200, 276, 93], [233, 305], [114, 196, 66, 34], [212, 107]]]
 h' := ![![[186, 58, 118], [320, 203, 239], [266, 149, 135], [174, 225, 206], [42, 121, 48], [78, 170, 71], [175, 167, 303], [0, 0, 1], [0, 1]], ![[26, 278, 219], [276, 63, 80], [27, 5, 181], [241, 260, 242], [245, 285, 325], [7, 315, 32], [206, 231, 144], [90, 288, 278], [186, 58, 118]], ![[0, 1], [322, 71, 18], [60, 183, 21], [285, 189, 226], [277, 268, 301], [143, 189, 234], [190, 276, 227], [157, 49, 58], [26, 278, 219]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198, 111], []]
 b := ![[], [303, 202, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [163, 275, 125, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355942517, -487249610, 732901260, 334086950, 1590869620]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1338614761, -1665345780, -1307814940, 334086950, 1590869620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![874, 636, -265, -185, -807]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![874, 636, -265, -185, -807]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![326, 237, 1, 0, 0], ![124, 50, 0, 1, 0], ![190, 206, 0, 0, 1]] where
  M :=![![![874, 636, -265, -185, -807], ![1212, 896, -375, -262, -1148], ![1696, 1223, -500, -350, -1544], ![506, 387, -97, -81, -374], ![-325, -230, 81, 59, 266]]]
  hmulB := by decide  
  f := ![![![68, 568, -679, -267, -1659]], ![![-228, -2174, 2569, 1006, 6252]], ![![-92, -955, 1121, 438, 2722]], ![![-14, -157, 183, 71, 442]], ![![-101, -1010, 1189, 465, 2890]]]
  g := ![![![782, 709, -265, -185, -807], ![1110, 1007, -375, -262, -1148], ![1488, 1351, -500, -350, -1544], ![336, 310, -97, -81, -374], ![-251, -229, 81, 59, 266]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P1 : CertificateIrreducibleZModOfList' 337 2 2 8 [121, 224, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 336], [0, 1]]
 g := ![![[311, 39], [214], [187], [189], [319, 2], [56], [151, 300], [1]], ![[0, 298], [214], [187], [189], [208, 335], [56], [14, 37], [1]]]
 h' := ![![[113, 336], [51, 92], [296, 302], [119, 47], [156, 111], [238, 311], [264, 122], [216, 113], [0, 1]], ![[0, 1], [0, 245], [48, 35], [38, 290], [230, 226], [333, 26], [233, 215], [179, 224], [113, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [221, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N1 : CertifiedPrimeIdeal' SI337N1 337 where
  n := 2
  hpos := by decide
  P := [121, 224, 1]
  hirr := P337P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91877, -50666, 107865, 58470, 208940]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-243931, -212403, 107865, 58470, 208940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N1 B_one_repr
lemma NI337N1 : Nat.card (O ⧸ I337N1) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![68, 568, -679, -267, -1659]] ![![874, 636, -265, -185, -807]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4245, -3103, 1303, 908, 3972]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-4245, -3103, 1303, 908, 3972]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![34, 133, 31, 1, 0], ![257, 65, 185, 0, 1]] where
  M :=![![![-4245, -3103, 1303, 908, 3972], ![-5904, -4306, 1781, 1246, 5456], ![-8080, -5973, 2358, 1674, 7400], ![-2336, -1811, 355, 327, 1684], ![1488, 1135, -359, -274, -1269]]]
  hmulB := by decide  
  f := ![![![-15, -85, 103, 36, 236]], ![![80, 348, -441, -162, -1040]], ![![-272, -1443, 1796, 686, 4328]], ![![6, 4, -8, -1, -12]], ![![-141, -767, 951, 362, 2287]]]
  g := ![![![-3043, -1101, -2195, 908, 3972], ![-4180, -1512, -3015, 1246, 5456], ![-5668, -2045, -4088, 1674, 7400], ![-1286, -446, -926, 327, 1684], ![971, 346, 700, -274, -1269]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [80, 186, 283, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [343, 27, 70], [68, 319, 277], [0, 1]]
 g := ![![[295, 89, 181], [99, 118, 1], [297, 246], [344, 265, 71], [129, 269, 94], [175, 339], [93, 64, 1], []], ![[264, 10, 142, 18], [272, 285, 115, 239], [47, 161], [154, 330, 16, 189], [143, 272, 109, 45], [169, 75], [332, 296, 45, 54], [222, 42]], ![[114, 260, 108, 169], [297, 61, 98, 302], [156, 126], [69, 127, 215, 44], [193, 204, 36, 143], [213, 25], [302, 185, 173, 326], [15, 42]]]
 h' := ![![[343, 27, 70], [61, 49, 212], [181, 320, 346], [240, 297, 151], [90, 155, 50], [40, 79, 326], [194, 137, 214], [0, 0, 1], [0, 1]], ![[68, 319, 277], [311, 230, 270], [336, 70, 220], [283, 145, 253], [243, 323, 81], [17, 174, 219], [345, 314, 128], [300, 242, 319], [343, 27, 70]], ![[0, 1], [234, 68, 212], [126, 304, 128], [304, 252, 290], [2, 216, 216], [132, 94, 149], [13, 243, 5], [301, 105, 27], [68, 319, 277]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 124], []]
 b := ![[], [256, 283, 256], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [80, 186, 283, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87016034, 42091332, -92188268, -49613570, -173027296]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![133261938, 51548906, 96414646, -49613570, -173027296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 0, 7, 3, 19]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![-8, 0, 7, 3, 19]] 
 ![![347, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![288, 0, 0, 0, 1]] where
  M :=![![![-8, 0, 7, 3, 19], ![4, 18, -25, -14, -76], ![32, -59, 46, 30, 152], ![-58, 49, -9, -11, -38], ![-3, 22, -25, -15, -80]]]
  hmulB := by decide  
  f := ![![![702, 500, -205, -149, -627]], ![![84, 60, -25, -18, -76]], ![![278, 197, -81, -59, -247]], ![![118, 85, -39, -27, -114]], ![![581, 414, -169, -123, -518]]]
  g := ![![![-19, 0, 7, 3, 19], ![73, 18, -25, -14, -76], ![-142, -59, 46, 30, 152], ![31, 49, -9, -11, -38], ![76, 22, -25, -15, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 45, -54, -21, -131]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![6, 45, -54, -21, -131]] 
 ![![347, 0, 0, 0, 0], ![245, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![284, 0, 0, 0, 1]] where
  M :=![![![6, 45, -54, -21, -131], ![-20, -173, 206, 80, 500], ![80, 666, -793, -308, -1920], ![-134, -1184, 1406, 543, 3406], ![-5, -35, 42, 17, 102]]]
  hmulB := by decide  
  f := ![![![1336, 855, -326, -229, -965]], ![![948, 608, -232, -163, -687]], ![![32, 20, -9, -6, -26]], ![![42, 26, -10, -7, -28]], ![![1091, 699, -266, -187, -788]]]
  g := ![![![77, 45, -54, -21, -131], ![-293, -173, 206, 80, 500], ![1124, 666, -793, -308, -1920], ![-1992, -1184, 1406, 543, 3406], ![-60, -35, 42, 17, 102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-4245, -3103, 1303, 908, 3972]] ![![-8, 0, 7, 3, 19]]
  ![![-1336, -855, 326, 229, 965]] where
 M := ![![![-1336, -855, 326, 229, 965]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![-1336, -855, 326, 229, 965]] ![![6, 45, -54, -21, -131]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![-347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 352, -146, -102, -444]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![487, 352, -146, -102, -444]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![210, 21, 1, 0, 0], ![238, 234, 0, 1, 0], ![324, 3, 0, 0, 1]] where
  M :=![![![487, 352, -146, -102, -444], ![672, 503, -212, -148, -648], ![960, 680, -289, -200, -880], ![304, 224, -74, -55, -236], ![-192, -128, 52, 36, 159]]]
  hmulB := by decide  
  f := ![![![-5, -48, 54, 18, 116]], ![![32, 171, -212, -68, -488]], ![![-2, -21, 23, 8, 48]], ![![18, 86, -110, -35, -260]], ![![-4, -43, 48, 16, 103]]]
  g := ![![![571, 82, -146, -102, -444], ![832, 119, -212, -148, -648], ![1130, 161, -289, -200, -880], ![302, 44, -74, -55, -236], ![-204, -29, 52, 36, 159]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 2 2 8 [236, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [262, 348], [0, 1]]
 g := ![![[61, 337], [205], [83, 180], [284, 268], [20, 226], [67], [291, 240], [1]], ![[58, 12], [205], [128, 169], [2, 81], [251, 123], [67], [2, 109], [1]]]
 h' := ![![[262, 348], [322, 141], [305, 113], [333, 326], [166, 172], [238, 122], [77, 263], [113, 262], [0, 1]], ![[0, 1], [270, 208], [246, 236], [240, 23], [209, 177], [94, 227], [230, 86], [4, 87], [262, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [189, 233]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 2
  hpos := by decide
  P := [236, 87, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1609536, -1067887, 2032887, 1041192, 4011130]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5661678, -857968, 2032887, 1041192, 4011130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -11, 18, 9, 39]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-10, -11, 18, 9, 39]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![158, 182, 1, 0, 0], ![280, 95, 0, 1, 0], ![247, 207, 0, 0, 1]] where
  M :=![![![-10, -11, 18, 9, 39], ![-60, -7, 40, 24, 60], ![-336, -236, 437, 224, 864], ![-930, -346, 870, 489, 1570], ![265, 139, -292, -157, -554]]]
  hmulB := by decide  
  f := ![![![340, 261, -134, -89, -409]], ![![500, 261, -80, -56, -220]], ![![416, 256, -103, -70, -302]], ![![410, 281, -130, -87, -390]], ![![537, 339, -142, -96, -419]]]
  g := ![![![-43, -35, 18, 9, 39], ![-80, -63, 40, 24, 60], ![-990, -802, 437, 224, 864], ![-1900, -1519, 870, 489, 1570], ![651, 524, -292, -157, -554]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P1 : CertificateIrreducibleZModOfList' 349 2 2 8 [290, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [320, 348], [0, 1]]
 g := ![![[35, 92], [168], [270, 346], [107, 334], [56, 93], [326], [109, 143], [1]], ![[159, 257], [168], [8, 3], [193, 15], [151, 256], [326], [150, 206], [1]]]
 h' := ![![[320, 348], [160, 328], [225, 283], [31, 245], [163, 166], [253, 82], [149, 32], [59, 320], [0, 1]], ![[0, 1], [71, 21], [45, 66], [255, 104], [235, 183], [318, 267], [268, 317], [202, 29], [320, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [186]]
 b := ![[], [127, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N1 : CertifiedPrimeIdeal' SI349N1 349 where
  n := 2
  hpos := by decide
  P := [290, 29, 1]
  hirr := P349P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-413727, -302065, 553114, 279627, 1107021]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1259414, -1022025, 553114, 279627, 1107021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N1 B_one_repr
lemma NI349N1 : Nat.card (O ⧸ I349N1) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -3, 0, 1, 3]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![4, -3, 0, 1, 3]] 
 ![![349, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![322, 0, 1, 0, 0], ![153, 0, 0, 1, 0], ![329, 0, 0, 0, 1]] where
  M :=![![![4, -3, 0, 1, 3], ![-12, -3, 12, 4, 28], ![16, 36, -55, -24, -144], ![6, -78, 84, 39, 226], ![-11, 1, 8, 3, 20]]]
  hmulB := by decide  
  f := ![![![-266, -211, 48, 43, 195]], ![![-112, -89, 20, 18, 82]], ![![-244, -194, 41, 38, 174]], ![![-108, -89, 12, 14, 69]], ![![-253, -200, 48, 42, 189]]]
  g := ![![![-2, -3, 0, 1, 3], ![-38, -3, 12, 4, 28], ![182, 36, -55, -24, -144], ![-275, -78, 84, 39, 226], ![-28, 1, 8, 3, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![487, 352, -146, -102, -444]] ![![-10, -11, 18, 9, 39]]
  ![![266, 211, -48, -43, -195]] where
 M := ![![![266, 211, -48, -43, -195]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![266, 211, -48, -43, -195]] ![![4, -3, 0, 1, 3]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1, I349N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
    exact isPrimeI349N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0 ⊙ MulI349N1)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 79, -47, -32, -152]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![39, 79, -47, -32, -152]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![281, 307, 1, 0, 0], ![109, 142, 0, 1, 0], ![294, 14, 0, 0, 1]] where
  M :=![![![39, 79, -47, -32, -152], ![160, -8, -9, 2, 0], ![-48, 113, 64, 14, 152], ![56, 183, -219, -129, -684], ![68, -75, 3, 14, 39]]]
  hmulB := by decide  
  f := ![![![-57, 15, 15, 16, 0]], ![![-384, -346, 591, 286, 1216]], ![![-385, -290, 530, 264, 1064]], ![![-189, -146, 264, 131, 532]], ![![-58, 1, 31, 22, 39]]]
  g := ![![![174, 60, -47, -32, -152], ![7, 7, -9, 2, 0], ![-182, -67, 64, 14, 152], ![784, 270, -219, -129, -684], ![-39, -10, 3, 14, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [184, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 352], [0, 1]]
 g := ![![[306, 259], [315], [73], [213], [146], [337, 152], [228, 265], [1]], ![[0, 94], [315], [73], [213], [146], [261, 201], [272, 88], [1]]]
 h' := ![![[176, 352], [246, 139], [291, 204], [223, 255], [244, 289], [120, 128], [55, 161], [169, 176], [0, 1]], ![[0, 1], [0, 214], [189, 149], [272, 98], [276, 64], [56, 225], [151, 192], [81, 177], [176, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [178, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 2
  hpos := by decide
  P := [184, 177, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41792, -21927, 47529, 25242, 91136]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-121651, -55166, 47529, 25242, 91136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -31, 35, 14, 86]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-1, -31, 35, 14, 86]] 
 ![![353, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![163, 0, 0, 0, 1]] where
  M :=![![![-1, -31, 35, 14, 86], ![8, 112, -129, -50, -312], ![-48, -419, 496, 190, 1192], ![100, 747, -897, -343, -2160], ![-2, 21, -21, -8, -49]]]
  hmulB := by decide  
  f := ![![![3547, 2565, -1079, -750, -3294]], ![![918, 664, -279, -194, -852]], ![![209, 152, -63, -44, -194]], ![![1601, 1158, -484, -337, -1482]], ![![1635, 1182, -498, -346, -1519]]]
  g := ![![![-40, -31, 35, 14, 86], ![145, 112, -129, -50, -312], ![-556, -419, 496, 190, 1192], ![1010, 747, -897, -343, -2160], ![22, 21, -21, -8, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N1 : Nat.card (O ⧸ I353N1) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N1)

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := prime_ideal_of_norm_prime hp353.out _ NI353N1

def I353N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, 122, -52, -36, -158]] i)))

def SI353N2: IdealEqSpanCertificate' Table ![![165, 122, -52, -36, -158]] 
 ![![353, 0, 0, 0, 0], ![328, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![319, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![165, 122, -52, -36, -158], ![232, 165, -68, -48, -208], ![320, 244, -107, -72, -320], ![108, 68, -20, -19, -72], ![-62, -48, 20, 14, 61]]]
  hmulB := by decide  
  f := ![![![33, 30, -28, -16, 22]], ![![32, 29, -28, -16, 16]], ![![17, 10, -15, -8, -10]], ![![51, 38, -48, -27, -22]], ![![-4, 0, 4, 2, 13]]]
  g := ![![![-55, 122, -52, -36, -158], ![-76, 165, -68, -48, -208], ![-109, 244, -107, -72, -320], ![-35, 68, -20, -19, -72], ![22, -48, 20, 14, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N2 : Nat.card (O ⧸ I353N2) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N2)

lemma isPrimeI353N2 : Ideal.IsPrime I353N2 := prime_ideal_of_norm_prime hp353.out _ NI353N2

def I353N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 25, -35, -20, -108]] i)))

def SI353N3: IdealEqSpanCertificate' Table ![![5, 25, -35, -20, -108]] 
 ![![353, 0, 0, 0, 0], ![334, 1, 0, 0, 0], ![345, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![5, 25, -35, -20, -108], ![48, -82, 61, 42, 208], ![-176, 143, -26, -38, -136], ![160, 29, -167, -79, -460], ![64, -91, 57, 42, 197]]]
  hmulB := by decide  
  f := ![![![3341, 2641, -1285, -812, -3740]], ![![3174, 2506, -1217, -770, -3544]], ![![3285, 2604, -1273, -802, -3700]], ![![1046, 811, -383, -247, -1124]], ![![157, 124, -60, -38, -175]]]
  g := ![![![22, 25, -35, -20, -108], ![-5, -82, 61, 42, 208], ![-92, 143, -26, -38, -136], ![183, 29, -167, -79, -460], ![8, -91, 57, 42, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N3 : Nat.card (O ⧸ I353N3) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N3)

lemma isPrimeI353N3 : Ideal.IsPrime I353N3 := prime_ideal_of_norm_prime hp353.out _ NI353N3
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![39, 79, -47, -32, -152]] ![![-1, -31, 35, 14, 86]]
  ![![-47, 236, -242, -142, -750]] where
 M := ![![![-47, 236, -242, -142, -750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N1 : IdealMulLeCertificate' Table 
  ![![-47, 236, -242, -142, -750]] ![![165, 122, -52, -36, -158]]
  ![![721, 502, 130, -14, 252]] where
 M := ![![![721, 502, 130, -14, 252]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N2 : IdealMulLeCertificate' Table 
  ![![721, 502, 130, -14, 252]] ![![5, 25, -35, -20, -108]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![18709, -27887, 18709, 13414, 64952]]]
 hmul := by decide  
 g := ![![![![53, -79, 53, 38, 184]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1, I353N2, I353N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
    exact isPrimeI353N2
    exact isPrimeI353N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0 ⊙ MulI353N1 ⊙ MulI353N2)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 158, -242, -114, -538]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![123, 158, -242, -114, -538]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![0, 0, 0, 359, 0], ![246, 316, 234, 131, 1]] where
  M :=![![![123, 158, -242, -114, -538], ![584, -105, -180, -156, -56], ![3520, 3144, -5329, -2632, -10960], ![9372, 2232, -7354, -4387, -12308], ![-2718, -1460, 3036, 1626, 5803]]]
  hmulB := by decide  
  f := ![![![57, 38, -14, -10, -42]], ![![72, 65, -28, -20, -88]], ![![128, 72, -39, -24, -112]], ![![28, 16, 10, 3, 28]], ![![196, 136, -56, -39, -169]]]
  g := ![![![369, 474, 350, 196, -538], ![40, 49, 36, 20, -56], ![7520, 9656, 7129, 3992, -10960], ![8460, 10840, 8002, 4479, -12308], ![-3984, -5112, -3774, -2113, 5803]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 4 2 8 [302, 228, 96, 247, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [352, 234, 193, 219], [45, 294, 60, 236], [74, 189, 106, 263], [0, 1]]
 g := ![![[277, 146, 52, 91], [259, 209, 196, 254], [320, 33, 207, 108], [205, 302, 27], [248, 16, 135], [103, 212, 195, 47], [112, 1], []], ![[127, 231, 107, 351, 231, 74], [113, 106, 22, 4, 305, 121], [258, 203, 208, 144, 14, 235], [61, 148, 131], [247, 242, 92], [4, 206, 71, 343, 331, 153], [128, 336, 232, 265, 348, 88], [83, 84, 214]], ![[136, 80, 31, 209, 105, 104], [353, 30, 175, 110, 356, 348], [292, 106, 211, 312, 62, 357], [71, 286, 294], [56, 226, 120], [308, 45, 279, 14, 144, 140], [325, 331, 172, 346, 254, 304], [56, 286, 51]], ![[110, 161, 244, 164, 288, 210], [267, 320, 319, 138, 288, 221], [292, 229, 252, 176, 112, 332], [190, 38, 233], [20, 163, 242], [331, 111, 71, 340, 200, 325], [166, 84, 178, 311, 243, 356], [109, 178, 241]]]
 h' := ![![[352, 234, 193, 219], [44, 343, 339, 74], [290, 232, 251, 297], [231, 64, 250, 99], [109, 307, 317, 229], [127, 69, 155, 213], [281, 10, 149, 242], [0, 0, 1], [0, 1]], ![[45, 294, 60, 236], [340, 249, 123, 94], [123, 56, 112, 110], [157, 226, 150, 122], [98, 106, 340, 61], [296, 317, 236, 181], [124, 82, 158, 191], [113, 179, 155, 208], [352, 234, 193, 219]], ![[74, 189, 106, 263], [18, 308, 195, 16], [321, 29, 155, 199], [178, 257, 10, 86], [126, 153, 239, 139], [237, 325, 59, 174], [154, 325, 53, 26], [191, 197, 106, 14], [45, 294, 60, 236]], ![[0, 1], [205, 177, 61, 175], [230, 42, 200, 112], [108, 171, 308, 52], [293, 152, 181, 289], [314, 7, 268, 150], [50, 301, 358, 259], [201, 342, 97, 137], [74, 189, 106, 263]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [89, 75, 355], []]
 b := ![[], [], [25, 303, 243, 286], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 4
  hpos := by decide
  P := [302, 228, 96, 247, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2468411070802374, -1212016894744657, 2634911058651661, 1415354656337158, 4955408790666816]
  a := ![649, 505, -992, -453, -2054]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3402504104665290, -4365240096784007, -3222648317430037, -1804298598665782, 4955408790666816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 16610312161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, -38, 14, 10, 42]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-57, -38, 14, 10, 42]] 
 ![![359, 0, 0, 0, 0], ![112, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![204, 0, 0, 1, 0], ![241, 0, 0, 0, 1]] where
  M :=![![![-57, -38, 14, 10, 42], ![-72, -65, 28, 20, 88], ![-128, -72, 39, 24, 112], ![-28, -16, -10, -3, -28], ![30, 8, -4, -2, -9]]]
  hmulB := by decide  
  f := ![![![-123, -158, 242, 114, 538]], ![![-40, -49, 76, 36, 168]], ![![-17, -18, 29, 14, 62]], ![![-96, -96, 158, 77, 340]], ![![-75, -102, 154, 72, 345]]]
  g := ![![![-23, -38, 14, 10, 42], ![-52, -65, 28, 20, 88], ![-69, -72, 39, 24, 112], ![26, -16, -10, -3, -28], ![5, 8, -4, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![123, 158, -242, -114, -538]] ![![-57, -38, 14, 10, 42]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![-359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0)


lemma PB547I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB547I7 : PrimesBelowBoundCertificateInterval O 307 359 547 where
  m := 9
  g := ![2, 2, 2, 2, 2, 3, 3, 4, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB547I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0, I353N1, I353N2, I353N3]
    · exact ![I359N0, I359N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![9354951841, 311]
    · exact ![9597924961, 313]
    · exact ![31855013, 100489]
    · exact ![12003612721, 331]
    · exact ![38272753, 113569]
    · exact ![41781923, 347, 347]
    · exact ![121801, 121801, 349]
    · exact ![124609, 353, 353, 353]
    · exact ![16610312161, 359]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
      exact NI353N2
      exact NI353N3
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I313N1, I331N1, I347N1, I347N2, I349N2, I353N1, I353N2, I353N3, I359N1]
  Il := ![[I311N1], [I313N1], [], [I331N1], [], [I347N1, I347N2], [I349N2], [I353N1, I353N2, I353N3], [I359N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
