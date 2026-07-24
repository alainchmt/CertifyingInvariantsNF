
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7333, 3051, -13311, 6006, 15254]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![-7333, 3051, -13311, 6006, 15254]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![9, 294, 1, 0, 0], ![59, 133, 0, 1, 0], ![372, 142, 0, 0, 1]] where
  M :=![![![-7333, 3051, -13311, 6006, 15254], ![3242, -1327, 5815, -2733, -7066], ![-1600, 509, -2460, 1750, 5336], ![1836, 150, 423, -4726, -17212], ![-1240, 11, -692, 2695, 9721]]]
  hmulB := by decide  
  f := ![![![31067, 100480, 90699, -43273, -102118]], ![![-15572, -12206, 72779, -32234, -81460]], ![![-7977, -5050, 41009, -18212, -45910]], ![![-433, 7951, 27713, -12612, -31084]], ![![17278, 65907, 81506, -38233, -91641]]]
  g := ![![![-10936, 1759, -13311, 6006, 15254], ![5066, -636, 5815, -2733, -7066], ![-3822, -493, -2460, 1750, 5336], ![12347, 5450, 423, -4726, -17212], ![-6969, -2838, -692, 2695, 9721]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 2 2 9 [272, 462, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 540], [0, 1]]
 g := ![![[308, 21], [48], [191, 115], [516, 154], [119, 540], [406], [237], [290], [1]], ![[344, 520], [48], [79, 426], [239, 387], [40, 1], [406], [237], [290], [1]]]
 h' := ![![[79, 540], [184, 283], [525, 228], [308, 307], [92, 413], [262, 52], [103, 270], [514, 492], [269, 79], [0, 1]], ![[0, 1], [360, 258], [143, 313], [216, 234], [259, 128], [42, 489], [334, 271], [430, 49], [18, 462], [79, 540]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [86, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 2
  hpos := by decide
  P := [272, 462, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15587, 16797, 35181, 176776, 395115]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-291580, -166255, 35181, 176776, 395115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 292681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, -256, -42, 78, 248]] i)))

def SI541N1: IdealEqSpanCertificate' Table ![![-117, -256, -42, 78, 248]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![365, 53, 1, 0, 0], ![131, 261, 0, 1, 0], ![319, 144, 0, 0, 1]] where
  M :=![![![-117, -256, -42, 78, 248], ![92, -39, -270, -204, -940], ![-532, -112, 289, 1902, 7412], ![3608, 1370, -1818, -11849, -46120], ![-1964, -754, 1004, 6418, 24991]]]
  hmulB := by decide  
  f := ![![![1999, -1004, 3290, -2882, -6352]], ![![-588, -883, -3298, -7592, -13060]], ![![1295, -779, 1877, -2788, -5744]], ![![221, -765, -930, -5003, -8988]], ![![1017, -802, 1098, -3552, -6921]]]
  g := ![![![-137, -100, -42, 78, 248], ![786, 375, -270, -204, -940], ![-5027, -2919, 289, 1902, 7412], ![31297, 18173, -1818, -11849, -46120], ![-16971, -9848, 1004, 6418, 24991]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P1 : CertificateIrreducibleZModOfList' 541 2 2 9 [308, 315, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [226, 540], [0, 1]]
 g := ![![[333, 172], [103], [305, 135], [83, 182], [425, 252], [141], [151], [222], [1]], ![[253, 369], [103], [519, 406], [99, 359], [31, 289], [141], [151], [222], [1]]]
 h' := ![![[226, 540], [502, 71], [194, 134], [404, 515], [22, 63], [84, 343], [459, 499], [520, 221], [233, 226], [0, 1]], ![[0, 1], [318, 470], [182, 407], [479, 26], [194, 478], [239, 198], [164, 42], [153, 320], [455, 315], [226, 540]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [469, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N1 : CertifiedPrimeIdeal' SI541N1 541 where
  n := 2
  hpos := by decide
  P := [308, 315, 1]
  hirr := P541P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2332826, 3155668, 6035949, 29891593, 64019772]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49063882, -32046770, 6035949, 29891593, 64019772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N1 B_one_repr
lemma NI541N1 : Nat.card (O ⧸ I541N1) = 292681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N1

def I541N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-291, -108, 159, 959, 3740]] i)))

def SI541N2: IdealEqSpanCertificate' Table ![![-291, -108, 159, 959, 3740]] 
 ![![541, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![234, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![330, 0, 0, 0, 1]] where
  M :=![![![-291, -108, 159, 959, 3740], ![1822, 668, -971, -5978, -23302], ![-11346, -4156, 6036, 37215, 145058], ![70628, 25869, -37569, -231657, -902956], ![-38302, -14029, 20374, 125629, 489679]]]
  hmulB := by decide  
  f := ![![![3981, 3937, -14595, 6412, 16304]], ![![1434, 1431, -5221, 2293, 5832]], ![![1720, 1703, -6298, 2766, 7034]], ![![350, 340, -1299, 566, 1442]], ![![2430, 2405, -8904, 3913, 9949]]]
  g := ![![![-2397, -108, 159, 959, 3740], ![14928, 668, -971, -5978, -23302], ![-92926, -4156, 6036, 37215, 145058], ![578444, 25869, -37569, -231657, -902956], ![-313694, -14029, 20374, 125629, 489679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N2 : Nat.card (O ⧸ I541N2) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N2)

lemma isPrimeI541N2 : Ideal.IsPrime I541N2 := prime_ideal_of_norm_prime hp541.out _ NI541N2
def MulI541N0 : IdealMulLeCertificate' Table 
  ![![-7333, 3051, -13311, 6006, 15254]] ![![-117, -256, -42, 78, 248]]
  ![![-69103, -24205, 33445, 223178, 868338]] where
 M := ![![![-69103, -24205, 33445, 223178, 868338]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI541N1 : IdealMulLeCertificate' Table 
  ![![-69103, -24205, 33445, 223178, 868338]] ![![-291, -108, 159, 959, 3740]]
  ![![541, 0, 0, 0, 0]] where
 M := ![![![-17899925799, -6556225356, 9521333828, 58710772044, 228844013834]]]
 hmul := by decide  
 g := ![![![![-33086739, -12118716, 17599508, 108522684, 423001874]]]]
 hle2 := by decide  


def PBC541 : ContainsPrimesAboveP 541 ![I541N0, I541N1, I541N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
    exact isPrimeI541N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 541 (by decide) (𝕀 ⊙ MulI541N0 ⊙ MulI541N1)
instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 12, -19, 9, 24]] i)))

def SI547N0: IdealEqSpanCertificate' Table ![![-15, 12, -19, 9, 24]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![126, 277, 1, 0, 0], ![106, 524, 0, 1, 0], ![538, 274, 0, 0, 1]] where
  M :=![![![-15, 12, -19, 9, 24], ![6, -6, 15, -10, -30], ![-10, -4, -6, 25, 90], ![40, 15, -19, -121, -480], ![-22, -7, 10, 67, 263]]]
  hmulB := by decide  
  f := ![![![-61, -97, -39, 22, 48]], ![![4, -39, -79, 47, 108]], ![![-12, -42, -49, 29, 66]], ![![-8, -56, -83, 50, 114]], ![![-58, -115, -78, 45, 101]]]
  g := ![![![-21, -11, -19, 9, 24], ![28, 17, 15, -10, -30], ![-92, -66, -6, 25, 90], ![500, 366, -19, -121, -480], ![-274, -201, 10, 67, 263]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P0 : CertificateIrreducibleZModOfList' 547 2 2 9 [441, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [468, 546], [0, 1]]
 g := ![![[345, 129], [329, 475], [324], [56], [216], [109, 269], [289], [224], [1]], ![[0, 418], [0, 72], [324], [56], [216], [191, 278], [289], [224], [1]]]
 h' := ![![[468, 546], [413, 26], [195, 501], [50, 529], [35, 313], [67, 444], [239, 285], [519, 17], [106, 468], [0, 1]], ![[0, 1], [0, 521], [0, 46], [378, 18], [470, 234], [546, 103], [151, 262], [270, 530], [330, 79], [468, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [287]]
 b := ![[], [335, 417]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N0 : CertifiedPrimeIdeal' SI547N0 547 where
  n := 2
  hpos := by decide
  P := [441, 79, 1]
  hirr := P547P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9433, 14328, 26728, 131880, 279410]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-306543, -279804, 26728, 131880, 279410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N0 : Ideal.IsPrime I547N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N0 B_one_repr
lemma NI547N0 : Nat.card (O ⧸ I547N0) = 299209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N0

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 32, -6, 0, 2]] i)))

def SI547N1: IdealEqSpanCertificate' Table ![![15, 32, -6, 0, 2]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![269, 379, 1, 0, 0], ![338, 489, 0, 1, 0], ![541, 59, 0, 0, 1]] where
  M :=![![![15, 32, -6, 0, 2], ![2, 15, 30, -18, -34], ![2, -16, -5, -72, -178], ![-34, -70, -54, -161, 2], ![22, 26, 8, 4, -149]]]
  hmulB := by decide  
  f := ![![![-29363, 12220, -53374, 24016, 60902]], ![![12870, -5347, 23366, -10514, -26662]], ![![-5533, 2309, -10077, 4534, 11498]], ![![-6634, 2769, -12084, 5437, 13788]], ![![-27657, 11511, -50276, 22622, 57367]]]
  g := ![![![1, 4, -6, 0, 2], ![30, -1, 30, -18, -34], ![223, 87, -5, -72, -178], ![124, 181, -54, -161, 2], ![141, 7, 8, 4, -149]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P1 : CertificateIrreducibleZModOfList' 547 2 2 9 [534, 245, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [302, 546], [0, 1]]
 g := ![![[444, 189], [32, 140], [414], [290], [446], [373, 44], [93], [402], [1]], ![[87, 358], [193, 407], [414], [290], [446], [533, 503], [93], [402], [1]]]
 h' := ![![[302, 546], [416, 141], [535, 484], [456, 516], [334, 492], [473, 138], [270, 204], [472, 164], [13, 302], [0, 1]], ![[0, 1], [332, 406], [107, 63], [393, 31], [134, 55], [30, 409], [67, 343], [223, 383], [415, 245], [302, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [400]]
 b := ![[], [432, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N1 : CertifiedPrimeIdeal' SI547N1 547 where
  n := 2
  hpos := by decide
  P := [534, 245, 1]
  hirr := P547P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-498658, 520081, 1104710, 5520433, 12347966]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16167864, -7031420, 1104710, 5520433, 12347966]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N1 : Ideal.IsPrime I547N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N1 B_one_repr
lemma NI547N1 : Nat.card (O ⧸ I547N1) = 299209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N1

def I547N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1289, -539, 2347, -1056, -2678]] i)))

def SI547N2: IdealEqSpanCertificate' Table ![![1289, -539, 2347, -1056, -2678]] 
 ![![547, 0, 0, 0, 0], ![438, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![267, 0, 0, 1, 0], ![316, 0, 0, 0, 1]] where
  M :=![![![1289, -539, 2347, -1056, -2678], ![-566, 233, -1029, 463, 1174], ![248, -103, 448, -202, -512], ![-108, 46, -197, 86, 220], ![102, -43, 186, -83, -211]]]
  hmulB := by decide  
  f := ![![![-17, -2, 251, -201, -614]], ![![-14, -2, 201, -160, -488]], ![![-3, 0, 69, -62, -194]], ![![-19, -5, 128, -64, -164]], ![![-4, 1, 142, -135, -429]]]
  g := ![![![1840, -539, 2347, -1056, -2678], ![-804, 233, -1029, 463, 1174], ![352, -103, 448, -202, -512], ![-151, 46, -197, 86, 220], ![145, -43, 186, -83, -211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI547N2 : Nat.card (O ⧸ I547N2) = 547 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI547N2)

lemma isPrimeI547N2 : Ideal.IsPrime I547N2 := prime_ideal_of_norm_prime hp547.out _ NI547N2
def MulI547N0 : IdealMulLeCertificate' Table 
  ![![-15, 12, -19, 9, 24]] ![![15, 32, -6, 0, 2]]
  ![![-17, -2, 251, -201, -614]] where
 M := ![![![-17, -2, 251, -201, -614]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI547N1 : IdealMulLeCertificate' Table 
  ![![-17, -2, 251, -201, -614]] ![![1289, -539, 2347, -1056, -2678]]
  ![![547, 0, 0, 0, 0]] where
 M := ![![![547, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC547 : ContainsPrimesAboveP 547 ![I547N0, I547N1, I547N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI547N0
    exact isPrimeI547N1
    exact isPrimeI547N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 547 (by decide) (𝕀 ⊙ MulI547N0 ⊙ MulI547N1)
instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7619, -30146, -39297, 18389, 44172]] i)))

def SI557N0: IdealEqSpanCertificate' Table ![![-7619, -30146, -39297, 18389, 44172]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![0, 0, 557, 0, 0], ![406, 384, 9, 1, 0], ![173, 77, 123, 0, 1]] where
  M :=![![![-7619, -30146, -39297, 18389, 44172], ![7394, 10770, -19151, 8284, 21414], ![4846, 15678, 14208, -6807, -16110], ![-2496, -1961, 11367, -4851, -12024], ![70, -2193, -7138, 3153, 7627]]]
  hmulB := by decide  
  f := ![![![-416187, 173391, -756127, 340218, 862776]], ![![182340, -75969, 331269, -149077, -378036]], ![![-79882, 33263, -145164, 65176, 165378]], ![![-178882, 74523, -324997, 146212, 370800]], ![![-121757, 50722, -221216, 99502, 252355]]]
  g := ![![![-27137, -18838, -10122, 18389, 44172], ![-12676, -8652, -4897, 8284, 21414], ![9974, 6948, 3693, -6807, -16110], ![7266, 5003, 2754, -4851, -12024], ![-4667, -3232, -1748, 3153, 7627]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P0 : CertificateIrreducibleZModOfList' 557 3 2 9 [209, 57, 330, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [540, 310, 323], [244, 246, 234], [0, 1]]
 g := ![![[136, 373, 402], [314, 273], [279, 184, 359], [147, 302, 493], [10, 531], [130, 104, 196], [383, 183], [227, 1], []], ![[65, 188, 361, 132], [297, 36], [400, 439, 138, 443], [190, 431, 134, 263], [377, 203], [74, 7, 79, 457], [256, 267], [446, 360], [454, 170]], ![[227, 528, 273, 390], [55, 155], [398, 73, 447, 469], [534, 286, 65, 43], [1, 376], [12, 254, 213, 475], [350, 137], [210, 296], [543, 170]]]
 h' := ![![[540, 310, 323], [298, 288, 435], [174, 173, 477], [469, 539, 77], [228, 60, 170], [123, 542, 100], [296, 404, 14], [459, 220, 228], [0, 0, 1], [0, 1]], ![[244, 246, 234], [209, 53, 71], [376, 517, 551], [138, 473, 317], [536, 222, 487], [209, 332, 260], [300, 256, 256], [99, 309, 152], [93, 462, 246], [540, 310, 323]], ![[0, 1], [341, 216, 51], [498, 424, 86], [412, 102, 163], [278, 275, 457], [364, 240, 197], [261, 454, 287], [70, 28, 177], [78, 95, 310], [244, 246, 234]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 156], []]
 b := ![[], [471, 90, 372], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N0 : CertifiedPrimeIdeal' SI557N0 557 where
  n := 3
  hpos := by decide
  P := [209, 57, 330, 1]
  hirr := P557P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![865783889, -462753312, -1392264500, -7157347784, -17704489504]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10717460805, 7380977536, 4022757764, -7157347784, -17704489504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N0 : Ideal.IsPrime I557N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N0 B_one_repr
lemma NI557N0 : Nat.card (O ⧸ I557N0) = 172808693 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N0

def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-416187, 173391, -756127, 340218, 862776]] i)))

def SI557N1: IdealEqSpanCertificate' Table ![![-416187, 173391, -756127, 340218, 862776]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![214, 548, 1, 0, 0], ![255, 133, 0, 1, 0], ![278, 366, 0, 0, 1]] where
  M :=![![![-416187, 173391, -756127, 340218, 862776], ![182340, -75969, 331269, -149077, -378036], ![-79882, 33263, -145164, 65176, 165378], ![35026, -14706, 63413, -29440, -74034], ![-32992, 13775, -59882, 27181, 68765]]]
  hmulB := by decide  
  f := ![![![-7619, -30146, -39297, 18389, 44172]], ![![7394, 10770, -19151, 8284, 21414]], ![![4356, -958, -33914, 15203, 38010]], ![![-1727, -11233, -22543, 10388, 25314]], ![![1056, -7973, -32210, 14627, 36131]]]
  g := ![![![-296611, 96061, -756127, 340218, 862776], ![129981, -42052, 331269, -149077, -378036], ![-56750, 18647, -145164, 65176, 165378], ![26128, -6738, 63413, -29440, -74034], ![-23817, 7264, -59882, 27181, 68765]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P1 : CertificateIrreducibleZModOfList' 557 2 2 9 [290, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [486, 556], [0, 1]]
 g := ![![[321, 436], [17], [464, 203], [33, 119], [425], [212, 273], [143], [28], [1]], ![[0, 121], [17], [533, 354], [496, 438], [425], [324, 284], [143], [28], [1]]]
 h' := ![![[486, 556], [253, 184], [234, 266], [456, 260], [501, 531], [347, 216], [488, 80], [228, 202], [267, 486], [0, 1]], ![[0, 1], [0, 373], [286, 291], [377, 297], [119, 26], [50, 341], [378, 477], [368, 355], [295, 71], [486, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [530, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N1 : CertifiedPrimeIdeal' SI557N1 557 where
  n := 2
  hpos := by decide
  P := [290, 71, 1]
  hirr := P557P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33562, -11330, 19420, 116344, 442092]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281434, -337402, 19420, 116344, 442092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N1 : Ideal.IsPrime I557N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N1 B_one_repr
lemma NI557N1 : Nat.card (O ⧸ I557N1) = 310249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N1
def MulI557N0 : IdealMulLeCertificate' Table 
  ![![-7619, -30146, -39297, 18389, 44172]] ![![-416187, 173391, -756127, 340218, 862776]]
  ![![557, 0, 0, 0, 0]] where
 M := ![![![557, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC557 : ContainsPrimesAboveP 557 ![I557N0, I557N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI557N0
    exact isPrimeI557N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 557 (by decide) (𝕀 ⊙ MulI557N0)
instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-273905, 114114, -497629, 223909, 567820]] i)))

def SI563N0: IdealEqSpanCertificate' Table ![![-273905, 114114, -497629, 223909, 567820]] 
 ![![563, 0, 0, 0, 0], ![0, 563, 0, 0, 0], ![442, 462, 1, 0, 0], ![165, 375, 0, 1, 0], ![553, 292, 0, 0, 1]] where
  M :=![![![-273905, 114114, -497629, 223909, 567820], ![120002, -49996, 218021, -98096, -248762], ![-52570, 21906, -95522, 42961, 108922], ![23000, -9609, 41867, -18717, -47312], ![-21690, 9051, -39450, 17685, 44765]]]
  hmulB := by decide  
  f := ![![![-691, -381, 3715, -1624, -4108]], ![![-860, -2315, -1145, 755, 1628]], ![![-1248, -2199, 1974, -652, -1882]], ![![-775, -1650, 329, 39, -98]], ![![-1125, -1576, 3055, -1207, -3197]]]
  g := ![![![-233164, -35081, -497629, 223909, 567820], ![102142, 15362, 218021, -98096, -248762], ![-44679, -6683, -95522, 42961, 108922], ![19129, 2632, 41867, -18717, -47312], ![-18220, -2608, -39450, 17685, 44765]]]
  hle1 := by decide   
  hle2 := by decide  


def P563P0 : CertificateIrreducibleZModOfList' 563 2 2 9 [436, 259, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [304, 562], [0, 1]]
 g := ![![[459, 236], [108, 67], [82], [432], [179, 59], [304, 308], [161], [84], [1]], ![[139, 327], [208, 496], [82], [432], [99, 504], [478, 255], [161], [84], [1]]]
 h' := ![![[304, 562], [204, 133], [78, 462], [19, 334], [213, 237], [324, 215], [475, 172], [336, 286], [127, 304], [0, 1]], ![[0, 1], [100, 430], [339, 101], [215, 229], [197, 326], [376, 348], [404, 391], [15, 277], [211, 259], [304, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [457, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N0 : CertifiedPrimeIdeal' SI563N0 563 where
  n := 2
  hpos := by decide
  P := [436, 259, 1]
  hirr := P563P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17218, 20359, 41346, 200115, 444982]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-528217, -397974, 41346, 200115, 444982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI563N0 : Ideal.IsPrime I563N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI563N0 B_one_repr
lemma NI563N0 : Nat.card (O ⧸ I563N0) = 316969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI563N0

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 85, -243, -312, -1326]] i)))

def SI563N1: IdealEqSpanCertificate' Table ![![21, 85, -243, -312, -1326]] 
 ![![563, 0, 0, 0, 0], ![345, 1, 0, 0, 0], ![331, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![552, 0, 0, 0, 1]] where
  M :=![![![21, 85, -243, -312, -1326], ![-702, -291, 475, 2409, 9438], ![4620, 1707, -2502, -15200, -59268], ![-28868, -10580, 15375, 94706, 369156], ![15652, 5739, -8344, -51357, -200189]]]
  hmulB := by decide  
  f := ![![![-10097, -21684, 4457, -1327, -4722]], ![![-6191, -13308, 2694, -795, -2850]], ![![-5929, -12734, 2611, -770, -2754]], ![![-1684, -3603, 767, -191, -738]], ![![-9902, -21269, 4364, -1309, -4643]]]
  g := ![![![1443, 85, -243, -312, -1326], ![-9758, -291, 475, 2409, 9438], ![61081, 1707, -2502, -15200, -59268], ![-380363, -10580, 15375, 94706, 369156], ![206269, 5739, -8344, -51357, -200189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N1 : Nat.card (O ⧸ I563N1) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N1)

lemma isPrimeI563N1 : Ideal.IsPrime I563N1 := prime_ideal_of_norm_prime hp563.out _ NI563N1

def I563N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -32, -78, 36, 88]] i)))

def SI563N2: IdealEqSpanCertificate' Table ![![-3, -32, -78, 36, 88]] 
 ![![563, 0, 0, 0, 0], ![360, 1, 0, 0, 0], ![453, 0, 1, 0, 0], ![190, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![-3, -32, -78, 36, 88], ![16, 33, -12, 6, 16], ![4, 22, 35, -6, -20], ![-8, -2, 24, 53, 88], ![2, -2, -14, -10, -13]]]
  hmulB := by decide  
  f := ![![![-77225, 32188, -140314, 63136, 160112]], ![![-49320, 20557, -89612, 40322, 102256]], ![![-62163, 25910, -112947, 50822, 128884]], ![![-26050, 10858, -47332, 21297, 54008]], ![![-12356, 5150, -22450, 10102, 25619]]]
  g := ![![![57, -32, -78, 36, 88], ![-16, 33, -12, 6, 16], ![-37, 22, 35, -6, -20], ![-50, -2, 24, 53, 88], ![18, -2, -14, -10, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N2 : Nat.card (O ⧸ I563N2) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N2)

lemma isPrimeI563N2 : Ideal.IsPrime I563N2 := prime_ideal_of_norm_prime hp563.out _ NI563N2

def I563N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-893, -2558, -1576, 756, 1746]] i)))

def SI563N3: IdealEqSpanCertificate' Table ![![-893, -2558, -1576, 756, 1746]] 
 ![![563, 0, 0, 0, 0], ![522, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![328, 0, 0, 1, 0], ![228, 0, 0, 0, 1]] where
  M :=![![![-893, -2558, -1576, 756, 1746], ![234, -137, -2036, 800, 2070], ![470, 1034, 193, -856, -1590], ![122, -386, 56, -4819, -8922], ![-114, -148, -204, 1354, 2551]]]
  hmulB := by decide  
  f := ![![![218729, -74214, 346648, -232000, -684834]], ![![202408, -68833, 321252, -214196, -631590]], ![![4662, -538, 4257, -8228, -28878]], ![![118146, -46614, 206824, -104783, -280602]], ![![93626, -28228, 137764, -110438, -341561]]]
  g := ![![![1245, -2558, -1576, 756, 1746], ![-1148, -137, -2036, 800, 2070], ![182, 1034, 193, -856, -1590], ![6778, -386, 56, -4819, -8922], ![-1682, -148, -204, 1354, 2551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N3 : Nat.card (O ⧸ I563N3) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N3)

lemma isPrimeI563N3 : Ideal.IsPrime I563N3 := prime_ideal_of_norm_prime hp563.out _ NI563N3
def MulI563N0 : IdealMulLeCertificate' Table 
  ![![-273905, 114114, -497629, 223909, 567820]] ![![21, 85, -243, -312, -1326]]
  ![![38807615, -16180042, 70541618, -31686200, -80285642]] where
 M := ![![![38807615, -16180042, 70541618, -31686200, -80285642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI563N1 : IdealMulLeCertificate' Table 
  ![![38807615, -16180042, 70541618, -31686200, -80285642]] ![![-3, -32, -78, 36, 88]]
  ![![-218729, 74214, -346648, 232000, 684834]] where
 M := ![![![-218729, 74214, -346648, 232000, 684834]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI563N2 : IdealMulLeCertificate' Table 
  ![![-218729, 74214, -346648, 232000, 684834]] ![![-893, -2558, -1576, 756, 1746]]
  ![![563, 0, 0, 0, 0]] where
 M := ![![![-563, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC563 : ContainsPrimesAboveP 563 ![I563N0, I563N1, I563N2, I563N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI563N0
    exact isPrimeI563N1
    exact isPrimeI563N2
    exact isPrimeI563N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 563 (by decide) (𝕀 ⊙ MulI563N0 ⊙ MulI563N1 ⊙ MulI563N2)
instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22983, -9454, 41793, -18805, -47682]] i)))

def SI569N0: IdealEqSpanCertificate' Table ![![22983, -9454, 41793, -18805, -47682]] 
 ![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![0, 0, 569, 0, 0], ![562, 249, 143, 1, 0], ![135, 108, 247, 0, 1]] where
  M :=![![![22983, -9454, 41793, -18805, -47682], ![-10072, 4178, -18187, 8200, 20784], ![4384, -1872, 7994, -3491, -8928], ![-1946, 893, -3417, 2215, 5154], ![1826, -771, 3292, -1659, -4085]]]
  hmulB := by decide  
  f := ![![![-305, -119, 155, 994, 3870]], ![![1882, 689, -1007, -6167, -24042]], ![![-11708, -4285, 6230, 38406, 149700]], ![![-2292, -846, 1210, 7515, 29286]], ![![-4867, -1783, 2587, 15965, 62227]]]
  g := ![![![29927, 17263, 25498, -18805, -47682], ![-13048, -7526, -11115, 8200, 20784], ![5574, 3219, 4767, -3491, -8928], ![-3414, -1946, -2800, 2215, 5154], ![2611, 1500, 2196, -1659, -4085]]]
  hle1 := by decide   
  hle2 := by decide  


def P569P0 : CertificateIrreducibleZModOfList' 569 3 2 9 [16, 541, 215, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 349, 505], [337, 219, 64], [0, 1]]
 g := ![![[319, 421, 276], [198, 134], [105, 287], [203, 214, 268], [295, 389, 471], [227, 205, 338], [419, 153], [354, 1], []], ![[84, 227, 199, 418], [305, 430], [214, 104], [384, 551, 547, 562], [534, 293, 222, 40], [5, 560, 302, 82], [520, 484], [393, 165], [451, 113]], ![[398, 332, 19, 214], [45, 215], [362, 196], [153, 456, 278, 450], [491, 436, 353, 13], [413, 143, 15, 18], [488, 456], [314, 35], [323, 113]]]
 h' := ![![[17, 349, 505], [286, 468, 214], [271, 509, 479], [166, 327, 359], [401, 57, 118], [351, 106, 195], [231, 396, 337], [26, 223, 164], [0, 0, 1], [0, 1]], ![[337, 219, 64], [143, 125, 413], [195, 514, 62], [341, 500, 224], [499, 350, 3], [487, 373, 74], [343, 35, 94], [99, 256, 22], [470, 495, 219], [17, 349, 505]], ![[0, 1], [73, 545, 511], [519, 115, 28], [321, 311, 555], [462, 162, 448], [71, 90, 300], [167, 138, 138], [566, 90, 383], [291, 74, 349], [337, 219, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 192], []]
 b := ![[], [192, 13, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N0 : CertifiedPrimeIdeal' SI569N0 569 where
  n := 3
  hpos := by decide
  P := [16, 541, 215, 1]
  hirr := P569P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3934816, -14595028, -21250878, -101683511, -186745295]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![144746367, 79917559, 106582740, -101683511, -186745295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI569N0 : Ideal.IsPrime I569N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI569N0 B_one_repr
lemma NI569N0 : Nat.card (O ⧸ I569N0) = 184220009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI569N0

def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![305, 119, -155, -994, -3870]] i)))

def SI569N1: IdealEqSpanCertificate' Table ![![305, 119, -155, -994, -3870]] 
 ![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![245, 426, 1, 0, 0], ![326, 280, 0, 1, 0], ![19, 289, 0, 0, 1]] where
  M :=![![![305, 119, -155, -994, -3870], ![-1882, -689, 1007, 6167, 24042], ![11708, 4285, -6230, -38406, -149700], ![-72888, -26698, 38767, 239068, 931848], ![39528, 14479, -21024, -129649, -505349]]]
  hmulB := by decide  
  f := ![![![-22983, 9454, -41793, 18805, 47682]], ![![10072, -4178, 18187, -8200, -20784]], ![![-2363, 946, -4393, 1964, 4986]], ![![-8208, 3359, -14989, 6735, 17082]], ![![4345, -1805, 7836, -3534, -8957]]]
  g := ![![![766, 2571, -155, -994, -3870], ![-4773, -16001, 1007, 6167, 24042], ![29706, 99605, -6230, -38406, -149700], ![-184907, -620008, 38767, 239068, 931848], ![100277, 336236, -21024, -129649, -505349]]]
  hle1 := by decide   
  hle2 := by decide  


def P569P1 : CertificateIrreducibleZModOfList' 569 2 2 9 [306, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [487, 568], [0, 1]]
 g := ![![[242, 225], [287], [313], [337, 439], [404, 306], [435, 427], [214], [465], [1]], ![[0, 344], [287], [313], [186, 130], [348, 263], [130, 142], [214], [465], [1]]]
 h' := ![![[487, 568], [92, 15], [433, 359], [436, 238], [418, 281], [36, 38], [398, 284], [280, 105], [263, 487], [0, 1]], ![[0, 1], [0, 554], [14, 210], [266, 331], [136, 288], [334, 531], [439, 285], [205, 464], [159, 82], [487, 568]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [246, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N1 : CertifiedPrimeIdeal' SI569N1 569 where
  n := 2
  hpos := by decide
  P := [306, 82, 1]
  hirr := P569P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14981, -611, 14633, 77063, 237390]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58406, -169451, 14633, 77063, 237390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI569N1 : Ideal.IsPrime I569N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI569N1 B_one_repr
lemma NI569N1 : Nat.card (O ⧸ I569N1) = 323761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI569N1
def MulI569N0 : IdealMulLeCertificate' Table 
  ![![22983, -9454, 41793, -18805, -47682]] ![![305, 119, -155, -994, -3870]]
  ![![569, 0, 0, 0, 0]] where
 M := ![![![-569, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC569 : ContainsPrimesAboveP 569 ![I569N0, I569N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI569N0
    exact isPrimeI569N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 569 (by decide) (𝕀 ⊙ MulI569N0)
instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-387, -100, 80, 1138, 4376]] i)))

def SI571N0: IdealEqSpanCertificate' Table ![![-387, -100, 80, 1138, 4376]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![444, 245, 1, 0, 0], ![281, 374, 0, 1, 0], ![428, 416, 0, 0, 1]] where
  M :=![![![-387, -100, 80, 1138, 4376], ![2100, 751, -1062, -6830, -26596], ![-12936, -4730, 6857, 42404, 165272], ![80464, 29468, -42790, -263907, -1028656], ![-43638, -15980, 23202, 143120, 557851]]]
  hmulB := by decide  
  f := ![![![1111, 2036, -1628, 658, 1784]], ![![468, 1769, 2226, -1146, -2692]], ![![1064, 2341, -309, 18, 228]], ![![853, 2158, 654, -433, -896]], ![![1174, 2816, 402, -340, -621]]]
  g := ![![![-3903, -3968, 80, 1138, 4376], ![24126, 24307, -1062, -6830, -26596], ![-150104, -151133, 6857, 42404, 165272], ![934329, 940692, -42790, -263907, -1028656], ![-506694, -510146, 23202, 143120, 557851]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P0 : CertificateIrreducibleZModOfList' 571 2 2 9 [516, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [556, 570], [0, 1]]
 g := ![![[415, 508], [434, 149], [521], [541, 324], [508, 119], [362, 244], [434], [225], [1]], ![[218, 63], [483, 422], [521], [249, 247], [436, 452], [128, 327], [434], [225], [1]]]
 h' := ![![[556, 570], [459, 191], [77, 288], [63, 377], [532, 553], [496, 491], [177, 463], [554, 114], [55, 556], [0, 1]], ![[0, 1], [449, 380], [325, 283], [118, 194], [231, 18], [554, 80], [84, 108], [557, 457], [280, 15], [556, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [281]]
 b := ![[], [340, 426]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N0 : CertifiedPrimeIdeal' SI571N0 571 where
  n := 2
  hpos := by decide
  P := [516, 15, 1]
  hirr := P571P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51486, 31945, 88556, 452839, 1098698]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1115343, -1134999, 88556, 452839, 1098698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N0 : Ideal.IsPrime I571N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N0 B_one_repr
lemma NI571N0 : Nat.card (O ⧸ I571N0) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N0

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, -296, 113, -43, -126]] i)))

def SI571N1: IdealEqSpanCertificate' Table ![![-145, -296, 113, -43, -126]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![62, 288, 1, 0, 0], ![416, 484, 0, 1, 0], ![445, 458, 0, 0, 1]] where
  M :=![![![-145, -296, 113, -43, -126], ![-40, -188, -299, 138, 336], ![60, 98, -110, 31, 84], ![22, 91, 107, -87, -126], ![-18, -55, -24, 13, -5]]]
  hmulB := by decide  
  f := ![![![126197, -52575, 229277, -103164, -261618]], ![![-55290, 23033, -100449, 45197, 114618]], ![![-14142, 5891, -25692, 11560, 29316]], ![![45056, -18772, 81861, -36834, -93408]], ![![54019, -22506, 98145, -44161, -111989]]]
  g := ![![![117, 80, 113, -43, -126], ![-330, -236, -299, 138, 336], ![-76, -38, -110, 31, 84], ![150, 121, 107, -87, -126], ![-3, 5, -24, 13, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P1 : CertificateIrreducibleZModOfList' 571 2 2 9 [88, 532, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 570], [0, 1]]
 g := ![![[32, 271], [135, 116], [564], [506, 331], [558, 123], [32, 155], [219], [379], [1]], ![[323, 300], [91, 455], [564], [282, 240], [216, 448], [367, 416], [219], [379], [1]]]
 h' := ![![[39, 570], [111, 94], [145, 357], [10, 317], [2, 468], [39, 319], [288, 282], [87, 494], [483, 39], [0, 1]], ![[0, 1], [351, 477], [364, 214], [382, 254], [553, 103], [489, 252], [437, 289], [510, 77], [291, 532], [39, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [509, 296]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N1 : CertifiedPrimeIdeal' SI571N1 571 where
  n := 2
  hpos := by decide
  P := [88, 532, 1]
  hirr := P571P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14458, 15203, 31386, 157983, 355530]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-395608, -434887, 31386, 157983, 355530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N1 : Ideal.IsPrime I571N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N1 B_one_repr
lemma NI571N1 : Nat.card (O ⧸ I571N1) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N1

def I571N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -64, 2, 252, 956]] i)))

def SI571N2: IdealEqSpanCertificate' Table ![![-83, -64, 2, 252, 956]] 
 ![![571, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![269, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![192, 0, 0, 0, 1]] where
  M :=![![![-83, -64, 2, 252, 956], ![452, 169, -264, -1450, -5668], ![-2768, -998, 1487, 9094, 35456], ![17268, 6326, -9172, -56651, -220804], ![-9366, -3434, 4974, 30722, 119743]]]
  hmulB := by decide  
  f := ![![![28273391, -11779204, 51366934, -23112696, -58612492]], ![![1859898, -774867, 3379052, -1520414, -3855684]], ![![13329193, -5553182, 24216401, -10896238, -27632244]], ![![2768708, -1153494, 5030172, -2263343, -5739708]], ![![9510914, -3962418, 17279374, -7774902, -19716713]]]
  g := ![![![-343, -64, 2, 252, 956], ![2162, 169, -264, -1450, -5668], ![-13453, -998, 1487, 9094, 35456], ![83732, 6326, -9172, -56651, -220804], ![-45408, -3434, 4974, 30722, 119743]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI571N2 : Nat.card (O ⧸ I571N2) = 571 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI571N2)

lemma isPrimeI571N2 : Ideal.IsPrime I571N2 := prime_ideal_of_norm_prime hp571.out _ NI571N2
def MulI571N0 : IdealMulLeCertificate' Table 
  ![![-387, -100, 80, 1138, 4376]] ![![-145, -296, 113, -43, -126]]
  ![![11183, 4070, -5889, -36797, -143386]] where
 M := ![![![11183, 4070, -5889, -36797, -143386]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI571N1 : IdealMulLeCertificate' Table 
  ![![11183, 4070, -5889, -36797, -143386]] ![![-83, -64, 2, 252, 956]]
  ![![571, 0, 0, 0, 0]] where
 M := ![![![724754883, 265459042, -385508937, -2377155795, -9265723206]]]
 hmul := by decide  
 g := ![![![![1269273, 464902, -675147, -4163145, -16227186]]]]
 hle2 := by decide  


def PBC571 : ContainsPrimesAboveP 571 ![I571N0, I571N1, I571N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI571N0
    exact isPrimeI571N1
    exact isPrimeI571N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 571 (by decide) (𝕀 ⊙ MulI571N0 ⊙ MulI571N1)
instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -8, -34, 18, 42]] i)))

def SI577N0: IdealEqSpanCertificate' Table ![![7, -8, -34, 18, 42]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![0, 0, 577, 0, 0], ![288, 305, 19, 1, 0], ![440, 556, 46, 0, 1]] where
  M :=![![![7, -8, -34, 18, 42], ![6, 25, 4, 20, 42], ![2, 26, 43, 92, 126], ![-58, 94, 176, 851, 1722], ![24, -22, -54, -248, -551]]]
  hmulB := by decide  
  f := ![![![79, -12, 110, -50, -126]], ![![-26, 29, -36, 16, 42]], ![![10, -10, 35, -16, -42]], ![![26, 9, 37, -17, -42]], ![![36, 18, 52, -24, -59]]]
  g := ![![![-41, -50, -4, 18, 42], ![-42, -51, -4, 20, 42], ![-142, -170, -13, 92, 126], ![-1738, -2109, -165, 851, 1722], ![544, 662, 52, -248, -551]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P0 : CertificateIrreducibleZModOfList' 577 3 2 9 [194, 449, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [553, 529, 142], [514, 47, 435], [0, 1]]
 g := ![![[476, 110, 99], [375, 469], [186, 352], [403, 527], [399, 163], [285, 243], [112, 178, 334], [490, 1], []], ![[162, 68, 452, 335], [150, 107], [326, 539], [419, 18], [288, 576], [521, 68], [287, 509, 29, 415], [520, 478], [28, 546]], ![[541, 75, 444, 287], [71, 191], [226, 142], [8, 254], [309, 566], [95, 44], [163, 569, 284, 144], [480, 573], [312, 546]]]
 h' := ![![[553, 529, 142], [480, 265, 551], [168, 206, 254], [47, 414, 217], [196, 407, 536], [70, 272, 345], [198, 252, 489], [145, 210, 196], [0, 0, 1], [0, 1]], ![[514, 47, 435], [360, 371, 57], [42, 126, 223], [347, 405, 324], [268, 242, 475], [177, 473, 24], [268, 477, 490], [572, 287, 373], [337, 362, 47], [553, 529, 142]], ![[0, 1], [279, 518, 546], [44, 245, 100], [571, 335, 36], [476, 505, 143], [375, 409, 208], [468, 425, 175], [523, 80, 8], [564, 215, 529], [514, 47, 435]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [532, 96], []]
 b := ![[], [93, 177, 235], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N0 : CertifiedPrimeIdeal' SI577N0 577 where
  n := 3
  hpos := by decide
  P := [194, 449, 87, 1]
  hirr := P577P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-616477933, 699000620, 1432790328, 7142067100, 15750503580]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15576695629, -18951319680, -1488370276, 7142067100, 15750503580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N0 : Ideal.IsPrime I577N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N0 B_one_repr
lemma NI577N0 : Nat.card (O ⧸ I577N0) = 192100033 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N0

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130057, -54184, 236285, -106317, -269614]] i)))

def SI577N1: IdealEqSpanCertificate' Table ![![130057, -54184, 236285, -106317, -269614]] 
 ![![577, 0, 0, 0, 0], ![216, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![391, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![130057, -54184, 236285, -106317, -269614], ![-56980, 23740, -103521, 46580, 118124], ![24964, -10400, 45356, -20405, -51748], ![-10938, 4559, -19867, 8959, 22706], ![10308, -4295, 18726, -8431, -21377]]]
  hmulB := by decide  
  f := ![![![2309, 1043, -1757, -6606, -26122]], ![![842, 383, -645, -2399, -9490]], ![![465, 198, -321, -1390, -5470]], ![![687, 385, -724, -1598, -6482]], ![![548, 207, -308, -1767, -6899]]]
  g := ![![![67795, -54184, 236285, -106317, -269614], ![-29703, 23740, -103521, 46580, 118124], ![13011, -10400, 45356, -20405, -51748], ![-5716, 4559, -19867, 8959, 22706], ![5377, -4295, 18726, -8431, -21377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI577N1 : Nat.card (O ⧸ I577N1) = 577 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI577N1)

lemma isPrimeI577N1 : Ideal.IsPrime I577N1 := prime_ideal_of_norm_prime hp577.out _ NI577N1

def I577N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -13, 1, -68, -260]] i)))

def SI577N2: IdealEqSpanCertificate' Table ![![9, -13, 1, -68, -260]] 
 ![![577, 0, 0, 0, 0], ![342, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![425, 0, 0, 0, 1]] where
  M :=![![![9, -13, 1, -68, -260], ![-124, -59, 43, 405, 1564], ![754, 281, -408, -2456, -9578], ![-4666, -1702, 2491, 15308, 59674], ![2530, 923, -1348, -8303, -32365]]]
  hmulB := by decide  
  f := ![![![-753515, 313936, -1368945, 615929, 1561984]], ![![-446052, 185838, -810363, 364606, 924634]], ![![-218339, 90966, -396667, 178470, 452598]], ![![-11643, 4849, -21156, 9504, 24112]], ![![-555119, 231279, -1008509, 453762, 1150729]]]
  g := ![![![200, -13, 1, -68, -260], ![-1136, -59, 43, 405, 1564], ![7046, 281, -408, -2456, -9578], ![-43913, -1702, 2491, 15308, 59674], ![23816, 923, -1348, -8303, -32365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI577N2 : Nat.card (O ⧸ I577N2) = 577 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI577N2)

lemma isPrimeI577N2 : Ideal.IsPrime I577N2 := prime_ideal_of_norm_prime hp577.out _ NI577N2
def MulI577N0 : IdealMulLeCertificate' Table 
  ![![7, -8, -34, 18, 42]] ![![130057, -54184, 236285, -106317, -269614]]
  ![![753515, -313936, 1368945, -615929, -1561984]] where
 M := ![![![753515, -313936, 1368945, -615929, -1561984]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI577N1 : IdealMulLeCertificate' Table 
  ![![753515, -313936, 1368945, -615929, -1561984]] ![![9, -13, 1, -68, -260]]
  ![![577, 0, 0, 0, 0]] where
 M := ![![![-577, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC577 : ContainsPrimesAboveP 577 ![I577N0, I577N1, I577N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI577N0
    exact isPrimeI577N1
    exact isPrimeI577N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 577 (by decide) (𝕀 ⊙ MulI577N0 ⊙ MulI577N1)
instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![672629, -280190, 1221904, -549990, -1394972]] i)))

def SI587N0: IdealEqSpanCertificate' Table ![![672629, -280190, 1221904, -549990, -1394972]] 
 ![![587, 0, 0, 0, 0], ![0, 587, 0, 0, 0], ![0, 0, 587, 0, 0], ![0, 0, 0, 587, 0], ![138, 152, 475, 106, 1]] where
  M :=![![![672629, -280190, 1221904, -549990, -1394972], ![-294992, 122639, -535188, 241906, 614944], ![131132, -53086, 233413, -112450, -293996], ![-69096, 18682, -96440, 85739, 275032], ![60120, -19636, 93312, -65504, -196975]]]
  hmulB := by decide  
  f := ![![![4655, 7058, -11192, 4818, 12500]], ![![2864, 9473, 9012, -4286, -10144]], ![![-1572, -1422, 6759, -2986, -7564]], ![![-1592, -4558, -2816, 1381, 3176]], ![![278, 2142, 4663, -2144, -5235]]]
  g := ![![![329095, 360742, 1130892, 250966, -1394972], ![-145072, -159027, -498524, -110634, 614944], ![69340, 76038, 238299, 52898, -293996], ![-64776, -71186, -222720, -49519, 275032], ![46410, 50972, 159551, 35458, -196975]]]
  hle1 := by decide   
  hle2 := by decide  


def P587P0 : CertificateIrreducibleZModOfList' 587 4 2 9 [263, 526, 218, 239, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [509, 547, 569, 131], [53, 491, 436, 153], [373, 135, 169, 303], [0, 1]]
 g := ![![[315, 32, 298, 29], [560, 109, 16, 292], [232, 236, 209], [228, 286, 566, 152], [403, 99, 114], [84, 468, 525], [127, 554, 245, 182], [1], []], ![[95, 562, 316, 77, 138, 466], [416, 32, 456, 365, 89, 450], [373, 141, 122], [580, 364, 405, 300, 44, 559], [483, 221, 324], [381, 88, 352], [301, 101, 550, 284], [572, 130, 493], [222, 457, 138]], ![[233, 42, 104, 294, 340, 51], [394, 440, 194, 102, 315, 451], [496, 329, 477], [69, 53, 88, 383, 285, 553], [482, 157, 501], [237, 362, 88], [440, 529, 488, 214, 582, 510], [3, 168, 217], [93, 113, 516]], ![[167, 212, 427, 123, 347, 87], [584, 543, 552, 396, 402, 16], [494, 516, 199], [371, 167, 402, 436, 405, 47], [30, 445, 448], [548, 475, 175], [515, 172, 585, 42, 564, 328], [330, 104, 124], [68, 572, 237]]]
 h' := ![![[509, 547, 569, 131], [57, 562, 48, 326], [501, 386, 26, 349], [497, 273, 338, 122], [459, 268, 582, 537], [56, 529, 444, 124], [58, 480, 572, 87], [324, 61, 369, 348], [0, 0, 1], [0, 1]], ![[53, 491, 436, 153], [220, 388, 358, 490], [129, 8, 228, 165], [526, 354, 123, 551], [458, 210, 465, 197], [252, 27, 282, 18], [527, 343, 425, 501], [382, 369, 297], [528, 555, 425, 511], [509, 547, 569, 131]], ![[373, 135, 169, 303], [577, 140, 73, 14], [344, 281, 441, 449], [171, 107, 266, 440], [455, 265, 86, 69], [58, 459, 422, 398], [298, 479, 44, 43], [450, 390, 422, 526], [69, 411, 263, 475], [53, 491, 436, 153]], ![[0, 1], [430, 84, 108, 344], [574, 499, 479, 211], [348, 440, 447, 61], [229, 431, 41, 371], [515, 159, 26, 47], [284, 459, 133, 543], [516, 354, 86, 300], [323, 208, 485, 188], [373, 135, 169, 303]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [273, 480, 316], []]
 b := ![[], [], [506, 121, 178, 466], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N0 : CertifiedPrimeIdeal' SI587N0 587 where
  n := 4
  hpos := by decide
  P := [263, 526, 218, 239, 1]
  hirr := P587P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5503103191, 10547372088, 17936715960, 87603329310, 177251966190]
  a := ![-2, 3, -1, 18, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41680194953, -45880326216, -143401613670, -31858782090, 177251966190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI587N0 : Ideal.IsPrime I587N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI587N0 B_one_repr
lemma NI587N0 : Nat.card (O ⧸ I587N0) = 118727795761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI587N0

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4655, 7058, -11192, 4818, 12500]] i)))

def SI587N1: IdealEqSpanCertificate' Table ![![4655, 7058, -11192, 4818, 12500]] 
 ![![587, 0, 0, 0, 0], ![261, 1, 0, 0, 0], ![558, 0, 1, 0, 0], ![525, 0, 0, 1, 0], ![518, 0, 0, 0, 1]] where
  M :=![![![4655, 7058, -11192, 4818, 12500], ![2864, 9473, 9012, -4286, -10144], ![-1572, -1422, 6759, -2986, -7564], ![-1592, -4558, -2816, 1381, 3176], ![920, 2052, -176, 24, 187]]]
  hmulB := by decide  
  f := ![![![672629, -280190, 1221904, -549990, -1394972]], ![![298571, -124373, 542388, -244132, -619204]], ![![639622, -266438, 1161935, -523010, -1326556]], ![![601467, -250564, 1092680, -491753, -1247164]], ![![593666, -247288, 1078432, -485452, -1231333]]]
  g := ![![![-7831, 7058, -11192, 4818, 12500], ![11, 9473, 9012, -4286, -10144], ![3550, -1422, 6759, -2986, -7564], ![663, -4558, -2816, 1381, 3176], ![-930, 2052, -176, 24, 187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI587N1 : Nat.card (O ⧸ I587N1) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI587N1)

lemma isPrimeI587N1 : Ideal.IsPrime I587N1 := prime_ideal_of_norm_prime hp587.out _ NI587N1
def MulI587N0 : IdealMulLeCertificate' Table 
  ![![672629, -280190, 1221904, -549990, -1394972]] ![![4655, 7058, -11192, 4818, 12500]]
  ![![587, 0, 0, 0, 0]] where
 M := ![![![587, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC587 : ContainsPrimesAboveP 587 ![I587N0, I587N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI587N0
    exact isPrimeI587N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 587 (by decide) (𝕀 ⊙ MulI587N0)
instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108821, -445351, -607090, 283553, 682342]] i)))

def SI593N0: IdealEqSpanCertificate' Table ![![-108821, -445351, -607090, 283553, 682342]] 
 ![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![565, 121, 76, 504, 1]] where
  M :=![![![-108821, -445351, -607090, 283553, 682342], ![115236, 174732, -277034, 119259, 309412], ![70894, 234495, 223097, -106103, -251126], ![-38920, -35209, 167312, -73898, -187184], ![1826, -30552, -107630, 48966, 120695]]]
  hmulB := by decide  
  f := ![![![-3821, 1593, -6940, 3131, 7934]], ![![1672, -690, 3052, -1317, -3376]], ![![-742, 355, -1265, 919, 2078]], ![![240, 177, 1034, 1890, 3272]], ![![-3191, 1573, -5274, 4438, 9917]]]
  g := ![![![-650307, -139981, -88474, -579455, 682342], ![-294608, -62840, -40122, -262773, 309412], ![239388, 51637, 32561, 213257, -251126], ![178280, 38135, 24272, 158966, -187184], ![-114993, -24679, -15650, -102498, 120695]]]
  hle1 := by decide   
  hle2 := by decide  


def P593P0 : CertificateIrreducibleZModOfList' 593 4 2 9 [294, 92, 149, 284, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 117, 125, 358], [306, 285, 477, 259], [423, 190, 584, 569], [0, 1]]
 g := ![![[425, 575, 89, 464], [30, 127, 502], [220, 356, 578], [137, 213, 534], [579, 52, 397, 257], [160, 175, 484], [237, 378, 526, 8], [1], []], ![[163, 78, 268, 298, 197, 323], [456, 588, 163], [447, 297, 556], [195, 270, 515], [37, 293, 104, 411, 469, 529], [273, 245, 495], [3, 261, 161, 437, 190, 71], [152, 428, 113], [83, 314, 76]], ![[572, 65, 348, 403, 565, 442], [184, 462, 152], [232, 464, 400], [462, 311, 113], [537, 363, 363, 28, 67, 586], [435, 358, 183], [534, 37, 375, 359, 365, 536], [39, 557, 306], [543, 112, 72]], ![[578, 288, 510, 223, 515, 290], [405, 62, 215], [100, 180, 458], [264, 309, 32], [190, 348, 165, 346, 96, 497], [133, 113, 171], [271, 330, 448, 176, 553, 566], [544, 469, 168], [537, 516, 576]]]
 h' := ![![[173, 117, 125, 358], [280, 30, 468, 196], [66, 304, 481, 271], [85, 297, 583, 551], [558, 285, 464, 94], [252, 492, 291, 229], [296, 347, 147, 571], [299, 501, 444, 309], [0, 0, 1], [0, 1]], ![[306, 285, 477, 259], [570, 469, 57, 35], [156, 270, 374, 532], [374, 356, 260, 148], [556, 427, 279, 388], [351, 90, 402, 370], [253, 7, 582, 41], [307, 169, 194, 315], [190, 423, 456, 457], [173, 117, 125, 358]], ![[423, 190, 584, 569], [303, 246, 548, 112], [170, 7, 131, 162], [37, 361, 361, 20], [455, 491, 287, 136], [487, 164, 405, 589], [576, 13, 18, 37], [82, 425, 524, 372], [410, 214, 443, 256], [306, 285, 477, 259]], ![[0, 1], [438, 441, 113, 250], [329, 12, 200, 221], [353, 172, 575, 467], [62, 576, 156, 568], [427, 440, 88, 591], [503, 226, 439, 537], [26, 91, 24, 190], [296, 549, 286, 473], [423, 190, 584, 569]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [89, 372, 583], []]
 b := ![[], [], [242, 85, 32, 316], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI593N0 : CertifiedPrimeIdeal' SI593N0 593 where
  n := 4
  hpos := by decide
  P := [294, 92, 149, 284, 1]
  hirr := P593P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-360790982774, 1348576500349, 1960991037424, 9381215437597, 17211852188946]
  a := ![-5, 4, 10, 49, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16399759321648, -3509756388469, -2202596585704, -14612803183459, 17211852188946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI593N0 : Ideal.IsPrime I593N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI593N0 B_one_repr
lemma NI593N0 : Nat.card (O ⧸ I593N0) = 123657019201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI593N0

def I593N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3821, -1593, 6940, -3131, -7934]] i)))

def SI593N1: IdealEqSpanCertificate' Table ![![3821, -1593, 6940, -3131, -7934]] 
 ![![593, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![329, 0, 1, 0, 0], ![417, 0, 0, 1, 0], ![332, 0, 0, 0, 1]] where
  M :=![![![3821, -1593, 6940, -3131, -7934], ![-1672, 690, -3052, 1317, 3376], ![742, -355, 1265, -919, -2078], ![-240, -177, -1034, -1890, -3272], ![278, -46, 670, 328, 449]]]
  hmulB := by decide  
  f := ![![![108821, 445351, 607090, -283553, -682342]], ![![35957, 147655, 202148, -94400, -227202]], ![![60255, 246688, 336441, -157138, -378144]], ![![76589, 313232, 426626, -199271, -479510]], ![![60922, 249388, 340070, -158834, -382223]]]
  g := ![![![3329, -1593, 6940, -3131, -7934], ![-1355, 690, -3052, 1317, 3376], ![1227, -355, 1265, -919, -2078], ![3793, -177, -1034, -1890, -3272], ![-838, -46, 670, 328, 449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI593N1 : Nat.card (O ⧸ I593N1) = 593 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI593N1)

lemma isPrimeI593N1 : Ideal.IsPrime I593N1 := prime_ideal_of_norm_prime hp593.out _ NI593N1
def MulI593N0 : IdealMulLeCertificate' Table 
  ![![-108821, -445351, -607090, 283553, 682342]] ![![3821, -1593, 6940, -3131, -7934]]
  ![![593, 0, 0, 0, 0]] where
 M := ![![![-593, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC593 : ContainsPrimesAboveP 593 ![I593N0, I593N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI593N0
    exact isPrimeI593N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 593 (by decide) (𝕀 ⊙ MulI593N0)


lemma PB953I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)

def PB953I11 : PrimesBelowBoundCertificateInterval O 523 593 953 where
  m := 9
  g := ![3, 3, 2, 4, 2, 3, 3, 2, 2]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB953I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0, I541N1, I541N2]
    · exact ![I547N0, I547N1, I547N2]
    · exact ![I557N0, I557N1]
    · exact ![I563N0, I563N1, I563N2, I563N3]
    · exact ![I569N0, I569N1]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1, I577N2]
    · exact ![I587N0, I587N1]
    · exact ![I593N0, I593N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC541
    · exact PBC547
    · exact PBC557
    · exact PBC563
    · exact PBC569
    · exact PBC571
    · exact PBC577
    · exact PBC587
    · exact PBC593
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![292681, 292681, 541]
    · exact ![299209, 299209, 547]
    · exact ![172808693, 310249]
    · exact ![316969, 563, 563, 563]
    · exact ![184220009, 323761]
    · exact ![326041, 326041, 571]
    · exact ![192100033, 577, 577]
    · exact ![118727795761, 587]
    · exact ![123657019201, 593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
      exact NI547N2
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
      exact NI557N1
    · dsimp ; intro j
      fin_cases j
      exact NI563N0
      exact NI563N1
      exact NI563N2
      exact NI563N3
    · dsimp ; intro j
      fin_cases j
      exact NI569N0
      exact NI569N1
    · dsimp ; intro j
      fin_cases j
      exact NI571N0
      exact NI571N1
      exact NI571N2
    · dsimp ; intro j
      fin_cases j
      exact NI577N0
      exact NI577N1
      exact NI577N2
    · dsimp ; intro j
      fin_cases j
      exact NI587N0
      exact NI587N1
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
      exact NI593N1
  β := ![I541N2, I547N2, I563N1, I563N2, I563N3, I571N2, I577N1, I577N2, I587N1, I593N1]
  Il := ![[I541N2], [I547N2], [], [I563N1, I563N2, I563N3], [], [I571N2], [I577N1, I577N2], [I587N1], [I593N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
