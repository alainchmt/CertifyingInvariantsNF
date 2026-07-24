
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 269, 75, 0, -66]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![263, 269, 75, 0, -66]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![52, 297, 37, 1, 0], ![29, 142, 13, 0, 1]] where
  M :=![![![263, 269, 75, 0, -66], ![792, 866, 269, 18, -198], ![2322, 2627, 830, 88, -378], ![1740, 2611, 1091, 311, 60], ![816, 1400, 618, 208, 245]]]
  hmulB := by decide  
  f := ![![![1759, 359, -337, -106, 270]], ![![-2922, -632, 571, 184, -462]], ![![4992, 1161, -1000, -334, 822]], ![![-1912, -408, 372, 119, -300]], ![![-959, -206, 187, 60, -151]]]
  g := ![![![7, 31, 3, 0, -66], ![18, 76, 7, 18, -198], ![28, 97, 8, 88, -378], ![-52, -316, -36, 311, 60], ![-55, -306, -33, 208, 245]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [15, 301, 298, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [309, 19, 216], [15, 291, 95], [0, 1]]
 g := ![![[166, 193, 160], [266, 84, 193], [99, 290, 5], [291, 28], [19, 69, 208], [184, 222, 8], [13, 1], []], ![[230, 265, 258, 112], [167, 159, 16, 125], [38, 236, 110, 150], [164, 90], [284, 280, 123, 104], [110, 227, 45, 72], [260, 89], [200, 6]], ![[278, 92, 38, 291], [202, 91, 193, 43], [244, 46, 67, 190], [164, 24], [204, 82, 78, 174], [94, 10, 72, 58], [0, 50], [10, 6]]]
 h' := ![![[309, 19, 216], [53, 80, 99], [70, 44, 82], [43, 11, 194], [26, 54, 31], [39, 148, 72], [116, 115, 179], [0, 0, 1], [0, 1]], ![[15, 291, 95], [294, 218, 61], [0, 78, 89], [56, 221, 51], [31, 34, 159], [176, 197, 50], [77, 189, 112], [114, 279, 291], [309, 19, 216]], ![[0, 1], [281, 13, 151], [38, 189, 140], [141, 79, 66], [51, 223, 121], [195, 277, 189], [27, 7, 20], [75, 32, 19], [15, 291, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 257], []]
 b := ![[], [129, 255, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [15, 301, 298, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![179585855, 199192132, 77690780, 11369996, -115658960]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9461273, 42591240, 3731728, 11369996, -115658960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1759, 359, -337, -106, 270]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![1759, 359, -337, -106, 270]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![188, 237, 1, 0, 0], ![114, 0, 0, 1, 0], ![241, 23, 0, 0, 1]] where
  M :=![![![1759, 359, -337, -106, 270], ![-2922, -632, 571, 184, -462], ![4992, 1161, -1000, -334, 822], ![-2970, -809, 629, 231, -540], ![768, 174, -152, -52, 127]]]
  hmulB := by decide  
  f := ![![![263, 269, 75, 0, -66]], ![![792, 866, 269, 18, -198]], ![![770, 831, 253, 14, -192]], ![![102, 107, 31, 1, -24]], ![![265, 277, 80, 2, -65]]]
  g := ![![![39, 238, -337, -106, 270], ![-64, -403, 571, 184, -462], ![106, 705, -1000, -334, 822], ![-56, -442, 629, 231, -540], ![15, 107, -152, -52, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [152, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [296, 310], [0, 1]]
 g := ![![[129, 12], [16, 52], [171, 105], [139], [46, 163], [51, 60], [225], [1]], ![[260, 299], [169, 259], [151, 206], [139], [89, 148], [84, 251], [225], [1]]]
 h' := ![![[296, 310], [56, 261], [132, 36], [128, 87], [161, 254], [23, 115], [100, 252], [159, 296], [0, 1]], ![[0, 1], [184, 50], [214, 275], [67, 224], [83, 57], [164, 196], [52, 59], [73, 15], [296, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [65, 216]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [152, 15, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12125179, -11443083, -3328685, 182833, 6631455]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3232656, 2009427, -3328685, 182833, 6631455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![263, 269, 75, 0, -66]] ![![1759, 359, -337, -106, 270]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 34, -10, -8, 10]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![57, 34, -10, -8, 10]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![62, 230, 244, 1, 0], ![24, 250, 69, 0, 1]] where
  M :=![![![57, 34, -10, -8, 10], ![-96, -25, 50, 24, -66], ![720, 458, -73, -104, 90], ![-336, 28, 308, 161, -456], ![458, 378, 42, -42, -55]]]
  hmulB := by decide  
  f := ![![![-91, -14, 14, 4, -10]], ![![108, -1, -22, -4, 18]], ![![-204, -54, 7, 4, 6]], ![![-98, -46, -8, 1, 16]], ![![34, -14, -15, -2, 15]]]
  g := ![![![1, -2, 4, -8, 10], ![0, 35, -4, 24, -66], ![16, 6, 61, -104, 90], ![2, 246, -24, 161, -456], ![14, 76, 45, -42, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [31, 187, 307, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 14, 302], [228, 298, 11], [0, 1]]
 g := ![![[199, 215, 309], [58, 304], [299, 50], [225, 68, 48], [193, 72, 173], [253, 175, 265], [6, 1], []], ![[262, 135, 199, 115], [91, 307], [167, 104], [145, 214, 101, 39], [115, 128, 27, 39], [130, 251, 245, 3], [177, 225], [105, 121]], ![[69, 31, 176, 99], [128, 275], [285, 230], [206, 235, 82, 1], [158, 142, 203, 312], [99, 149, 75, 289], [269, 196], [83, 121]]]
 h' := ![![[91, 14, 302], [219, 306, 50], [217, 258, 238], [224, 307, 287], [277, 187, 294], [295, 14, 122], [127, 99, 162], [0, 0, 1], [0, 1]], ![[228, 298, 11], [169, 292, 266], [122, 210, 165], [149, 214, 143], [50, 91, 106], [9, 146, 207], [158, 83, 237], [18, 133, 298], [91, 14, 302]], ![[0, 1], [229, 28, 310], [292, 158, 223], [287, 105, 196], [223, 35, 226], [119, 153, 297], [83, 131, 227], [270, 180, 14], [228, 298, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [247, 137], []]
 b := ![[], [136, 128, 297], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [31, 187, 307, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52154854, 51471785, 14453323, -573775, -19803666]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1798776, 16403695, 4859129, -573775, -19803666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1082, 189, -197, -59, 155]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![1082, 189, -197, -59, 155]] 
 ![![313, 0, 0, 0, 0], ![218, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![1082, 189, -197, -59, 155], ![-1683, -296, 307, 93, -243], ![2637, 475, -482, -151, 387], ![-1254, -247, 235, 85, -204], ![439, 84, -80, -27, 66]]]
  hmulB := by decide  
  f := ![![![582, -9, -341, -83, 343]], ![![393, -14, -237, -57, 239]], ![![93, -15, -66, -15, 67]], ![![264, -47, -191, -43, 194]], ![![329, -29, -213, -50, 215]]]
  g := ![![![-157, 189, -197, -59, 155], ![246, -296, 307, 93, -243], ![-394, 475, -482, -151, 387], ![206, -247, 235, 85, -204], ![-69, 84, -80, -27, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, -11, 9, 3, -9]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![-32, -11, 9, 3, -9]] 
 ![![313, 0, 0, 0, 0], ![233, 1, 0, 0, 0], ![173, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![299, 0, 0, 0, 1]] where
  M :=![![![-32, -11, 9, 3, -9], ![99, 46, -17, -9, 9], ![-81, 19, 64, 11, -81], ![420, 287, 7, -29, -60], ![159, 154, 42, -7, -74]]]
  hmulB := by decide  
  f := ![![![-7496, -1225, 1349, 359, -1005]], ![![-5545, -907, 998, 266, -744]], ![![-4189, -680, 753, 198, -558]], ![![-1774, -301, 321, 91, -246]], ![![-7165, -1169, 1289, 342, -959]]]
  g := ![![![11, -11, 9, 3, -9], ![-31, 46, -17, -9, 9], ![25, 19, 64, 11, -81], ![-152, 287, 7, -29, -60], ![-65, 154, 42, -7, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![57, 34, -10, -8, 10]] ![![1082, 189, -197, -59, 155]]
  ![![-7496, -1225, 1349, 359, -1005]] where
 M := ![![![-7496, -1225, 1349, 359, -1005]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![-7496, -1225, 1349, 359, -1005]] ![![-32, -11, 9, 3, -9]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45264, -7835, 8229, 2433, -6437]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-45264, -7835, 8229, 2433, -6437]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![268, 237, 284, 1, 0], ![35, 35, 94, 0, 1]] where
  M :=![![![-45264, -7835, 8229, 2433, -6437], ![69945, 12028, -12701, -3715, 9885], ![-107475, -18121, 19458, 5513, -14925], ![46308, 6921, -8223, -1879, 5748], ![-17101, -2748, 3076, 805, -2278]]]
  hmulB := by decide  
  f := ![![![196, 59, -63, -19, 67]], ![![-747, -384, 97, 65, -27]], ![![129, -499, -514, -55, 699]], ![![-289, -693, -442, -16, 665]], ![![-28, -189, -150, -11, 214]]]
  g := ![![![-1489, -1133, -245, 2433, -6437], ![2270, 1724, 357, -3715, 9885], ![-3352, -2531, -452, 5513, -14925], ![1100, 792, -47, -1879, 5748], ![-483, -359, -36, 805, -2278]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [172, 18, 278, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 250, 268], [260, 66, 49], [0, 1]]
 g := ![![[169, 245, 61], [28, 268], [292, 277, 103], [14, 18, 95], [258, 113, 156], [49, 129, 67], [39, 1], []], ![[246, 223, 237, 286], [70, 175], [292, 83, 199, 173], [27, 68, 296, 252], [196, 197, 153, 51], [139, 316, 235, 34], [268, 235], [33, 182]], ![[293, 185, 126, 113], [47, 87], [179, 123, 229, 70], [194, 100, 312, 24], [88, 224, 43, 28], [249, 254, 30, 142], [253, 51], [252, 182]]]
 h' := ![![[96, 250, 268], [280, 34, 239], [179, 256, 153], [128, 155, 172], [4, 55, 27], [131, 136, 182], [266, 77, 235], [0, 0, 1], [0, 1]], ![[260, 66, 49], [44, 256, 160], [213, 165, 90], [32, 308, 270], [58, 266, 38], [9, 297, 276], [142, 171, 8], [53, 252, 66], [96, 250, 268]], ![[0, 1], [132, 27, 235], [218, 213, 74], [164, 171, 192], [29, 313, 252], [37, 201, 176], [181, 69, 74], [164, 65, 250], [260, 66, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 96], []]
 b := ![[], [161, 7, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [172, 18, 278, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15546102364, -15927749064, -5314975400, -311675128, 8434779140]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-716827880, -748511084, -2238701824, -311675128, 8434779140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -6, 6, -1, -1]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-24, -6, 6, -1, -1]] 
 ![![317, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![240, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-24, -6, 6, -1, -1], ![15, -9, -4, 13, -15], ![141, 118, -35, -77, 111], ![-558, -348, 138, 185, -288], ![121, 72, -30, -37, 58]]]
  hmulB := by decide  
  f := ![![![1778, 216, -372, -103, 287]], ![![809, 97, -170, -47, 131]], ![![1359, 164, -285, -79, 219]], ![![888, 108, -186, -52, 141]], ![![633, 78, -132, -37, 100]]]
  g := ![![![-1, -6, 6, -1, -1], ![6, -9, -4, 13, -15], ![-28, 118, -35, -77, 111], ![63, -348, 138, 185, -288], ![-12, 72, -30, -37, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![751, 274, -184, -66, 154]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![751, 274, -184, -66, 154]] 
 ![![317, 0, 0, 0, 0], ![237, 1, 0, 0, 0], ![257, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![223, 0, 0, 0, 1]] where
  M :=![![![751, 274, -184, -66, 154], ![-1650, -599, 406, 138, -330], ![3546, 1258, -875, -262, 666], ![-2778, -898, 688, 115, -408], ![326, 92, -80, -2, 33]]]
  hmulB := by decide  
  f := ![![![-6417, -5994, -1452, 242, 2302]], ![![-4887, -4565, -1106, 184, 1752]], ![![-5583, -5220, -1267, 208, 1996]], ![![-4314, -4046, -988, 155, 1528]], ![![-5033, -4714, -1148, 184, 1791]]]
  g := ![![![-125, 274, -184, -66, 154], ![269, -599, 406, 138, -330], ![-543, 1258, -875, -262, 666], ![328, -898, 688, 115, -408], ![-25, 92, -80, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-45264, -7835, 8229, 2433, -6437]] ![![-24, -6, 6, -1, -1]]
  ![![-7391, 2973, 605, -1950, 2158]] where
 M := ![![![-7391, 2973, 605, -1950, 2158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![-7391, 2973, 605, -1950, 2158]] ![![751, 274, -184, -66, 154]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![-2190153, -1095235, 523367, 511004, -849560]]]
 hmul := by decide  
 g := ![![![![-6909, -3455, 1651, 1612, -2680]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, -182, -230, -26, 270]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![491, -182, -230, -26, 270]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![209, 296, 134, 326, 1]] where
  M :=![![![491, -182, -230, -26, 270], ![-3162, -1873, -130, 158, 498], ![-6450, -7434, -2189, 262, 3390], ![-19152, -17074, -3914, 729, 6408], ![-12594, -11964, -2956, 466, 4607]]]
  hmulB := by decide  
  f := ![![![701, 266, -174, -66, 150]], ![![-1602, -607, 398, 150, -342]], ![![3654, 1382, -907, -338, 774]], ![![-3336, -1250, 830, 299, -696]], ![![-2795, -1046, 696, 250, -583]]]
  g := ![![![-169, -242, -110, -266, 270], ![-324, -451, -202, -490, 498], ![-2160, -3054, -1379, -3338, 3390], ![-4104, -5782, -2606, -6309, 6408], ![-2947, -4156, -1874, -4536, 4607]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [257, 277, 132, 218, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 264, 282, 101], [132, 53, 273, 190], [192, 13, 107, 40], [0, 1]]
 g := ![![[270, 150, 200, 194], [16, 62, 260, 76], [288, 330, 328], [228, 280, 42, 139], [55, 96, 20], [284, 47, 171], [113, 1], []], ![[27, 97, 279, 149, 24, 101], [61, 307, 116, 142, 264, 237], [250, 145, 291], [88, 96, 223, 85, 52, 32], [214, 161, 323], [307, 269, 179], [13, 318, 89, 230, 286, 176], [197, 203, 271]], ![[17, 171, 130, 265, 131, 12], [184, 116, 147, 278, 217, 148], [128, 28, 127], [111, 218, 146, 309, 194, 106], [197, 11, 83], [69, 50, 144], [99, 308, 245, 10, 6, 41], [173, 193, 21]], ![[234, 113, 228, 26, 191, 51], [120, 281, 233, 227, 5, 40], [194, 309, 328], [192, 289, 48, 207, 48, 35], [163, 11, 293], [17, 123, 149], [5, 194, 297, 303, 85, 162], [74, 28, 276]]]
 h' := ![![[120, 264, 282, 101], [191, 145, 191, 288], [209, 231, 40, 260], [322, 277, 92, 63], [26, 230, 59, 173], [119, 145, 187, 196], [87, 218, 33, 59], [0, 0, 1], [0, 1]], ![[132, 53, 273, 190], [1, 290, 220, 330], [9, 163, 315, 322], [294, 115, 179, 136], [66, 212, 231, 194], [214, 139, 318, 150], [2, 99, 238, 29], [181, 312, 58, 192], [120, 264, 282, 101]], ![[192, 13, 107, 40], [103, 108, 187, 26], [67, 273, 191, 79], [43, 95, 244, 69], [191, 213, 213, 123], [138, 90, 100, 165], [268, 95, 207, 319], [105, 213, 138, 161], [132, 53, 273, 190]], ![[0, 1], [33, 119, 64, 18], [292, 326, 116, 1], [318, 175, 147, 63], [83, 7, 159, 172], [54, 288, 57, 151], [293, 250, 184, 255], [303, 137, 134, 309], [192, 13, 107, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [104, 301, 100], []]
 b := ![[], [], [121, 289, 175, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [257, 277, 132, 218, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![582036388506, -81139418052, -624070382760, -388804259641, 946047452691]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-595594807323, -846257357748, -384877429134, -932931340897, 946047452691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-701, -266, 174, 66, -150]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![-701, -266, 174, 66, -150]] 
 ![![331, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![219, 0, 0, 1, 0], ![298, 0, 0, 0, 1]] where
  M :=![![![-701, -266, 174, 66, -150], ![1602, 607, -398, -150, 342], ![-3654, -1382, 907, 338, -774], ![3336, 1250, -830, -299, 696], ![-438, -164, 108, 38, -89]]]
  hmulB := by decide  
  f := ![![![-491, 182, 230, 26, -270]], ![![-75, 37, 40, 4, -48]], ![![-71, 56, 49, 4, -60]], ![![-267, 172, 164, 15, -198]], ![![-404, 200, 216, 22, -257]]]
  g := ![![![103, -266, 174, 66, -150], ![-235, 607, -398, -150, 342], ![533, -1382, 907, 338, -774], ![-481, 1250, -830, -299, 696], ![62, -164, 108, 38, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![491, -182, -230, -26, 270]] ![![-701, -266, 174, 66, -150]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![-331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5530, -2106, 1374, 525, -1189]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-5530, -2106, 1374, 525, -1189]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![64, 151, 1, 0, 0], ![223, 90, 0, 1, 0], ![204, 57, 0, 0, 1]] where
  M :=![![![-5530, -2106, 1374, 525, -1189], ![12693, 4831, -3156, -1205, 2733], ![-29181, -11122, 7241, 2769, -6261], ![27066, 10274, -6752, -2571, 5856], ![-3635, -1406, 884, 343, -756]]]
  hmulB := by decide  
  f := ![![![1188, 236, -212, -73, 175]], ![![-1881, -351, 382, 145, -351]], ![![-606, -109, 129, 50, -122]], ![![276, 60, -36, -8, 19]], ![![404, 85, -64, -20, 47]]]
  g := ![![![95, -561, 1374, 525, -1189], ![-220, 1288, -3156, -1205, 2733], ![496, -2958, 7241, 2769, -6261], ![-481, 2752, -6752, -2571, 5856], ![52, -364, 884, 343, -756]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 2 2 8 [285, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 336], [0, 1]]
 g := ![![[275, 162], [158], [75], [94], [158, 296], [52], [297, 85], [1]], ![[0, 175], [158], [75], [94], [238, 41], [52], [238, 252], [1]]]
 h' := ![![[146, 336], [127, 103], [189, 81], [41, 225], [128, 46], [2, 188], [279, 273], [52, 146], [0, 1]], ![[0, 1], [0, 234], [220, 256], [202, 112], [104, 291], [153, 149], [34, 64], [137, 191], [146, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [12, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 2
  hpos := by decide
  P := [285, 191, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![412011, 230292, -113196, -133334, 221496]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23131, 49548, -113196, -133334, 221496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-421, -384, -92, 12, 128]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-421, -384, -92, 12, 128]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![249, 145, 1, 0, 0], ![314, 228, 0, 1, 0], ![191, 301, 0, 0, 1]] where
  M :=![![![-421, -384, -92, 12, 128], ![-1572, -1549, -408, 36, 528], ![-6444, -6240, -1621, 132, 2016], ![-11508, -11388, -3048, 179, 3552], ![-7784, -7708, -2068, 112, 2367]]]
  hmulB := by decide  
  f := ![![![17379, 6608, -4324, -1628, 3712]], ![![-39660, -15013, 9864, 3660, -8400]], ![![-3957, -1477, 983, 348, -816]], ![![-10878, -4088, 2704, 979, -2272]], ![![-25543, -9653, 6352, 2344, -5393]]]
  g := ![![![-17, -84, -92, 12, 128], ![-36, -325, -408, 36, 528], ![-87, -1211, -1621, 132, 2016], ![38, -2016, -3048, 179, 3552], ![59, -1323, -2068, 112, 2367]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P1 : CertificateIrreducibleZModOfList' 337 2 2 8 [39, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [223, 336], [0, 1]]
 g := ![![[314, 121], [255], [262], [144], [31, 190], [189], [38, 190], [1]], ![[0, 216], [255], [262], [144], [276, 147], [189], [283, 147], [1]]]
 h' := ![![[223, 336], [243, 11], [304, 167], [225, 63], [139, 12], [138, 114], [203, 226], [298, 223], [0, 1]], ![[0, 1], [0, 326], [138, 170], [120, 274], [119, 325], [285, 223], [51, 111], [151, 114], [223, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [294, 218]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N1 : CertifiedPrimeIdeal' SI337N1 337 where
  n := 2
  hpos := by decide
  P := [39, 114, 1]
  hirr := P337P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-179365, -153908, -34051, 10432, 82364]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31774, -66429, -34051, 10432, 82364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N1 B_one_repr
lemma NI337N1 : Nat.card (O ⧸ I337N1) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-256, -100, 56, 45, -79]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![-256, -100, 56, 45, -79]] 
 ![![337, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![188, 0, 0, 0, 1]] where
  M :=![![![-256, -100, 56, 45, -79], ![813, 387, -190, -181, 303], ![-3093, -1620, 749, 769, -1263], ![6018, 3302, -1484, -1577, 2568], ![-1181, -640, 290, 305, -498]]]
  hmulB := by decide  
  f := ![![![-1818, -1934, -594, -1, 613]], ![![-243, -257, -78, 0, 80]], ![![-87, -94, -29, -1, 25]], ![![-450, -482, -148, -3, 138]], ![![-1069, -1142, -352, -3, 352]]]
  g := ![![![46, -100, 56, 45, -79], ![-176, 387, -190, -181, 303], ![733, -1620, 749, 769, -1263], ![-1490, 3302, -1484, -1577, 2568], ![289, -640, 290, 305, -498]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-5530, -2106, 1374, 525, -1189]] ![![-421, -384, -92, 12, 128]]
  ![![-1818, -1934, -594, -1, 613]] where
 M := ![![![-1818, -1934, -594, -1, 613]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![-1818, -1934, -594, -1, 613]] ![![-256, -100, 56, 45, -79]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1, I337N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
    exact isPrimeI337N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0 ⊙ MulI337N1)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-741, -211, 93, 44, -28]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-741, -211, 93, 44, -28]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![118, 291, 281, 1, 0], ![26, 155, 178, 0, 1]] where
  M :=![![![-741, -211, 93, 44, -28], ![204, -468, -299, -2, 444], ![-5322, -3645, -464, 296, 1308], ![-8394, -8039, -1969, 401, 3516], ![-6770, -5950, -1308, 318, 2407]]]
  hmulB := by decide  
  f := ![![![3263, 1235, -811, -302, 692]], ![![-7398, -2782, 1839, 668, -1548]], ![![16572, 6157, -4118, -1422, 3372]], ![![8284, 3058, -2058, -691, 1660]], ![![5446, 2010, -1353, -454, 1091]]]
  g := ![![![-15, -25, -21, 44, -28], ![-32, -198, -227, -2, 444], ![-214, -843, -912, 296, 1308], ![-424, -1930, -2134, 401, 3516], ![-308, -1359, -1496, 318, 2407]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [168, 324, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [291, 29, 212], [346, 317, 135], [0, 1]]
 g := ![![[116, 264, 124], [81, 254, 132], [316, 109], [106, 34, 9], [207, 68, 241], [256, 300], [149, 290, 1], []], ![[312, 39, 213, 284], [95, 263, 43, 100], [12, 144], [255, 256, 81, 328], [260, 199, 168, 127], [41, 157], [220, 38, 12, 297], [244, 181]], ![[186, 21, 175, 148], [328, 137, 241, 238], [93, 271], [47, 272, 73, 51], [29, 231, 72, 301], [304, 38], [111, 176, 300, 66], [321, 181]]]
 h' := ![![[291, 29, 212], [272, 254, 274], [179, 163, 241], [236, 73, 261], [271, 198, 344], [242, 122, 58], [299, 164, 91], [0, 0, 1], [0, 1]], ![[346, 317, 135], [255, 338, 171], [101, 131, 260], [27, 169, 12], [39, 1, 79], [171, 252, 181], [257, 79, 114], [314, 63, 317], [291, 29, 212]], ![[0, 1], [321, 102, 249], [147, 53, 193], [230, 105, 74], [152, 148, 271], [212, 320, 108], [52, 104, 142], [205, 284, 29], [346, 317, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [263, 315], []]
 b := ![[], [64, 144, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [168, 324, 57, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6065288, 3928946, -843990, -1348112, 1552518]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![359588, 448384, 292874, -1348112, 1552518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, -83, 51, 20, -44]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![-207, -83, 51, 20, -44]] 
 ![![347, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![214, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![182, 0, 0, 0, 1]] where
  M :=![![![-207, -83, 51, 20, -44], ![468, 176, -123, -46, 108], ![-1158, -473, 268, 108, -228], ![972, 325, -283, -99, 252], ![-190, -106, 20, 14, -13]]]
  hmulB := by decide  
  f := ![![![4585, 2491, -1121, -1182, 1924]], ![![459, 249, -112, -118, 192]], ![![3074, 1673, -752, -794, 1292]], ![![1409, 760, -342, -359, 584]], ![![2504, 1362, -612, -646, 1051]]]
  g := ![![![-8, -83, 51, 20, -44], ![20, 176, -123, -46, 108], ![-41, -473, 268, 108, -228], ![50, 325, -283, -99, 252], ![0, -106, 20, 14, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2556, -1097, 675, 267, -593]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![-2556, -1097, 675, 267, -593]] 
 ![![347, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![306, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![-2556, -1097, 675, 267, -593], ![6315, 2596, -1631, -637, 1425], ![-15189, -6079, 3870, 1499, -3369], ![14808, 5769, -3723, -1429, 3228], ![-1813, -738, 466, 181, -406]]]
  hmulB := by decide  
  f := ![![![5284, 4619, 981, -307, -2087]], ![![1491, 1305, 278, -86, -588]], ![![751, 669, 148, -39, -287]], ![![5430, 4785, 1035, -301, -2118]], ![![1887, 1678, 370, -99, -724]]]
  g := ![![![151, -1097, 675, 267, -593], ![-355, 2596, -1631, -637, 1425], ![828, -6079, 3870, 1499, -3369], ![-783, 5769, -3723, -1429, 3228], ![101, -738, 466, 181, -406]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-741, -211, 93, 44, -28]] ![![-207, -83, 51, 20, -44]]
  ![![-4967, -2354, 74, 182, 64]] where
 M := ![![![-4967, -2354, 74, 182, 64]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![-4967, -2354, 74, 182, 64]] ![![-2556, -1097, 675, 267, -593]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![-714820, -109305, 125267, 35741, -96813]]]
 hmul := by decide  
 g := ![![![![-2060, -315, 361, 103, -279]]]]
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

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![177261, 30806, -32246, -9596, 25300]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![177261, 30806, -32246, -9596, 25300]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![0, 0, 0, 349, 0], ![152, 102, 125, 139, 1]] where
  M :=![![![177261, 30806, -32246, -9596, 25300], ![-274812, -47789, 49998, 14896, -39252], ![426336, 74306, -77581, -23196, 60996], ![-193776, -34114, 35350, 10761, -28056], ![69392, 12180, -12624, -3808, 9953]]]
  hmulB := by decide  
  f := ![![![-55, -30, 6, 4, -4]], ![![36, -21, -38, -8, 36]], ![![-408, -282, -5, 20, 12]], ![![-120, -254, -142, -19, 120]], ![![-208, -222, -67, -1, 61]]]
  g := ![![![-10511, -7306, -9154, -10104, 25300], ![16308, 11335, 14202, 15676, -39252], ![-25344, -17614, -22069, -24360, 60996], ![11664, 8102, 10150, 11205, -28056], ![-4136, -2874, -3601, -3975, 9953]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 4 2 8 [33, 301, 67, 249, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 56, 153, 56], [76, 85, 39, 44], [313, 207, 157, 249], [0, 1]]
 g := ![![[252, 237, 227, 169], [14, 191, 272], [189, 239, 57, 142], [255, 149, 275, 151], [1, 134, 312, 25], [265, 295, 95], [100, 1], []], ![[16, 18, 169, 174, 230, 57], [187, 206, 181], [38, 117, 44, 130, 306, 194], [23, 72, 133, 202, 286, 73], [216, 79, 169, 143, 22, 269], [84, 125, 258], [41, 15, 319, 320, 262, 48], [268, 233, 344]], ![[29, 143, 123, 279, 20, 98], [82, 268, 135], [34, 110, 37, 218, 170, 120], [200, 314, 150, 246, 55, 175], [175, 110, 24, 257, 286, 343], [19, 83, 145], [108, 304, 294, 90, 223, 302], [99, 196, 191]], ![[79, 290, 242, 189, 186, 263], [310, 144, 231], [208, 31, 115, 108, 304, 332], [301, 190, 125, 236, 205, 126], [201, 246, 281, 95, 104, 75], [343, 210, 168], [342, 319, 304, 41, 323, 228], [17, 125, 228]]]
 h' := ![![[60, 56, 153, 56], [167, 240, 252, 336], [45, 263, 53, 137], [310, 36, 179, 96], [316, 53, 57, 271], [133, 343, 149, 344], [190, 230, 328, 161], [0, 0, 1], [0, 1]], ![[76, 85, 39, 44], [148, 250, 267, 224], [284, 90, 45, 251], [279, 104, 216, 290], [226, 293, 169, 124], [309, 316, 125, 211], [17, 166, 182, 266], [340, 29, 231, 254], [60, 56, 153, 56]], ![[313, 207, 157, 249], [340, 167, 172, 205], [258, 254, 80, 22], [60, 134, 101, 202], [238, 341, 284, 239], [219, 187, 67, 195], [130, 295, 44, 205], [66, 36, 202, 59], [76, 85, 39, 44]], ![[0, 1], [259, 41, 7, 282], [307, 91, 171, 288], [183, 75, 202, 110], [106, 11, 188, 64], [104, 201, 8, 297], [156, 7, 144, 66], [37, 284, 264, 36], [313, 207, 157, 249]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [321, 225, 74], []]
 b := ![[], [], [228, 225, 219, 268], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 4
  hpos := by decide
  P := [33, 301, 67, 249, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![975714258687, 56184689092, -828835918684, -545654567012, 1306771580136]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-566342595765, -381760792220, -470416284916, -522025513484, 1306771580136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 14835483601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 30, -6, -4, 4]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![55, 30, -6, -4, 4]] 
 ![![349, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![212, 0, 0, 0, 1]] where
  M :=![![![55, 30, -6, -4, 4], ![-36, 21, 38, 8, -36], ![408, 282, 5, -20, -12], ![120, 254, 142, 19, -120], ![224, 220, 56, 0, -45]]]
  hmulB := by decide  
  f := ![![![-177261, -30806, 32246, 9596, -25300]], ![![-36798, -6395, 6694, 1992, -5252]], ![![-56076, -9746, 10201, 3036, -8004]], ![![-78171, -13584, 14220, 4231, -11156]], ![![-107876, -18748, 19624, 5840, -15397]]]
  g := ![![![-5, 30, -6, -4, 4], ![2, 21, 38, 8, -36], ![-44, 282, 5, -20, -12], ![-33, 254, 142, 19, -120], ![-36, 220, 56, 0, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![177261, 30806, -32246, -9596, 25300]] ![![55, 30, -6, -4, 4]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-434, -263, -23, 21, 73]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![-434, -263, -23, 21, 73]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![337, 211, 240, 1, 0], ![18, 221, 332, 0, 1]] where
  M :=![![![-434, -263, -23, 21, 73], ![-939, -1062, -305, 37, 471], ![-5763, -5049, -1136, 221, 1857], ![-11004, -10457, -2593, 371, 3876], ![-7867, -7358, -1802, 259, 2676]]]
  hmulB := by decide  
  f := ![![![-378, -221, 93, 113, -179]], ![![1809, 1034, -447, -511, 819]], ![![-8295, -4679, 2056, 2277, -3675]], ![![-4869, -2746, 1207, 1337, -2158]], ![![-6698, -3770, 1661, 1830, -2957]]]
  g := ![![![-25, -59, -83, 21, 73], ![-62, -320, -469, 37, 471], ![-322, -1309, -1900, 221, 1857], ![-583, -2678, -3905, 371, 3876], ![-406, -1851, -2698, 259, 2676]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 3 2 8 [74, 270, 228, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 268, 305], [46, 84, 48], [0, 1]]
 g := ![![[309, 125, 218], [298, 311], [39, 86], [319, 83], [333, 304], [214, 29, 267], [176, 125, 1], []], ![[185, 144, 165, 346], [148, 164], [242, 93], [135, 331], [188, 140], [61, 29, 138, 137], [137, 60, 142, 192], [346, 186]], ![[28, 133, 121, 67], [278, 337], [209, 314], [13, 22], [75, 281], [215, 66, 205, 258], [86, 247, 284, 154], [250, 186]]]
 h' := ![![[79, 268, 305], [314, 69, 159], [221, 152, 283], [49, 282, 63], [351, 336, 275], [49, 41, 294], [37, 63, 178], [0, 0, 1], [0, 1]], ![[46, 84, 48], [266, 294, 160], [117, 67, 238], [187, 30, 228], [247, 122, 265], [220, 144, 136], [150, 108, 279], [52, 112, 84], [79, 268, 305]], ![[0, 1], [42, 343, 34], [136, 134, 185], [293, 41, 62], [14, 248, 166], [312, 168, 276], [245, 182, 249], [207, 241, 268], [46, 84, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [173, 42], []]
 b := ![[], [115, 71, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 3
  hpos := by decide
  P := [74, 270, 228, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-138313818, -219772216, -146003964, -51166952, 238254216]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36307006, -119200360, -189706332, -51166952, 238254216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 43986977 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-378, -221, 93, 113, -179]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-378, -221, 93, 113, -179]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![146, 226, 1, 0, 0], ![93, 128, 0, 1, 0], ![255, 20, 0, 0, 1]] where
  M :=![![![-378, -221, 93, 113, -179], ![1809, 1034, -447, -511, 819], ![-8295, -4679, 2056, 2277, -3675], ![17730, 9925, -4393, -4779, 7740], ![-3439, -1918, 854, 923, -1498]]]
  hmulB := by decide  
  f := ![![![-434, -263, -23, 21, 73]], ![![-939, -1062, -305, 37, 471]], ![![-797, -803, -208, 33, 337]], ![![-486, -484, -124, 20, 201]], ![![-389, -271, -39, 18, 87]]]
  g := ![![![60, -91, 93, 113, -179], ![-267, 428, -447, -511, 819], ![1181, -1947, 2056, 2277, -3675], ![-2465, 4135, -4393, -4779, 7740], ![476, -802, 854, 923, -1498]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [58, 298, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 352], [0, 1]]
 g := ![![[66, 140], [25], [338], [83], [58], [344, 97], [86, 201], [1]], ![[0, 213], [25], [338], [83], [58], [31, 256], [198, 152], [1]]]
 h' := ![![[55, 352], [286, 136], [18, 348], [81, 53], [134, 78], [169, 231], [307, 319], [295, 55], [0, 1]], ![[0, 1], [0, 217], [96, 5], [172, 300], [188, 275], [166, 122], [202, 34], [143, 298], [55, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [21, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [58, 298, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67809, -57557, -13434, 4019, 33984]
  a := ![-5, 2, -3, 1, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20244, 5055, -13434, 4019, 33984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![-434, -263, -23, 21, 73]] ![![-378, -221, 93, 113, -179]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10135, -3865, 2515, 962, -2176]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-10135, -3865, 2515, 962, -2176]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![268, 354, 310, 1, 0], ![251, 6, 305, 0, 1]] where
  M :=![![![-10135, -3865, 2515, 962, -2176], ![23226, 8826, -5789, -2208, 5016], ![-53568, -20483, 13242, 5078, -11448], ![49458, 18677, -12425, -4719, 10788], ![-6770, -2688, 1590, 630, -1359]]]
  hmulB := by decide  
  f := ![![![261, 45, -45, -12, 32]], ![![-348, -28, 69, 10, -48]], ![![546, 95, -48, 12, -24]], ![![324, 89, -7, 11, -44]], ![![641, 112, -71, 2, 1]]]
  g := ![![![775, -923, 1025, 962, -2176], ![-1794, 2118, -2371, -2208, 5016], ![4064, -4873, 5378, 5078, -11448], ![-3882, 4525, -5125, -4719, 10788], ![461, -606, 615, 630, -1359]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 3 2 8 [324, 33, 236, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 106, 242], [346, 252, 117], [0, 1]]
 g := ![![[168, 222, 91], [198, 212, 135], [202, 213, 51], [279, 120], [81, 125], [256, 351, 225], [18, 123, 1], []], ![[324, 147, 328, 237], [275, 176, 109, 141], [143, 101, 148, 133], [98, 111], [145, 150], [56, 33, 69, 331], [236, 159, 150, 255], [4, 47]], ![[72, 314, 281, 227], [343, 188, 241, 129], [87, 57, 357, 248], [315, 196], [340, 233], [316, 3, 336, 109], [268, 276, 350, 313], [129, 47]]]
 h' := ![![[136, 106, 242], [109, 62, 285], [249, 259, 213], [234, 191, 236], [188, 348, 185], [344, 93, 22], [271, 121, 344], [0, 0, 1], [0, 1]], ![[346, 252, 117], [139, 125, 305], [296, 219, 38], [349, 230, 148], [311, 53, 160], [82, 15, 48], [334, 298, 13], [327, 189, 252], [136, 106, 242]], ![[0, 1], [199, 172, 128], [144, 240, 108], [327, 297, 334], [245, 317, 14], [227, 251, 289], [238, 299, 2], [17, 170, 106], [346, 252, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158, 228], []]
 b := ![[], [302, 294, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 3
  hpos := by decide
  P := [324, 33, 236, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2284797595, 231526130, 2436170992, 1518465585, -3994047659]
  a := ![51, 23, 13, 60, -197]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1652569326, -1429919234, 2088847843, 1518465585, -3994047659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 46268279 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-261, -45, 45, 12, -32]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-261, -45, 45, 12, -32]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![251, 98, 1, 0, 0], ![266, 350, 0, 1, 0], ![57, 349, 0, 0, 1]] where
  M :=![![![-261, -45, 45, 12, -32], ![348, 28, -69, -10, 48], ![-546, -95, 48, -12, 24], ![-300, -353, -1, 95, -60], ![-166, -106, -32, -10, 65]]]
  hmulB := by decide  
  f := ![![![10135, 3865, -2515, -962, 2176]], ![![-23226, -8826, 5789, 2208, -5016]], ![![895, 350, -215, -84, 184]], ![![-15272, -5793, 3815, 1453, -3308]], ![![-20951, -7959, 5224, 1992, -4527]]]
  g := ![![![-36, 7, 45, 12, -32], ![49, -18, -69, -10, 48], ![-30, -25, 48, -12, 24], ![-61, -35, -1, 95, -60], ![19, -45, -32, -10, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [356, 347, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 358], [0, 1]]
 g := ![![[4, 193], [299, 345], [30, 22], [301], [69], [313, 60], [5, 144], [1]], ![[166, 166], [131, 14], [294, 337], [301], [69], [315, 299], [297, 215], [1]]]
 h' := ![![[12, 358], [179, 158], [90, 216], [101, 205], [224, 115], [221, 212], [15, 142], [3, 12], [0, 1]], ![[0, 1], [280, 201], [169, 143], [48, 154], [168, 244], [252, 147], [283, 217], [147, 347], [12, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [221, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [356, 347, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7229, -43272, -63318, -27991, 100329]
  a := ![16, 7, 5, 18, -63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![49100, -53081, -63318, -27991, 100329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-10135, -3865, 2515, 962, -2176]] ![![-261, -45, 45, 12, -32]]
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


lemma PB539I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB539I7 : PrimesBelowBoundCertificateInterval O 307 359 539 where
  m := 9
  g := ![2, 3, 3, 2, 3, 3, 2, 2, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB539I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0, I349N1]
    · exact ![I353N0, I353N1]
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
    · exact ![30080231, 96721]
    · exact ![30664297, 313, 313]
    · exact ![31855013, 317, 317]
    · exact ![12003612721, 331]
    · exact ![113569, 113569, 337]
    · exact ![41781923, 347, 347]
    · exact ![14835483601, 349]
    · exact ![43986977, 124609]
    · exact ![46268279, 128881]
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
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
      exact NI337N2
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I313N1, I313N2, I317N1, I317N2, I331N1, I337N2, I347N1, I347N2, I349N1]
  Il := ![[], [I313N1, I313N2], [I317N1, I317N2], [I331N1], [I337N2], [I347N1, I347N2], [I349N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
