
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 0, 0, 0, 0]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![367, 0, 0, 0, 0]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![0, 0, 0, 0, 367]] where
  M :=![![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![0, 0, 0, 0, 367]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 5 2 8 [97, 167, 175, 77, 56, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 309, 274, 139, 208], [310, 300, 365, 133, 4], [33, 51, 228, 316, 275], [185, 73, 234, 146, 247], [0, 1]]
 g := ![![[286, 78, 274, 229, 225], [22, 168, 340, 89, 227], [212, 315, 305, 226, 47], [106, 320, 230, 166, 33], [366, 0, 69, 279], [236, 42, 245, 360, 200], [1], []], ![[267, 81, 75, 120, 91, 255, 81, 30], [251, 152, 228, 44, 219, 148, 351, 338], [140, 246, 88, 204, 88, 281, 107, 25], [202, 122, 126, 211, 231, 322, 198, 170], [167, 325, 63, 324], [318, 117, 121, 199, 1, 329, 17, 166], [171, 302, 231, 83, 8, 23, 87, 102], [193, 320, 355, 325]], ![[174, 201, 131, 250, 112, 69, 86, 302], [250, 289, 344, 203, 275, 146, 128, 164], [324, 66, 133, 333, 4, 272, 134, 144], [50, 273, 34, 335, 348, 261, 184, 268], [303, 150, 25, 134], [112, 217, 11, 160, 282, 228, 49, 64], [198, 60, 191, 325, 67, 327, 37, 324], [21, 60, 168, 16]], ![[66, 89, 365, 348, 269, 299, 146, 311], [171, 195, 353, 3, 251, 281, 46, 34], [351, 56, 241, 329, 117, 167, 144, 68], [160, 235, 347, 53, 58, 105, 146, 79], [232, 54, 73, 199], [162, 275, 212, 218, 176, 47, 174, 312], [180, 233, 237, 366, 76, 212, 251, 320], [79, 218, 22, 23]], ![[56, 240, 296, 120, 360, 161, 220, 262], [286, 3, 27, 314, 66, 242, 264, 219], [247, 137, 271, 222, 66, 281, 234, 11], [299, 109, 289, 180, 131, 45, 264, 269], [168, 343, 163, 225], [44, 83, 223, 64, 51, 26, 324, 159], [81, 209, 155, 331, 85, 3, 309, 246], [162, 337, 91, 87]]]
 h' := ![![[150, 309, 274, 139, 208], [68, 359, 88, 342, 15], [355, 137, 172, 94, 31], [361, 15, 127, 219, 216], [57, 310, 10, 32, 20], [229, 54, 322, 118, 236], [270, 200, 192, 290, 311], [0, 0, 1], [0, 1]], ![[310, 300, 365, 133, 4], [161, 30, 17, 197, 337], [336, 90, 293, 357, 161], [299, 38, 238, 28, 363], [144, 210, 263, 56, 243], [36, 298, 127, 47, 18], [293, 247, 320, 50, 24], [109, 69, 247, 183, 332], [150, 309, 274, 139, 208]], ![[33, 51, 228, 316, 275], [306, 140, 310, 130, 268], [291, 0, 283, 70, 271], [275, 104, 199, 331, 6], [297, 83, 344, 35, 202], [121, 218, 350, 296, 177], [19, 253, 118, 125, 363], [111, 146, 49, 266, 9], [310, 300, 365, 133, 4]], ![[185, 73, 234, 146, 247], [355, 318, 93, 81, 195], [194, 124, 189, 144, 161], [196, 296, 304, 6, 126], [247, 328, 84, 174, 61], [167, 192, 186, 99, 318], [184, 135, 25, 115, 299], [32, 222, 149, 213, 65], [33, 51, 228, 316, 275]], ![[0, 1], [353, 254, 226, 351, 286], [115, 16, 164, 69, 110], [231, 281, 233, 150, 23], [83, 170, 33, 70, 208], [206, 339, 116, 174, 352], [13, 266, 79, 154, 104], [161, 297, 288, 72, 328], [185, 73, 234, 146, 247]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 79, 364, 342], [], [], []]
 b := ![[], [50, 111, 46, 326, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 5
  hpos := by decide
  P := [97, 167, 175, 77, 56, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95569184303213, 137667868675460, 72987295895752, 22110592767526, -85923482901604]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![260406496739, 375116808380, 198875465656, 60246846778, -234123931612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 6657793506607 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def PBC367 : ContainsPrimesAboveP 367 ![I367N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![367, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 367 (by decide) 𝕀

instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2364, 1075, -587, -395, 725]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![2364, 1075, -587, -395, 725]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![366, 175, 1, 0, 0], ![53, 164, 0, 1, 0], ![294, 356, 0, 0, 1]] where
  M :=![![![2364, 1075, -587, -395, 725], ![-7515, -3628, 1865, 1461, -2565], ![26397, 13409, -6550, -5783, 9837], ![-46590, -24719, 11555, 11231, -18660], ![8569, 4606, -2126, -2125, 3508]]]
  hmulB := by decide  
  f := ![![![-2276, -271, 477, 117, -443]], ![![4965, 1628, -505, -283, 75]], ![![96, 509, 237, -18, -408]], ![![1904, 712, -148, -110, -43]], ![![2969, 1364, -100, -179, -288]]]
  g := ![![![67, -240, -587, -395, 725], ![-36, 921, 1865, 1461, -2565], ![-434, -3737, -6550, -5783, 9837], ![1649, 7384, 11555, 11231, -18660], ![-354, -1404, -2126, -2125, 3508]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 2 2 8 [160, 175, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [198, 372], [0, 1]]
 g := ![![[106, 7], [267], [213, 267], [229], [242, 221], [253, 352], [312, 39], [1]], ![[0, 366], [267], [113, 106], [229], [359, 152], [198, 21], [201, 334], [1]]]
 h' := ![![[198, 372], [294, 315], [236, 283], [249, 283], [72, 244], [177, 229], [62, 195], [213, 198], [0, 1]], ![[0, 1], [0, 58], [320, 90], [333, 90], [267, 129], [13, 144], [253, 178], [252, 175], [198, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [166, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 2
  hpos := by decide
  P := [160, 175, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12107091, -11443723, -3319565, 190833, 6559615]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1972620, -4817800, -3319565, 190833, 6559615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100, -161, 43, 85, -123]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![-100, -161, 43, 85, -123]] 
 ![![373, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![152, 0, 1, 0, 0], ![174, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-100, -161, 43, 85, -123], ![1221, 842, -331, -415, 651], ![-6567, -3903, 1672, 1885, -3027], ![14724, 8297, -3671, -3975, 6444], ![-2787, -1590, 698, 763, -1234]]]
  hmulB := by decide  
  f := ![![![4076, 3113, 315, -195, -555]], ![![1593, 1226, 131, -75, -225]], ![![1789, 1383, 152, -83, -255]], ![![2070, 1633, 203, -91, -318]], ![![269, 235, 45, -8, -55]]]
  g := ![![![9, -161, 43, 85, -123], ![-16, 842, -331, -415, 651], ![34, -3903, 1672, 1885, -3027], ![-38, 8297, -3671, -3975, 6444], ![9, -1590, 698, 763, -1234]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1

def I373N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -6, 2, 1, -1]] i)))

def SI373N2: IdealEqSpanCertificate' Table ![![-18, -6, 2, 1, -1]] 
 ![![373, 0, 0, 0, 0], ![180, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![169, 0, 0, 1, 0], ![328, 0, 0, 0, 1]] where
  M :=![![![-18, -6, 2, 1, -1], ![9, -9, -8, -1, 9], ![-105, -70, -7, 5, 15], ![-102, -114, -36, 1, 48], ![-95, -86, -20, 3, 28]]]
  hmulB := by decide  
  f := ![![![-1052, -368, 256, 103, -233]], ![![-501, -175, 122, 49, -111]], ![![-159, -56, 39, 16, -36]], ![![-458, -158, 112, 44, -101]], ![![-927, -324, 226, 91, -206]]]
  g := ![![![3, -6, 2, 1, -1], ![-2, -9, -8, -1, 9], ![19, -70, -7, 5, 15], ![17, -114, -36, 1, 48], ![18, -86, -20, 3, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N2 : Nat.card (O ⧸ I373N2) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N2)

lemma isPrimeI373N2 : Ideal.IsPrime I373N2 := prime_ideal_of_norm_prime hp373.out _ NI373N2

def I373N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1762, -345, 333, 103, -265]] i)))

def SI373N3: IdealEqSpanCertificate' Table ![![-1762, -345, 333, 103, -265]] 
 ![![373, 0, 0, 0, 0], ![247, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![261, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![-1762, -345, 333, 103, -265], ![2871, 588, -551, -173, 441], ![-4773, -1035, 934, 299, -753], ![2634, 649, -541, -181, 444], ![-737, -154, 142, 45, -114]]]
  hmulB := by decide  
  f := ![![![774, 677, 157, -41, -377]], ![![525, 459, 106, -28, -254]], ![![393, 346, 81, -20, -188]], ![![678, 596, 136, -36, -309]], ![![401, 355, 83, -20, -185]]]
  g := ![![![112, -345, 333, 103, -265], ![-196, 588, -551, -173, 441], ![356, -1035, 934, 299, -753], ![-237, 649, -541, -181, 444], ![52, -154, 142, 45, -114]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N3 : Nat.card (O ⧸ I373N3) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N3)

lemma isPrimeI373N3 : Ideal.IsPrime I373N3 := prime_ideal_of_norm_prime hp373.out _ NI373N3
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![2364, 1075, -587, -395, 725]] ![![-100, -161, 43, 85, -123]]
  ![![-2905551, -1614458, 720458, 771620, -1254128]] where
 M := ![![![-2905551, -1614458, 720458, 771620, -1254128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N1 : IdealMulLeCertificate' Table 
  ![![-2905551, -1614458, 720458, 771620, -1254128]] ![![-18, -6, 2, 1, -1]]
  ![![2558626, 1421696, -634404, -679567, 1104475]] where
 M := ![![![2558626, 1421696, -634404, -679567, 1104475]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N2 : IdealMulLeCertificate' Table 
  ![![2558626, 1421696, -634404, -679567, 1104475]] ![![-1762, -345, 333, 103, -265]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![-2577057, -1288715, 615823, 601276, -999640]]]
 hmul := by decide  
 g := ![![![![-6909, -3455, 1651, 1612, -2680]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1, I373N2, I373N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
    exact isPrimeI373N2
    exact isPrimeI373N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0 ⊙ MulI373N1 ⊙ MulI373N2)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30752, -11592, 7608, 2887, -6563]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![-30752, -11592, 7608, 2887, -6563]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![99, 266, 78, 1, 0], ![64, 350, 354, 0, 1]] where
  M :=![![![-30752, -11592, 7608, 2887, -6563], ![70095, 26473, -17366, -6571, 14955], ![-159747, -60340, 39615, 14891, -33987], ![146538, 55200, -36378, -13423, 30888], ![-19369, -7242, 4800, 1741, -4038]]]
  hmulB := by decide  
  f := ![![![-150, -186, -66, -13, 11]], ![![-93, -291, -160, -71, -123]], ![![1689, 802, -149, -353, -1221]], ![![264, -72, -158, -128, -345]], ![![1483, 462, -296, -399, -1260]]]
  g := ![![![273, 4004, 5556, 2887, -6563], ![-624, -9129, -12662, -6571, 14955], ![1428, 20776, 28785, 14891, -33987], ![-1323, -18958, -26184, -13423, 30888], ![176, 2488, 3426, 1741, -4038]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 3 2 8 [62, 362, 348, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [327, 225, 272], [83, 153, 107], [0, 1]]
 g := ![![[172, 293, 118], [184, 5, 148], [333, 307], [244, 139, 225], [285, 158, 51], [60, 3, 234], [220, 31, 1], []], ![[212, 153, 318, 163], [141, 281, 15, 230], [326, 268], [66, 110, 9, 299], [266, 73, 190, 63], [366, 134, 135, 3], [166, 82, 231, 48], [158, 79]], ![[351, 29, 290, 142], [348, 50, 106, 101], [85, 87], [141, 199, 27, 195], [123, 235, 229, 289], [19, 114, 223, 324], [205, 304, 288, 207], [323, 79]]]
 h' := ![![[327, 225, 272], [341, 360, 298], [86, 6, 155], [32, 61, 341], [143, 328, 15], [70, 92, 52], [4, 302, 84], [0, 0, 1], [0, 1]], ![[83, 153, 107], [80, 199, 252], [372, 378, 333], [298, 65, 166], [261, 21, 172], [196, 216, 7], [278, 284, 246], [109, 160, 153], [327, 225, 272]], ![[0, 1], [145, 199, 208], [337, 374, 270], [231, 253, 251], [104, 30, 192], [339, 71, 320], [196, 172, 49], [128, 219, 225], [83, 153, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [358, 252], []]
 b := ![[], [128, 108, 183], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 3
  hpos := by decide
  P := [62, 362, 348, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49355720, 48671291, 13475077, -636234, -17904237]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3319826, 17109215, 16889713, -636234, -17904237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 54439939 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-150, -186, -66, -13, 11]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![-150, -186, -66, -13, 11]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![277, 223, 1, 0, 0], ![3, 99, 0, 1, 0], ![67, 370, 0, 0, 1]] where
  M :=![![![-150, -186, -66, -13, 11], ![-93, -291, -160, -71, -123], ![1689, 802, -149, -353, -1221], ![7902, 5976, 834, -805, -3888], ![6301, 4944, 786, -577, -2960]]]
  hmulB := by decide  
  f := ![![![-30752, -11592, 7608, 2887, -6563]], ![![70095, 26473, -17366, -6571, 14955]], ![![18346, 6945, -4553, -1717, 3913]], ![![18453, 6969, -4572, -1729, 3936]], ![![62943, 23776, -15596, -5900, 13429]]]
  g := ![![![46, 31, -66, -13, 11], ![139, 232, -160, -71, -123], ![332, 1374, -149, -353, -1221], ![105, 3531, 834, -805, -3888], ![-30, 2591, 786, -577, -2960]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P1 : CertificateIrreducibleZModOfList' 379 2 2 8 [190, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [297, 378], [0, 1]]
 g := ![![[164, 290], [277, 227], [217], [329, 142], [58, 266], [193, 64], [159, 281], [1]], ![[261, 89], [234, 152], [217], [55, 237], [228, 113], [251, 315], [236, 98], [1]]]
 h' := ![![[297, 378], [51, 153], [327, 201], [25, 322], [350, 349], [93, 32], [110, 371], [189, 297], [0, 1]], ![[0, 1], [12, 226], [142, 178], [151, 57], [157, 30], [122, 347], [8, 8], [91, 82], [297, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [160, 235]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N1 : CertifiedPrimeIdeal' SI379N1 379 where
  n := 2
  hpos := by decide
  P := [190, 82, 1]
  hirr := P379P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2267358, -2367214, -936130, -127492, 1823718]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![356818, -1202544, -936130, -127492, 1823718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N1 B_one_repr
lemma NI379N1 : Nat.card (O ⧸ I379N1) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N1
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![-30752, -11592, 7608, 2887, -6563]] ![![-150, -186, -66, -13, 11]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![379, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC379 : ContainsPrimesAboveP 379 ![I379N0, I379N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
    exact isPrimeI379N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 379 (by decide) (𝕀 ⊙ MulI379N0)
instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-685, -373, -17, 16, 2]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![-685, -373, -17, 16, 2]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![130, 137, 273, 1, 0], ![341, 58, 297, 0, 1]] where
  M :=![![![-685, -373, -17, 16, 2], ![-72, -734, -405, -78, 198], ![-2142, -1983, -578, -180, -342], ![2358, 465, -609, -611, -1692], ![1900, 956, -146, -416, -1497]]]
  hmulB := by decide  
  f := ![![![2487, 1409, -617, -686, 1106]], ![![-11214, -6292, 2781, 3036, -4914]], ![![49860, 27843, -12364, -13374, 21690]], ![![32100, 17922, -7960, -8607, 13960]], ![![39233, 21922, -9729, -10536, 17083]]]
  g := ![![![-9, -7, -13, 16, 2], ![-150, -4, -99, -78, 198], ![360, 111, 392, -180, -342], ![1720, 476, 1746, -611, -1692], ![1479, 378, 1457, -416, -1497]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 3 2 8 [182, 50, 350, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 85, 109], [378, 297, 274], [0, 1]]
 g := ![![[4, 228, 4], [107, 366, 76], [65, 46, 144], [144, 302, 227], [360, 224, 172], [273, 325, 42], [273, 33, 1], []], ![[109, 91, 342, 166], [216, 361, 278, 107], [367, 372, 180, 245], [168, 118, 51, 237], [54, 62, 339, 246], [177, 242, 61, 179], [64, 256, 109, 332], [27, 8]], ![[160, 86, 299, 86], [306, 220, 3, 24], [277, 301, 271, 204], [208, 256, 8, 260], [306, 330, 265, 289], [292, 381, 8, 252], [7, 140, 364, 306], [245, 8]]]
 h' := ![![[38, 85, 109], [59, 359, 381], [43, 337, 348], [219, 228, 371], [356, 306, 273], [104, 62, 129], [104, 260, 283], [0, 0, 1], [0, 1]], ![[378, 297, 274], [342, 227, 237], [249, 335, 294], [350, 44, 223], [343, 176, 301], [259, 184, 260], [28, 251, 172], [360, 207, 297], [38, 85, 109]], ![[0, 1], [70, 180, 148], [89, 94, 124], [340, 111, 172], [108, 284, 192], [122, 137, 377], [248, 255, 311], [246, 176, 85], [378, 297, 274]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 143], []]
 b := ![[], [190, 189, 206], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 3
  hpos := by decide
  P := [182, 50, 350, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2020004, 293849311, 361538669, 174690655, -566499072]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![445076706, 24068344, 315721186, 174690655, -566499072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 56181887 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2487, 1409, -617, -686, 1106]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![2487, 1409, -617, -686, 1106]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![222, 220, 1, 0, 0], ![92, 232, 0, 1, 0], ![268, 30, 0, 0, 1]] where
  M :=![![![2487, 1409, -617, -686, 1106], ![-11214, -6292, 2781, 3036, -4914], ![49860, 27843, -12364, -13374, 21690], ![-104472, -58179, 25905, 27869, -45252], ![20164, 11222, -5000, -5372, 8725]]]
  hmulB := by decide  
  f := ![![![-685, -373, -17, 16, 2]], ![![-72, -734, -405, -78, 198]], ![![-444, -643, -244, -36, 114]], ![![-202, -533, -251, -45, 116]], ![![-480, -316, -44, 4, 13]]]
  g := ![![![-245, 687, -617, -686, 1106], ![1068, -3068, 2781, 3036, -4914], ![-4668, 13577, -12364, -13374, 21690], ![9682, -28369, 25905, 27869, -45252], ![-1864, 5472, -5000, -5372, 8725]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P1 : CertificateIrreducibleZModOfList' 383 2 2 8 [330, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [233, 382], [0, 1]]
 g := ![![[279, 224], [252, 17], [218, 301], [274, 136], [304, 51], [165, 348], [182, 286], [1]], ![[0, 159], [0, 366], [262, 82], [173, 247], [314, 332], [53, 35], [178, 97], [1]]]
 h' := ![![[233, 382], [334, 135], [64, 363], [351, 105], [26, 265], [319, 267], [71, 242], [53, 233], [0, 1]], ![[0, 1], [0, 248], [0, 20], [304, 278], [108, 118], [101, 116], [156, 141], [339, 150], [233, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [343]]
 b := ![[], [32, 363]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N1 : CertifiedPrimeIdeal' SI383N1 383 where
  n := 2
  hpos := by decide
  P := [330, 150, 1]
  hirr := P383P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![412794, 230948, -112868, -131776, 218544]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54770, 128140, -112868, -131776, 218544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N1 B_one_repr
lemma NI383N1 : Nat.card (O ⧸ I383N1) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N1
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![-685, -373, -17, 16, 2]] ![![2487, 1409, -617, -686, 1106]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![383, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![168, 66, -38, -27, 49]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![168, 66, -38, -27, 49]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![2, 93, 1, 0, 0], ![296, 345, 0, 1, 0], ![49, 208, 0, 0, 1]] where
  M :=![![![168, 66, -38, -27, 49], ![-507, -235, 120, 103, -177], ![1815, 926, -441, -423, 705], ![-3342, -1804, 826, 847, -1392], ![647, 348, -158, -163, 266]]]
  hmulB := by decide  
  f := ![![![-50, -108, -52, -5, 49]], ![![-573, -489, -98, 9, 87]], ![![-140, -121, -25, 2, 22]], ![![-551, -521, -128, 4, 115]], ![![-315, -278, -60, 4, 53]]]
  g := ![![![15, 7, -38, -27, 49], ![-58, -26, 120, 103, -177], ![240, 106, -441, -423, 705], ![-482, -209, 826, 847, -1392], ![93, 41, -158, -163, 266]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 2 2 8 [226, 278, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 388], [0, 1]]
 g := ![![[15, 208], [202], [292, 157], [187], [111], [260], [129], [111, 1]], ![[152, 181], [202], [214, 232], [187], [111], [260], [129], [222, 388]]]
 h' := ![![[111, 388], [233, 347], [138, 37], [224, 270], [208, 365], [3, 82], [333, 250], [199, 36], [0, 1]], ![[0, 1], [239, 42], [355, 352], [241, 119], [267, 24], [158, 307], [75, 139], [305, 353], [111, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [286]]
 b := ![[], [38, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 2
  hpos := by decide
  P := [226, 278, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-179670, -152596, -34215, 12236, 86464]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20488, -49297, -34215, 12236, 86464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 25, -3, -4, 2]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![41, 25, -3, -4, 2]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![117, 235, 1, 0, 0], ![62, 260, 0, 1, 0], ![320, 107, 0, 0, 1]] where
  M :=![![![41, 25, -3, -4, 2], ![-12, 26, 33, 10, -42], ![474, 347, 6, -48, -6], ![114, 275, 205, 67, -276], ![376, 340, 66, -20, -75]]]
  hmulB := by decide  
  f := ![![![5607, 985, -1025, -306, 806]], ![![-8754, -1560, 1597, 480, -1254]], ![![-3567, -640, 650, 196, -510]], ![![-4974, -889, 907, 273, -712]], ![![2210, 382, -405, -120, 319]]]
  g := ![![![0, 4, -3, -4, 2], ![23, -15, 33, 10, -42], ![12, 31, 6, -48, -6], ![155, -92, 205, 67, -276], ![46, -5, 66, -20, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P1 : CertificateIrreducibleZModOfList' 389 2 2 8 [273, 334, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 388], [0, 1]]
 g := ![![[366, 316], [331], [320, 283], [49], [348], [335], [63], [55, 1]], ![[241, 73], [331], [325, 106], [49], [348], [335], [63], [110, 388]]]
 h' := ![![[55, 388], [269, 126], [165, 135], [351, 175], [180, 382], [291, 187], [135, 65], [156, 29], [0, 1]], ![[0, 1], [197, 263], [199, 254], [251, 214], [184, 7], [73, 202], [209, 324], [195, 360], [55, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [352, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N1 : CertifiedPrimeIdeal' SI389N1 389 where
  n := 2
  hpos := by decide
  P := [273, 334, 1]
  hirr := P389P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5085, 574, -3278, -5148, 8262]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4977, 3150, -3278, -5148, 8262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N1 B_one_repr
lemma NI389N1 : Nat.card (O ⧸ I389N1) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N1

def I389N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![242, 43, -43, -13, 33]] i)))

def SI389N2: IdealEqSpanCertificate' Table ![![242, 43, -43, -13, 33]] 
 ![![389, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![169, 0, 1, 0, 0], ![261, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![242, 43, -43, -13, 33], ![-357, -52, 69, 19, -57], ![627, 149, -90, -33, 57], ![-114, 83, 73, 7, -84], ![189, 104, 4, -9, -22]]]
  hmulB := by decide  
  f := ![![![3430, 1965, -855, -977, 1569]], ![![497, 285, -124, -142, 228]], ![![1673, 956, -417, -474, 762]], ![![1914, 1102, -478, -552, 885]], ![![1247, 713, -311, -354, 569]]]
  g := ![![![10, 43, -43, -13, 33], ![-16, -52, 69, 19, -57], ![20, 149, -90, -33, 57], ![-21, 83, 73, 7, -84], ![-4, 104, 4, -9, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N2 : Nat.card (O ⧸ I389N2) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N2)

lemma isPrimeI389N2 : Ideal.IsPrime I389N2 := prime_ideal_of_norm_prime hp389.out _ NI389N2
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![168, 66, -38, -27, 49]] ![![41, 25, -3, -4, 2]]
  ![![3430, 1965, -855, -977, 1569]] where
 M := ![![![3430, 1965, -855, -977, 1569]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N1 : IdealMulLeCertificate' Table 
  ![![3430, 1965, -855, -977, 1569]] ![![242, 43, -43, -13, 33]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1, I389N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
    exact isPrimeI389N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0 ⊙ MulI389N1)
instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033, 422, -260, -102, 226]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![1033, 422, -260, -102, 226]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![0, 0, 397, 0, 0], ![59, 212, 293, 1, 0], ![177, 217, 240, 0, 1]] where
  M :=![![![1033, 422, -260, -102, 226], ![-2406, -933, 626, 238, -546], ![5838, 2350, -1409, -554, 1218], ![-5274, -1914, 1416, 521, -1224], ![806, 392, -140, -66, 123]]]
  hmulB := by decide  
  f := ![![![-39, -14, 8, 6, -10]], ![![102, 43, -26, -22, 42]], ![![-438, -238, 87, 98, -138]], ![![-273, -154, 51, 61, -80]], ![![-227, -127, 42, 50, -65]]]
  g := ![![![-83, -68, -62, -102, 226], ![202, 169, 156, 238, -546], ![-446, -364, -331, -554, 1218], ![455, 386, 359, 521, -1224], ![-43, -31, -26, -66, 123]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 3 2 8 [314, 35, 209, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [365, 396, 389], [220, 0, 8], [0, 1]]
 g := ![![[344, 19, 349], [130, 30], [50, 28, 131], [63, 333, 265], [330, 40], [103, 105], [24, 11], [1]], ![[183, 78, 221, 139], [299, 276], [341, 390, 160, 157], [3, 381, 103, 241], [364, 298], [56, 119], [384, 191], [347, 196, 23, 282]], ![[152, 184, 360, 345], [183, 319], [309, 94, 4, 392], [81, 260, 377, 193], [352, 293], [168, 108], [230, 277], [324, 177, 182, 115]]]
 h' := ![![[365, 396, 389], [314, 144, 121], [180, 37, 344], [68, 354, 46], [193, 208, 258], [383, 124, 352], [147, 218, 36], [83, 362, 188], [0, 1]], ![[220, 0, 8], [120, 20, 39], [255, 6, 101], [179, 148, 344], [337, 122, 321], [233, 317, 199], [121, 382, 241], [3, 257, 280], [365, 396, 389]], ![[0, 1], [194, 233, 237], [263, 354, 349], [275, 292, 7], [111, 67, 215], [298, 353, 243], [127, 194, 120], [356, 175, 326], [220, 0, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 310], []]
 b := ![[], [68, 283, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 3
  hpos := by decide
  P := [314, 35, 209, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172854710, -238135339, -465322028, -253687915, 771197082]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-305696327, -286665149, -280156329, -253687915, 771197082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 62570773 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 14, -8, -6, 10]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![39, 14, -8, -6, 10]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![332, 208, 1, 0, 0], ![11, 171, 0, 1, 0], ![157, 191, 0, 0, 1]] where
  M :=![![![39, 14, -8, -6, 10], ![-102, -43, 26, 22, -42], ![438, 238, -87, -98, 138], ![-630, -306, 204, 187, -360], ![230, 152, -20, -42, 29]]]
  hmulB := by decide  
  f := ![![![-1033, -422, 260, 102, -226]], ![![2406, 933, -626, -238, 546]], ![![382, 130, -107, -38, 94]], ![![1021, 395, -266, -101, 232]], ![![747, 281, -198, -74, 173]]]
  g := ![![![3, 2, -8, -6, 10], ![-6, -3, 26, 22, -42], ![22, 22, -87, -98, 138], ![-35, -15, 204, 187, -360], ![7, 15, -20, -42, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P1 : CertificateIrreducibleZModOfList' 397 2 2 8 [138, 264, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 396], [0, 1]]
 g := ![![[140, 163], [110], [297, 265], [208, 25], [108], [206], [140], [133, 1]], ![[381, 234], [110], [209, 132], [357, 372], [108], [206], [140], [266, 396]]]
 h' := ![![[133, 396], [197, 166], [302, 260], [277, 139], [272, 392], [266, 120], [260, 172], [305, 83], [0, 1]], ![[0, 1], [43, 231], [343, 137], [105, 258], [4, 5], [346, 277], [110, 225], [228, 314], [133, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [393, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N1 : CertifiedPrimeIdeal' SI397N1 397 where
  n := 2
  hpos := by decide
  P := [138, 264, 1]
  hirr := P397P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80964, -123094, -91170, -38398, 185596]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3706, -25296, -91170, -38398, 185596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N1 B_one_repr
lemma NI397N1 : Nat.card (O ⧸ I397N1) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N1
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![1033, 422, -260, -102, 226]] ![![39, 14, -8, -6, 10]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![-397, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, 35, -29, -10, 24]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![143, 35, -29, -10, 24]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![258, 133, 1, 0, 0], ![86, 107, 0, 1, 0], ![270, 307, 0, 0, 1]] where
  M :=![![![143, 35, -29, -10, 24], ![-258, -68, 55, 20, -48], ![516, 161, -108, -46, 96], ![-378, -123, 99, 47, -108], ![102, 44, -14, -10, 11]]]
  hmulB := by decide  
  f := ![![![13, -25, -23, -4, 24]], ![![-276, -198, -17, 14, 24]], ![![-84, -83, -21, 2, 24]], ![![-74, -61, -10, 3, 12]], ![![-204, -170, -29, 8, 35]]]
  g := ![![![5, -6, -29, -10, 24], ![-8, 13, 55, 20, -48], ![16, -25, -108, -46, 96], ![-2, 37, 99, 47, -108], ![4, -1, -14, -10, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 2 2 8 [28, 270, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 400], [0, 1]]
 g := ![![[382, 43], [343], [172], [102], [75, 16], [203], [70], [131, 1]], ![[0, 358], [343], [172], [102], [166, 385], [203], [70], [262, 400]]]
 h' := ![![[131, 400], [22, 309], [53, 207], [154, 184], [306, 158], [2, 397], [318, 95], [342, 291], [0, 1]], ![[0, 1], [0, 92], [303, 194], [198, 217], [152, 243], [280, 4], [332, 306], [368, 110], [131, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [277]]
 b := ![[], [51, 339]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 2
  hpos := by decide
  P := [28, 270, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67699, -57613, -13350, 3991, 33312]
  a := ![-5, 2, -3, 1, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14865, -22284, -13350, 3991, 33312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 160801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205, 45, -39, -16, 36]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![205, 45, -39, -16, 36]] 
 ![![401, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![173, 0, 1, 0, 0], ![330, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![205, 45, -39, -16, 36], ![-384, -106, 77, 42, -84], ![882, 323, -190, -140, 252], ![-1110, -539, 263, 251, -420], ![246, 110, -56, -50, 85]]]
  hmulB := by decide  
  f := ![![![-181, -311, -169, 6, 300]], ![![-51, -79, -40, 2, 72]], ![![-109, -164, -81, 4, 144]], ![![-234, -331, -155, 9, 276]], ![![-103, -131, -55, 4, 97]]]
  g := ![![![11, 45, -39, -16, 36], ![-23, -106, 77, 42, -84], ![61, 323, -190, -140, 252], ![-92, -539, 263, 251, -420], ![19, 110, -56, -50, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N1 : Nat.card (O ⧸ I401N1) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N1)

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := prime_ideal_of_norm_prime hp401.out _ NI401N1

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, -18, 12, 5, -11]] i)))

def SI401N2: IdealEqSpanCertificate' Table ![![-50, -18, 12, 5, -11]] 
 ![![401, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![292, 0, 0, 1, 0], ![357, 0, 0, 0, 1]] where
  M :=![![![-50, -18, 12, 5, -11], ![117, 45, -28, -13, 27], ![-285, -114, 71, 37, -75], ![336, 152, -80, -53, 96], ![-49, -20, 14, 9, -18]]]
  hmulB := by decide  
  f := ![![![-660, -352, -2, 31, 49]], ![![-321, -173, -2, 15, 25]], ![![-111, -64, -3, 5, 11]], ![![-504, -280, -8, 23, 44]], ![![-605, -330, -6, 28, 49]]]
  g := ![![![13, -18, 12, 5, -11], ![-32, 45, -28, -13, 27], ![84, -114, 71, 37, -75], ![-108, 152, -80, -53, 96], ![17, -20, 14, 9, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N2 : Nat.card (O ⧸ I401N2) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N2)

lemma isPrimeI401N2 : Ideal.IsPrime I401N2 := prime_ideal_of_norm_prime hp401.out _ NI401N2

def I401N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, -9, 5, 7, -11]] i)))

def SI401N3: IdealEqSpanCertificate' Table ![![-32, -9, 5, 7, -11]] 
 ![![401, 0, 0, 0, 0], ![382, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![189, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-32, -9, 5, 7, -11], ![111, 54, -23, -33, 51], ![-513, -287, 120, 155, -243], ![1170, 671, -287, -339, 540], ![-247, -136, 60, 67, -108]]]
  hmulB := by decide  
  f := ![![![36, -87, -83, -57, -143]], ![![39, -80, -79, -55, -139]], ![![39, 19, -4, -9, -31]], ![![120, 46, -22, -34, -111]], ![![85, 48, -4, -17, -62]]]
  g := ![![![7, -9, 5, 7, -11], ![-44, 54, -23, -33, 51], ![238, -287, 120, 155, -243], ![-561, 671, -287, -339, 540], ![114, -136, 60, 67, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N3 : Nat.card (O ⧸ I401N3) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N3)

lemma isPrimeI401N3 : Ideal.IsPrime I401N3 := prime_ideal_of_norm_prime hp401.out _ NI401N3
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![143, 35, -29, -10, 24]] ![![205, 45, -39, -16, 36]]
  ![![7301, 1388, -1346, -468, 1140]] where
 M := ![![![7301, 1388, -1346, -468, 1140]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N1 : IdealMulLeCertificate' Table 
  ![![7301, 1388, -1346, -468, 1140]] ![![-50, -18, 12, 5, -11]]
  ![![-32152, -9450, 6582, 3723, -7333]] where
 M := ![![![-32152, -9450, 6582, 3723, -7333]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N2 : IdealMulLeCertificate' Table 
  ![![-32152, -9450, 6582, 3723, -7333]] ![![-32, -9, 5, 7, -11]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![2770509, 1385455, -662051, -646412, 1074680]]]
 hmul := by decide  
 g := ![![![![6909, 3455, -1651, -1612, 2680]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1, I401N2, I401N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
    exact isPrimeI401N2
    exact isPrimeI401N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0 ⊙ MulI401N1 ⊙ MulI401N2)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0, 0]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![409, 0, 0, 0, 0]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]] where
  M :=![![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [334, 181, 30, 285, 144, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 227, 407, 185, 69], [82, 55, 174, 5, 365], [395, 333, 41, 246, 186], [91, 202, 196, 382, 198], [0, 1]]
 g := ![![[225, 392, 369, 77, 384], [243, 249, 332, 203], [232, 331, 70, 71], [44, 138, 323, 263, 311], [343, 204, 196, 244, 212], [401, 151, 76, 1], [265, 1], []], ![[216, 221, 220, 201, 220, 185, 67, 318], [285, 348, 400, 163], [63, 378, 147, 270], [311, 128, 154, 46, 164, 398, 163, 401], [387, 290, 254, 371, 378, 307, 215, 106], [150, 294, 394, 202], [347, 222, 371, 41], [349, 49, 10, 310, 386, 147, 268, 82]], ![[284, 298, 62, 142, 191, 51, 82, 321], [163, 7, 273, 399], [363, 150, 160, 393], [374, 99, 258, 53, 108, 49, 214, 185], [313, 4, 380, 6, 23, 132, 180, 215], [214, 321, 113, 203], [50, 54, 287, 403], [218, 275, 59, 289, 199, 78, 178, 297]], ![[206, 181, 360, 63, 290, 381], [271, 363, 159, 137], [376, 286, 299, 48], [183, 214, 62, 127, 385, 366, 284, 165], [315, 353, 51, 234, 47, 173, 33, 268], [368, 194, 265, 91], [359, 356, 235, 54], [170, 3, 189, 351, 191, 161, 116, 59]], ![[272, 343, 360, 326, 134, 30, 260, 233], [26, 19, 40, 77], [268, 274, 173, 167], [301, 112, 258, 232, 14, 189, 95, 283], [320, 104, 260, 280, 40, 298, 137, 390], [358, 85, 280, 45], [278, 222, 89, 18], [295, 73, 71, 117, 140, 138, 234, 390]]]
 h' := ![![[106, 227, 407, 185, 69], [399, 55, 66, 378, 103], [188, 99, 95, 22, 77], [28, 60, 249, 306, 363], [367, 60, 178, 378, 164], [371, 108, 111, 365, 301], [243, 372, 49, 110, 1], [0, 0, 0, 1], [0, 1]], ![[82, 55, 174, 5, 365], [235, 285, 378, 32, 96], [42, 336, 382, 388, 347], [394, 22, 195, 39, 170], [27, 80, 15, 276, 248], [386, 341, 400, 72, 59], [307, 248, 378, 146, 171], [7, 364, 340, 319, 181], [106, 227, 407, 185, 69]], ![[395, 333, 41, 246, 186], [102, 82, 352, 233, 97], [51, 325, 243, 201, 342], [135, 215, 14, 287, 163], [254, 197, 42, 247, 178], [111, 398, 243, 62, 380], [336, 163, 127, 83, 332], [26, 233, 122, 111, 154], [82, 55, 174, 5, 365]], ![[91, 202, 196, 382, 198], [338, 379, 375, 318], [192, 257, 167, 399, 294], [43, 407, 284, 239, 146], [246, 181, 19, 105, 102], [82, 149, 118, 185, 289], [39, 318, 33, 217, 273], [190, 23, 274, 154, 192], [395, 333, 41, 246, 186]], ![[0, 1], [181, 17, 56, 266, 113], [337, 210, 340, 217, 167], [224, 114, 76, 356, 385], [36, 300, 155, 221, 126], [337, 231, 355, 134, 198], [236, 126, 231, 262, 41], [232, 198, 82, 233, 291], [91, 202, 196, 382, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [375, 14, 343, 375], [], [], []]
 b := ![[], [111, 194, 168, 87, 368], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 5
  hpos := by decide
  P := [334, 181, 30, 285, 144, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76585088278170945, -37221366451328721, 24999690481659321, 23302565926801674, -40620762385074939]
  a := ![51, 23, 13, 60, -197]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-187249604592105, -91005785944569, 61123937607969, 56974488818586, -99317267445171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 11445019581049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def PBC409 : ContainsPrimesAboveP 409 ![I409N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![409, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 409 (by decide) 𝕀

instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 7, -7, -1, 5]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![24, 7, -7, -1, 5]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![33, 266, 1, 0, 0], ![220, 254, 0, 1, 0], ![95, 257, 0, 0, 1]] where
  M :=![![![24, 7, -7, -1, 5], ![-57, -22, 9, -1, 3], ![-33, -71, -20, 27, -3], ![6, -17, -67, -63, 156], ![-143, -120, -12, 19, 16]]]
  hmulB := by decide  
  f := ![![![-1588, -261, 291, 85, -229]], ![![2493, 450, -431, -131, 333]], ![![1449, 264, -249, -76, 192]], ![![682, 137, -109, -35, 82]], ![![1168, 217, -198, -61, 152]]]
  g := ![![![0, 2, -7, -1, 5], ![-1, -7, 9, -1, 3], ![-12, -2, -20, 27, -3], ![3, -15, -67, -63, 156], ![-13, -14, -12, 19, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 2 2 8 [179, 171, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [248, 418], [0, 1]]
 g := ![![[15, 192], [181, 219], [195], [206], [386], [327, 388], [175], [248, 1]], ![[284, 227], [23, 200], [195], [206], [386], [181, 31], [175], [77, 418]]]
 h' := ![![[248, 418], [283, 232], [192, 122], [328, 219], [248, 25], [127, 321], [165, 183], [22, 151], [0, 1]], ![[0, 1], [416, 187], [280, 297], [170, 200], [163, 394], [125, 98], [297, 236], [179, 268], [248, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [330]]
 b := ![[], [71, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 2
  hpos := by decide
  P := [179, 171, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4236, -44504, -64198, -31159, 111417]
  a := ![16, 7, 5, 18, -63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3835, -8801, -64198, -31159, 111417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, -45, 49, -10, -6]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![-197, -45, 49, -10, -6]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![408, 223, 1, 0, 0], ![179, 61, 0, 1, 0], ![343, 51, 0, 0, 1]] where
  M :=![![![-197, -45, 49, -10, -6], ![102, -90, -25, 116, -138], ![1308, 1065, -322, -674, 978], ![-4908, -3037, 1219, 1609, -2508], ![1056, 630, -260, -320, 505]]]
  hmulB := by decide  
  f := ![![![-1045, -195, 185, 60, -126]], ![![1332, 88, -315, -62, 342]], ![![-318, -147, 13, 26, 60]], ![![-259, -78, 31, 17, 0]], ![![-701, -155, 112, 42, -59]]]
  g := ![![![-39, -24, 49, -10, -6], ![88, 13, -25, 116, -138], ![-196, 153, -322, -674, 978], ![167, -585, 1219, 1609, -2508], ![-21, 125, -260, -320, 505]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [246, 270, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 418], [0, 1]]
 g := ![![[369, 166], [293, 240], [373], [333], [192], [339, 205], [235], [149, 1]], ![[382, 253], [19, 179], [373], [333], [192], [297, 214], [235], [298, 418]]]
 h' := ![![[149, 418], [409, 66], [28, 272], [414, 293], [284, 282], [406, 187], [189, 144], [218, 167], [0, 1]], ![[0, 1], [187, 353], [332, 147], [76, 126], [402, 137], [196, 232], [276, 275], [380, 252], [149, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [408]]
 b := ![[], [305, 204]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N1 : CertifiedPrimeIdeal' SI419N1 419 where
  n := 2
  hpos := by decide
  P := [246, 270, 1]
  hirr := P419P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358014, -317131, -77890, 15167, 174876]
  a := ![-15, 2, -7, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74645, 17204, -77890, 15167, 174876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N1 B_one_repr
lemma NI419N1 : Nat.card (O ⧸ I419N1) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N1

def I419N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -23, -7, 0, 14]] i)))

def SI419N2: IdealEqSpanCertificate' Table ![![-25, -23, -7, 0, 14]] 
 ![![419, 0, 0, 0, 0], ![349, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![325, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-25, -23, -7, 0, 14], ![-168, -144, -23, 14, 42], ![-546, -541, -172, -4, 294], ![-1674, -1461, -255, 121, 396], ![-956, -908, -238, 24, 375]]]
  hmulB := by decide  
  f := ![![![-905937, -344609, 225017, 85938, -194746]], ![![-749625, -285149, 186192, 71110, -161144]], ![![-288144, -109609, 71570, 27334, -61942]], ![![-692103, -263266, 171904, 65653, -148778]], ![![-81403, -30965, 20219, 7722, -17499]]]
  g := ![![![20, -23, -7, 0, 14], ![112, -144, -23, 14, 42], ![479, -541, -172, -4, 294], ![1162, -1461, -255, 121, 396], ![775, -908, -238, 24, 375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N2 : Nat.card (O ⧸ I419N2) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N2)

lemma isPrimeI419N2 : Ideal.IsPrime I419N2 := prime_ideal_of_norm_prime hp419.out _ NI419N2
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![24, 7, -7, -1, 5]] ![![-197, -45, 49, -10, -6]]
  ![![-2982, -2978, 736, 2081, -2923]] where
 M := ![![![-2982, -2978, 736, 2081, -2923]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI419N1 : IdealMulLeCertificate' Table 
  ![![-2982, -2978, 736, 2081, -2923]] ![![-25, -23, -7, 0, 14]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![-516208, -287015, 127795, 137013, -222489]]]
 hmul := by decide  
 g := ![![![![-1232, -685, 305, 327, -531]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1, I419N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
    exact isPrimeI419N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0 ⊙ MulI419N1)


lemma PB539I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB539I8 : PrimesBelowBoundCertificateInterval O 359 419 539 where
  m := 9
  g := ![1, 4, 2, 2, 3, 2, 4, 1, 3]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB539I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0]
    · exact ![I373N0, I373N1, I373N2, I373N3]
    · exact ![I379N0, I379N1]
    · exact ![I383N0, I383N1]
    · exact ![I389N0, I389N1, I389N2]
    · exact ![I397N0, I397N1]
    · exact ![I401N0, I401N1, I401N2, I401N3]
    · exact ![I409N0]
    · exact ![I419N0, I419N1, I419N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
    · exact PBC419
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6657793506607]
    · exact ![139129, 373, 373, 373]
    · exact ![54439939, 143641]
    · exact ![56181887, 146689]
    · exact ![151321, 151321, 389]
    · exact ![62570773, 157609]
    · exact ![160801, 401, 401, 401]
    · exact ![11445019581049]
    · exact ![175561, 175561, 419]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
      exact NI373N2
      exact NI373N3
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
      exact NI389N2
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
      exact NI401N2
      exact NI401N3
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
      exact NI419N2
  β := ![I373N1, I373N2, I373N3, I389N2, I401N1, I401N2, I401N3, I419N2]
  Il := ![[], [I373N1, I373N2, I373N3], [], [], [I389N2], [], [I401N1, I401N2, I401N3], [], [I419N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
