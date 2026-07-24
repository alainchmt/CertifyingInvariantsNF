
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 405, 287, 142, -82]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![199, 405, 287, 142, -82]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![191, 234, 152, 241, 1]] where
  M :=![![![199, 405, 287, 142, -82], ![-492, -1031, -683, -287, 284], ![1704, 3768, 2942, 1305, -574], ![-3444, -6906, -3537, -1076, 2610], ![6978, 15969, 14113, 6714, -789]]]
  hmulB := by decide  
  f := ![![![-1099, -1353, -965, -56, 144]], ![![864, 1061, 751, 43, -112]], ![![-672, -816, -576, -33, 86]], ![![516, 618, 441, 26, -66]], ![![47, 48, 33, 2, -5]]]
  g := ![![![51, 63, 41, 64, -82], ![-176, -217, -141, -221, 284], ![358, 444, 290, 449, -574], ![-1614, -1986, -1287, -2026, 2610], ![507, 645, 431, 633, -789]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [170, 306, 235, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [220, 109, 72, 274], [299, 3, 14, 71], [67, 198, 225, 277], [0, 1]]
 g := ![![[17, 167, 287, 28], [93, 97, 159, 130], [93, 129, 254, 139], [58, 212, 98], [167, 150, 264, 120], [195, 72, 120, 52], [1], []], ![[40, 213, 206, 211, 292, 8], [253, 206, 130, 119, 173, 5], [58, 128, 97, 49, 31, 196], [243, 294, 166], [80, 278, 300, 4, 279, 146], [61, 116, 286, 111, 271, 225], [291, 178, 278], [288, 124, 125]], ![[75, 204, 122, 28, 74, 221], [83, 79, 265, 48, 31, 69], [22, 50, 154, 136, 105, 93], [160, 22, 72], [80, 33, 307, 14, 124, 279], [120, 133, 1, 221, 171, 284], [217, 83, 45], [196, 270, 65]], ![[87, 204, 160, 232, 52, 180], [34, 118, 29, 297, 123, 278], [136, 105, 93, 141, 54, 253], [290, 199, 70], [168, 31, 154, 134, 201, 45], [279, 157, 306, 215, 302, 7], [143, 260, 235], [103, 308, 223]]]
 h' := ![![[220, 109, 72, 274], [51, 260, 56, 31], [51, 36, 218, 290], [238, 188, 63, 254], [222, 172, 241, 151], [127, 219, 233, 162], [141, 5, 76, 275], [0, 0, 1], [0, 1]], ![[299, 3, 14, 71], [98, 72, 163, 5], [185, 237, 294, 167], [302, 39, 34, 89], [101, 257, 76, 119], [186, 147, 13, 277], [91, 297, 40, 162], [62, 19, 35, 30], [220, 109, 72, 274]], ![[67, 198, 225, 277], [164, 295, 176, 257], [144, 82, 195, 94], [32, 61, 31, 45], [233, 218, 191, 85], [13, 55, 104, 192], [57, 6, 118, 309], [101, 103, 204, 40], [299, 3, 14, 71]], ![[0, 1], [7, 306, 227, 18], [278, 267, 226, 71], [154, 23, 183, 234], [117, 286, 114, 267], [65, 201, 272, 302], [74, 3, 77, 187], [41, 189, 71, 241], [67, 198, 225, 277]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [200, 98, 106], []]
 b := ![[], [], [112, 287, 269, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [170, 306, 235, 36, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7912350986, 21445527408, 27438341072, 14994171970, 6296814416]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3841733770, -4668839376, -2989316560, -4831312226, 6296814416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1099, -1353, -965, -56, 144]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-1099, -1353, -965, -56, 144]] 
 ![![311, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![304, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![290, 0, 0, 0, 1]] where
  M :=![![![-1099, -1353, -965, -56, 144], ![864, 1061, 751, 43, -112], ![-672, -816, -576, -33, 86], ![516, 618, 441, 26, -66], ![138, 171, 115, 6, -17]]]
  hmulB := by decide  
  f := ![![![199, 405, 287, 142, -82]], ![![88, 179, 127, 63, -36]], ![![200, 408, 290, 143, -82]], ![![19, 39, 32, 18, -4]], ![![208, 429, 313, 154, -79]]]
  g := ![![![1423, -1353, -965, -56, 144], ![-1111, 1061, 751, 43, -112], ![853, -816, -576, -33, 86], ![-650, 618, 441, 26, -66], ![-174, 171, 115, 6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![199, 405, 287, 142, -82]] ![![-1099, -1353, -965, -56, 144]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 136, 104, 10, -10]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![109, 136, 104, 10, -10]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![200, 126, 282, 1, 0], ![283, 175, 209, 0, 1]] where
  M :=![![![109, 136, 104, 10, -10], ![-60, -41, -4, 34, 20], ![120, 240, 293, 136, 68], ![408, 1140, 1396, 769, 272], ![756, 2124, 2848, 1582, 735]]]
  hmulB := by decide  
  f := ![![![181, 344, 144, -6, -18]], ![![-108, -89, 68, 18, -12]], ![![-72, -288, -251, -16, 36]], ![![8, -74, -106, -11, 16]], ![![55, 69, 1, -6, 1]]]
  g := ![![![3, 2, -2, 10, -10], ![-40, -25, -44, 34, 20], ![-148, -92, -167, 136, 68], ![-736, -458, -870, 769, 272], ![-1673, -1041, -1907, 1582, 735]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [68, 107, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 52, 75], [291, 260, 238], [0, 1]]
 g := ![![[170, 141, 243], [23, 156], [0, 176], [133, 217, 58], [176, 79, 83], [17, 215, 281], [312, 1], []], ![[117, 223, 3, 72], [220, 289], [109, 29], [71, 311, 253, 6], [131, 138, 157, 235], [157, 32, 212, 36], [111, 305], [297, 304]], ![[175, 196, 218, 197], [58, 151], [1, 70], [67, 142, 86, 48], [244, 158, 296, 52], [111, 135, 276, 11], [155, 200], [134, 304]]]
 h' := ![![[21, 52, 75], [278, 1, 192], [150, 54, 248], [33, 277, 241], [239, 36, 269], [96, 79, 108], [68, 39, 207], [0, 0, 1], [0, 1]], ![[291, 260, 238], [273, 143, 228], [181, 252, 296], [304, 11, 177], [75, 84, 24], [58, 188, 201], [8, 253, 92], [277, 126, 260], [21, 52, 75]], ![[0, 1], [76, 169, 206], [138, 7, 82], [110, 25, 208], [36, 193, 20], [213, 46, 4], [131, 21, 14], [136, 187, 52], [291, 260, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 276], []]
 b := ![[], [262, 180, 109], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [68, 107, 1, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-810433, -1701800, -918934, -588613, 594363]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163874, -100799, 130505, -588613, 594363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 599, 428, 25, -64]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![491, 599, 428, 25, -64]] 
 ![![313, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![275, 0, 0, 0, 1]] where
  M :=![![![491, 599, 428, 25, -64], ![-384, -469, -336, -20, 50], ![300, 366, 261, 14, -40], ![-240, -300, -220, -19, 28], ![-66, -93, -80, -19, 1]]]
  hmulB := by decide  
  f := ![![![-385, -1061, -816, -157, 166]], ![![-78, -217, -168, -32, 34]], ![![-38, -100, -75, -16, 16]], ![![-186, -522, -404, -73, 80]], ![![-353, -964, -740, -148, 153]]]
  g := ![![![-117, 599, 428, 25, -64], ![92, -469, -336, -20, 50], ![-70, 366, 261, 14, -40], ![66, -300, -220, -19, 28], ![35, -93, -80, -19, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-629, -769, -549, -32, 82]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![-629, -769, -549, -32, 82]] 
 ![![313, 0, 0, 0, 0], ![278, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![248, 0, 0, 0, 1]] where
  M :=![![![-629, -769, -549, -32, 82], ![492, 601, 429, 25, -64], ![-384, -468, -334, -19, 50], ![300, 366, 263, 16, -38], ![78, 99, 73, 8, -9]]]
  hmulB := by decide  
  f := ![![![271, 19, -455, -62, 68]], ![![242, 21, -401, -55, 60]], ![![21, -3, -41, -5, 6]], ![![6, 0, -11, -2, 2]], ![![218, 23, -355, -48, 53]]]
  g := ![![![664, -769, -549, -32, 82], ![-519, 601, 429, 25, -64], ![404, -468, -334, -19, 50], ![-317, 366, 263, 16, -38], ![-87, 99, 73, 8, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![109, 136, 104, 10, -10]] ![![491, 599, 428, 25, -64]]
  ![![30755, 37501, 26700, 1461, -4066]] where
 M := ![![![30755, 37501, 26700, 1461, -4066]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![30755, 37501, 26700, 1461, -4066]] ![![-629, -769, -549, -32, 82]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-11026051, -13475902, -9626941, -563087, 1437922]]]
 hmul := by decide  
 g := ![![![![-35227, -43054, -30757, -1799, 4594]]]]
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

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, 0, 0, 0, 0]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![317, 0, 0, 0, 0]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![0, 0, 0, 317, 0], ![0, 0, 0, 0, 317]] where
  M :=![![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![0, 0, 0, 317, 0], ![0, 0, 0, 0, 317]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 5 2 8 [184, 117, 255, 184, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 139, 69, 304, 316], [240, 127, 303, 258, 123], [289, 314, 238, 57, 171], [225, 53, 24, 15, 24], [0, 1]]
 g := ![![[192, 242, 75, 129, 313], [66, 87, 199, 57], [55, 148, 81, 243, 156], [238, 35, 194, 152, 54], [5, 132, 204, 139, 240], [253, 114, 257, 296, 1], [], []], ![[250, 210, 230, 265, 61, 311, 265, 196], [126, 93, 264, 212], [118, 121, 126, 251, 190, 264, 175, 1], [107, 97, 107, 251, 257, 235, 112, 59], [282, 18, 173, 67, 25, 191, 15, 289], [55, 94, 120, 126, 246, 22, 167, 172], [105, 154, 208, 256], [269, 59, 5, 1]], ![[124, 210, 314, 136, 1, 283, 102, 9], [32, 299, 14, 64], [234, 236, 196, 31, 210, 307, 152, 217], [141, 100, 208, 206, 193, 57, 31, 207], [307, 119, 55, 232, 135, 129, 209, 101], [59, 27, 173, 61, 122, 52, 51, 216], [13, 59, 256, 244], [50, 25, 310, 230]], ![[284, 40, 242, 179, 241, 291, 156, 174], [142, 124, 143, 136], [99, 157, 100, 245, 62, 61, 311, 305], [32, 53, 262, 219, 311, 20, 255, 220], [108, 208, 121, 276, 31, 184, 257, 276], [180, 126, 69, 88, 44, 39, 222, 62], [72, 225, 171, 70], [295, 14, 125, 77]], ![[35, 250, 252, 26, 248, 62, 59, 59], [160, 31, 27, 238], [158, 274, 62, 2, 241, 195, 96, 16], [137, 155, 252, 117, 105, 235, 168, 204], [51, 263, 95, 116, 283, 131, 210, 99], [41, 137, 176, 84, 169, 125, 47, 251], [252, 277, 32, 57], [298, 198, 36, 259]]]
 h' := ![![[176, 139, 69, 304, 316], [161, 223, 48, 144, 228], [24, 149, 230, 258, 101], [271, 277, 101, 87, 135], [31, 160, 80, 124, 110], [47, 143, 74, 247, 160], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[240, 127, 303, 258, 123], [78, 235, 42, 213, 306], [306, 112, 166, 118, 294], [152, 104, 55, 30, 203], [115, 300, 193, 76, 163], [268, 191, 95, 160, 281], [221, 283, 49, 32, 70], [183, 259, 159, 16, 16], [176, 139, 69, 304, 316]], ![[289, 314, 238, 57, 171], [139, 91, 154, 137, 148], [315, 107, 270, 34, 309], [16, 71, 11, 26, 186], [143, 77, 273, 135, 57], [83, 1, 200, 26, 288], [201, 245, 124, 217, 181], [216, 107, 94, 125, 161], [240, 127, 303, 258, 123]], ![[225, 53, 24, 15, 24], [226, 34, 106, 161, 93], [186, 72, 265, 271, 88], [224, 74, 73, 49, 87], [12, 82, 300, 73, 9], [86, 6, 177, 273, 177], [289, 149, 125, 281, 131], [77, 166, 304, 33, 241], [289, 314, 238, 57, 171]], ![[0, 1], [105, 51, 284, 296, 176], [309, 194, 20, 270, 159], [241, 108, 77, 125, 23], [77, 15, 105, 226, 295], [137, 293, 88, 245, 45], [19, 274, 19, 104, 251], [231, 102, 76, 143, 216], [225, 53, 24, 15, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [310, 140, 77, 109], [], [], []]
 b := ![[], [128, 192, 196, 315, 109], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 5
  hpos := by decide
  P := [184, 117, 255, 184, 21, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-207098199174, -561189900648, -717739866272, -392179359254, -164539723018]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-653306622, -1770315144, -2264163616, -1237158862, -519052754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 3201078401357 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def PBC317 : ContainsPrimesAboveP 317 ![I317N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![317, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 317 (by decide) 𝕀

instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20699, -25056, -17906, -906, 2614]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![-20699, -25056, -17906, -906, 2614]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![307, 36, 293, 124, 1]] where
  M :=![![![-20699, -25056, -17906, -906, 2614], ![15684, 18511, 13248, 392, -1812], ![-10872, -11496, -8277, 564, 784], ![4704, 888, 828, -2789, 1128], ![8820, 16560, 11648, 4080, -3181]]]
  hmulB := by decide  
  f := ![![![151, 288, 114, -6, -14]], ![![-84, -59, 72, 16, -12]], ![![-72, -264, -223, -12, 32]], ![![192, 408, 204, 1, -24]], ![![139, 180, -7, -14, 5]]]
  g := ![![![-2487, -360, -2368, -982, 2614], ![1728, 253, 1644, 680, -1812], ![-760, -120, -719, -292, 784], ![-1032, -120, -996, -431, 1128], ![2977, 396, 2851, 1204, -3181]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [236, 258, 87, 142, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 143, 118, 202], [110, 243, 283, 258], [307, 275, 261, 202], [0, 1]]
 g := ![![[130, 1, 89, 46], [90, 133, 15, 189], [283, 197, 291], [252, 21, 269, 143], [232, 59, 279], [31, 228, 87], [189, 1], []], ![[224, 288, 207, 0, 318, 20], [167, 279, 296, 70, 153, 58], [34, 59, 68], [57, 50, 168, 183, 47, 214], [321, 291, 19], [54, 88, 74], [91, 26, 253, 25, 160, 294], [275, 326, 91]], ![[162, 72, 60, 36, 41, 223], [316, 58, 164, 114, 124, 234], [35, 30, 24], [20, 215, 103, 275, 71, 304], [131, 165, 131], [67, 176, 177], [61, 58, 63, 188, 161, 45], [317, 5, 33]], ![[30, 263, 126, 9, 321, 219], [78, 240, 273, 270, 36, 77], [300, 180, 177], [47, 118, 321, 68, 315, 100], [16, 326, 289], [162, 34, 287], [327, 74, 260, 183, 27, 241], [105, 173, 91]]]
 h' := ![![[103, 143, 118, 202], [275, 246, 3, 276], [153, 185, 47, 92], [108, 99, 311, 195], [237, 98, 76, 229], [238, 126, 167, 96], [81, 321, 180, 217], [0, 0, 1], [0, 1]], ![[110, 243, 283, 258], [300, 302, 134, 212], [77, 286, 319, 52], [275, 179, 19, 125], [20, 136, 285, 149], [242, 249, 191, 130], [121, 247, 328, 220], [324, 70, 315, 27], [103, 143, 118, 202]], ![[307, 275, 261, 202], [137, 268, 292, 83], [96, 7, 116, 149], [322, 116, 287, 149], [10, 9, 120, 207], [229, 320, 22, 88], [309, 25, 262, 138], [178, 284, 247, 322], [110, 243, 283, 258]], ![[0, 1], [6, 177, 233, 91], [229, 184, 180, 38], [224, 268, 45, 193], [326, 88, 181, 77], [285, 298, 282, 17], [320, 69, 223, 87], [290, 308, 99, 313], [307, 275, 261, 202]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [232, 280, 137], []]
 b := ![[], [], [77, 100, 184, 283], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [236, 258, 87, 142, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22945767868, 62225149990, 79687479464, 43559349346, 18335827122]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16937018606, -1806237542, -15990060022, -6737411522, 18335827122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -288, -114, 6, 14]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![-151, -288, -114, 6, 14]] 
 ![![331, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-151, -288, -114, 6, 14], ![84, 59, -72, -16, 12], ![72, 264, 223, 12, -32], ![-192, -408, -204, -1, 24], ![36, -48, -136, -24, 15]]]
  hmulB := by decide  
  f := ![![![20699, 25056, 17906, 906, -2614]], ![![5143, 6227, 4450, 226, -650]], ![![3910, 4728, 3379, 168, -492]], ![![9366, 11352, 8112, 419, -1188]], ![![2037, 2448, 1750, 78, -251]]]
  g := ![![![89, -288, -114, 6, 14], ![5, 59, -72, -16, 12], ![-110, 264, 223, 12, -32], ![138, -408, -204, -1, 24], ![47, -48, -136, -24, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![-20699, -25056, -17906, -906, 2614]] ![![-151, -288, -114, 6, 14]]
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

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -10, -31, -5, 4]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![17, -10, -31, -5, 4]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![224, 51, 263, 1, 0], ![200, 314, 321, 0, 1]] where
  M :=![![![17, -10, -31, -5, 4], ![24, 77, 45, -3, -10], ![-60, -126, -76, -25, -6], ![-36, -150, -241, -118, -50], ![-120, -330, -471, -283, -115]]]
  hmulB := by decide  
  f := ![![![65, 70, 55, 3, -8]], ![![-48, -55, -47, -1, 6]], ![![36, 42, 34, -5, -2]], ![![64, 71, 56, -2, -6]], ![![28, 30, 21, -4, -1]]]
  g := ![![![1, -3, 0, -5, 4], ![8, 10, 12, -3, -10], ![20, 9, 25, -25, -6], ![108, 64, 139, -118, -50], ![256, 149, 329, -283, -115]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [298, 208, 278, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [241, 168, 175], [155, 168, 162], [0, 1]]
 g := ![![[179, 19, 296], [43, 84], [130, 82], [209, 287], [192, 124, 196], [186, 263], [240, 59, 1], []], ![[218, 38, 34, 173], [12, 72], [135, 230], [282, 189], [143, 121, 74, 18], [138, 305], [299, 336, 265, 128], [43, 295]], ![[52, 94, 146, 112], [117, 321], [163, 295], [119, 334], [223, 21, 319, 64], [328, 237], [5, 60, 326, 209], [56, 295]]]
 h' := ![![[241, 168, 175], [95, 214, 149], [56, 215, 74], [147, 44, 115], [74, 248, 306], [224, 216, 323], [261, 235, 242], [0, 0, 1], [0, 1]], ![[155, 168, 162], [173, 148, 137], [288, 208, 181], [33, 211, 60], [184, 74, 111], [204, 101, 63], [35, 49, 227], [109, 298, 168], [241, 168, 175]], ![[0, 1], [224, 312, 51], [49, 251, 82], [134, 82, 162], [124, 15, 257], [71, 20, 288], [191, 53, 205], [260, 39, 168], [155, 168, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 108], []]
 b := ![[], [125, 175, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [298, 208, 278, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16154945, -43795380, -56044627, -30627051, -12883271]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27955367, 16508995, 36007121, -30627051, -12883271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -28, -20, -8, 6]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-13, -28, -20, -8, 6]] 
 ![![337, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![201, 0, 0, 0, 1]] where
  M :=![![![-13, -28, -20, -8, 6], ![36, 77, 54, 22, -16], ![-96, -204, -141, -58, 44], ![264, 564, 398, 167, -116], ![-300, -636, -434, -178, 145]]]
  hmulB := by decide  
  f := ![![![-3277, -4388, -2840, -124, 414]], ![![-790, -1059, -686, -30, 100]], ![![-160, -212, -137, -6, 20]], ![![-348, -468, -302, -13, 44]], ![![-1953, -2616, -1694, -74, 247]]]
  g := ![![![5, -28, -20, -8, 6], ![-14, 77, 54, 22, -16], ![36, -204, -141, -58, 44], ![-104, 564, 398, 167, -116], ![107, -636, -434, -178, 145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365, 446, 309, 17, -46]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![365, 446, 309, 17, -46]] 
 ![![337, 0, 0, 0, 0], ![329, 1, 0, 0, 0], ![273, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![365, 446, 309, 17, -46], ![-276, -325, -227, -13, 34], ![204, 234, 172, 11, -26], ![-156, -186, -145, -10, 22], ![-36, -30, -19, -1, 3]]]
  hmulB := by decide  
  f := ![![![125, 286, 235, 105, -58]], ![![121, 277, 228, 102, -56]], ![![105, 240, 197, 88, -48]], ![![54, 126, 109, 50, -22]], ![![18, 42, 39, 19, -1]]]
  g := ![![![-692, 446, 309, 17, -46], ![506, -325, -227, -13, 34], ![-372, 234, 172, 11, -26], ![303, -186, -145, -10, 22], ![45, -30, -19, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![17, -10, -31, -5, 4]] ![![-13, -28, -20, -8, 6]]
  ![![-125, -286, -235, -105, 58]] where
 M := ![![![-125, -286, -235, -105, 58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![-125, -286, -235, -105, 58]] ![![365, 446, 309, 17, -46]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![-337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 3171, 3175, 228, -456]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![593, 3171, 3175, 228, -456]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![3, 339, 252, 1, 0], ![316, 142, 342, 0, 1]] where
  M :=![![![593, 3171, 3175, 228, -456], ![-2736, -6247, -3441, -17, 456], ![2736, 4104, 576, -249, -34], ![-204, 2226, 3345, 338, -498], ![-2862, -5889, -2741, 54, 355]]]
  hmulB := by decide  
  f := ![![![823, 1005, 719, 42, -106]], ![![-636, -767, -543, -23, 84]], ![![504, 624, 470, 45, -46]], ![![-249, -288, -183, 11, 48]], ![![986, 1217, 897, 74, -107]]]
  g := ![![![415, -27, 293, 228, -456], ![-423, -188, -447, -17, 456], ![41, 269, 216, -249, -34], ![450, -120, 255, 338, -498], ![-332, -215, -397, 54, 355]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [10, 316, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 4, 290], [77, 342, 57], [0, 1]]
 g := ![![[162, 210, 339], [159, 308, 12], [173, 90], [209, 51, 184], [21, 237, 340], [142, 310], [113, 192, 1], []], ![[312, 247, 340, 115], [43, 91, 191, 332], [18, 61], [228, 92, 337, 29], [292, 76, 284, 16], [63, 3], [268, 328, 146, 310], [140, 126]], ![[276, 345, 236, 174], [83, 83, 115, 26], [175, 321], [194, 310, 165, 142], [122, 95, 20, 77], [49, 244], [95, 84, 315, 218], [26, 126]]]
 h' := ![![[115, 4, 290], [145, 17, 133], [69, 71, 157], [339, 101, 319], [137, 152, 312], [255, 251, 149], [258, 195, 225], [0, 0, 1], [0, 1]], ![[77, 342, 57], [139, 117, 101], [328, 214, 26], [94, 138, 282], [16, 102, 186], [178, 164, 216], [304, 315, 252], [27, 183, 342], [115, 4, 290]], ![[0, 1], [12, 213, 113], [309, 62, 164], [329, 108, 93], [112, 93, 196], [233, 279, 329], [305, 184, 217], [117, 164, 4], [77, 342, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [221, 128], []]
 b := ![[], [17, 48, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [10, 316, 155, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4075022, -8550048, -5491368, -2133772, 2246836]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2039406, 1140484, -680688, -2133772, 2246836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 1005, 719, 42, -106]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![823, 1005, 719, 42, -106]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![343, 95, 1, 0, 0], ![33, 340, 0, 1, 0], ![335, 128, 0, 0, 1]] where
  M :=![![![823, 1005, 719, 42, -106], ![-636, -767, -543, -23, 84], ![504, 624, 470, 45, -46], ![-276, -186, -21, 148, 90], ![18, 225, 421, 282, 171]]]
  hmulB := by decide  
  f := ![![![593, 3171, 3175, 228, -456]], ![![-2736, -6247, -3441, -17, 456]], ![![-155, 1436, 2198, 220, -326]], ![![-2625, -5813, -3060, 6, 402]], ![![-445, 740, 1788, 214, -271]]]
  g := ![![![-610, -196, 719, 42, -106], ![456, 138, -543, -23, 84], ![-423, -154, 470, 45, -46], ![-81, -173, -21, 148, 90], ![-608, -454, 421, 282, 171]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [249, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 346], [0, 1]]
 g := ![![[281, 131], [207, 192], [127], [167, 330], [275, 105], [202], [72, 10], [1]], ![[0, 216], [264, 155], [127], [124, 17], [214, 242], [202], [281, 337], [1]]]
 h' := ![![[125, 346], [160, 82], [80, 66], [57, 47], [231, 32], [287, 136], [116, 152], [98, 125], [0, 1]], ![[0, 1], [0, 265], [2, 281], [33, 300], [67, 315], [284, 211], [31, 195], [108, 222], [125, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [328]]
 b := ![[], [160, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [249, 222, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6550, 10042, 15600, 9679, 4013]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20196, -15206, 15600, 9679, 4013]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![593, 3171, 3175, 228, -456]] ![![823, 1005, 719, 42, -106]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2473, 3006, 2148, 116, -316]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![2473, 3006, 2148, 116, -316]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![283, 65, 183, 1, 0], ![106, 127, 215, 0, 1]] where
  M :=![![![2473, 3006, 2148, 116, -316], ![-1896, -2267, -1618, -64, 232], ![1392, 1584, 1149, 6, -128], ![-768, -528, -330, 253, 12], ![-660, -1086, -622, -126, 317]]]
  hmulB := by decide  
  f := ![![![-299, -246, 208, 52, -36]], ![![-216, -839, -734, -44, 104]], ![![624, 1344, 677, -6, -88]], ![![43, 347, 387, 31, -56]], ![![214, 445, 211, -4, -27]]]
  g := ![![![9, 102, 140, 116, -316], ![-24, -79, -114, -64, 232], ![38, 50, 79, 6, -128], ![-211, -53, -141, 253, 12], ![4, -95, -131, -126, 317]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [35, 300, 322, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [276, 205, 308], [100, 143, 41], [0, 1]]
 g := ![![[32, 126, 95], [71, 51], [333, 292, 340], [100, 150, 344], [292], [148, 19], [80, 27, 1], []], ![[242, 342, 138, 168], [203, 130], [42, 122, 333, 312], [146, 240, 47, 307], [265, 105, 91, 153], [48, 283], [53, 239, 127, 238], [308, 285]], ![[59, 95, 21, 106], [343, 258], [273, 336, 35, 268], [276, 26, 327, 280], [289, 99, 133, 196], [201, 110], [316, 330, 346, 12], [226, 285]]]
 h' := ![![[276, 205, 308], [156, 26, 188], [211, 264, 20], [339, 28, 290], [250, 200, 293], [119, 169], [341, 183, 307], [0, 0, 1], [0, 1]], ![[100, 143, 41], [228, 334, 341], [2, 43, 63], [220, 68, 187], [189, 326, 195], [346, 94, 51], [242, 204, 102], [133, 315, 143], [276, 205, 308]], ![[0, 1], [259, 338, 169], [7, 42, 266], [234, 253, 221], [232, 172, 210], [267, 86, 298], [312, 311, 289], [345, 34, 205], [100, 143, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199, 222], []]
 b := ![[], [344, 131, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [35, 300, 322, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![549854, 1670754, 2540739, 1449773, 845471]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1430819, -572892, -1273765, 1449773, 845471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 559, 519, 34, -74]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![127, 559, 519, 34, -74]] 
 ![![349, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![263, 0, 0, 1, 0], ![307, 0, 0, 0, 1]] where
  M :=![![![127, 559, 519, 34, -74], ![-444, -983, -517, 1, 68], ![408, 576, 38, -41, 2], ![12, 438, 565, 52, -82], ![-450, -897, -389, 16, 51]]]
  hmulB := by decide  
  f := ![![![-1577, 1103, 677, 1812, -872]], ![![-381, 214, 128, 405, -192]], ![![-254, 362, 234, 407, -206]], ![![-1375, 427, 228, 1246, -570]], ![![-1157, 1460, 938, 1736, -871]]]
  g := ![![![-194, 559, 519, 34, -74], ![270, -983, -517, 1, 68], ![-111, 576, 38, -41, 2], ![-182, 438, 565, 52, -82], ![228, -897, -389, 16, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -17, -11, -6, 4]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![-7, -17, -11, -6, 4]] 
 ![![349, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![234, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![-7, -17, -11, -6, 4], ![24, 53, 37, 17, -12], ![-72, -156, -110, -47, 34], ![204, 438, 307, 128, -94], ![-246, -525, -367, -152, 111]]]
  hmulB := by decide  
  f := ![![![617, 983, 527, 4, -74]], ![![149, 238, 128, 1, -18]], ![![184, 292, 156, 1, -22]], ![![414, 660, 353, 2, -50]], ![![218, 347, 185, 0, -27]]]
  g := ![![![10, -17, -11, -6, 4], ![-31, 53, 37, 17, -12], ![90, -156, -110, -47, 34], ![-250, 438, 307, 128, -94], ![299, -525, -367, -152, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![2473, 3006, 2148, 116, -316]] ![![127, 559, 519, 34, -74]]
  ![![-617, -983, -527, -4, 74]] where
 M := ![![![-617, -983, -527, -4, 74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![-617, -983, -527, -4, 74]] ![![-7, -17, -11, -6, 4]]
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

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![353, 0, 0, 0, 0]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]] where
  M :=![![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 5 2 8 [270, 275, 124, 47, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [292, 326, 90, 149, 306], [62, 244, 279, 173, 289], [20, 352, 19, 34, 126], [322, 136, 318, 350, 338], [0, 1]]
 g := ![![[331, 68, 70, 104, 337], [231, 217, 217, 98], [262, 309, 99, 262], [338, 176, 46, 331], [30, 226, 246, 182], [26, 274, 236, 293, 100], [1], []], ![[326, 196, 321, 344, 330, 296, 27, 186], [212, 292, 243, 164], [74, 325, 281, 166], [195, 213, 42, 46], [285, 221, 251, 18], [11, 227, 25, 15, 350, 206, 141, 65], [198, 125, 171, 273, 124, 285, 13, 98], [207, 127, 263, 91]], ![[0, 262, 202, 218, 120, 108, 61, 196], [154, 272, 339, 50], [39, 172, 310, 352], [293, 315, 17, 122], [190, 322, 105, 2], [345, 107, 190, 125, 158, 152, 133, 285], [231, 54, 250, 224, 4, 41, 62, 73], [19, 320, 83, 213]], ![[99, 216, 128, 79, 38, 309, 143, 279], [26, 49, 298, 1], [51, 6, 173, 36], [50, 165, 216, 23], [290, 79, 236, 168], [250, 130, 103, 23, 249, 72, 196, 245], [315, 54, 63, 70, 108, 183, 163, 110], [235, 271, 186, 344]], ![[7, 18, 340, 325, 189, 279, 138, 93], [134, 20, 340, 4], [178, 207, 62, 198], [182, 94, 166, 88], [199, 307, 21, 319], [8, 329, 288, 308, 163, 178, 262, 315], [10, 316, 239, 140, 126, 193, 282, 189], [95, 82, 311, 225]]]
 h' := ![![[292, 326, 90, 149, 306], [77, 117, 107, 59, 185], [242, 60, 25, 344, 110], [303, 139, 336, 246, 144], [207, 216, 213, 5, 265], [40, 242, 205, 89, 83], [83, 78, 229, 306, 343], [0, 0, 1], [0, 1]], ![[62, 244, 279, 173, 289], [201, 176, 350, 341, 111], [322, 279, 209, 22, 115], [74, 105, 149, 58, 318], [132, 293, 338, 116, 273], [277, 265, 213, 150, 205], [187, 352, 125, 308, 312], [75, 329, 52, 26, 122], [292, 326, 90, 149, 306]], ![[20, 352, 19, 34, 126], [172, 249, 59, 105, 103], [110, 298, 348, 281, 129], [224, 211, 218, 54, 42], [209, 341, 269, 286, 162], [18, 238, 51, 341, 186], [259, 117, 98, 259, 197], [126, 53, 75, 337, 338], [62, 244, 279, 173, 289]], ![[322, 136, 318, 350, 338], [24, 13, 171, 182, 278], [168, 337, 270, 154, 1], [309, 35, 292, 338, 347], [116, 326, 274, 139, 27], [224, 1, 311, 5, 121], [164, 232, 271, 316, 10], [137, 188, 78, 86, 15], [20, 352, 19, 34, 126]], ![[0, 1], [12, 151, 19, 19, 29], [48, 85, 207, 258, 351], [10, 216, 64, 10, 208], [78, 236, 318, 160, 332], [161, 313, 279, 121, 111], [220, 280, 336, 223, 197], [21, 136, 147, 257, 231], [322, 136, 318, 350, 338]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 210, 165, 185], [], [], []]
 b := ![[], [330, 144, 65, 48, 49], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 5
  hpos := by decide
  P := [270, 275, 124, 47, 10, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13210394601657, 35887272036480, 46091852588139, 25215338562706, 10690869470071]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37423214169, 101663660160, 130571820363, 71431554002, 30285749207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 5481173216993 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def PBC353 : ContainsPrimesAboveP 353 ![I353N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![353, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 353 (by decide) 𝕀

instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26191, -32082, -22859, -1329, 3412]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-26191, -32082, -22859, -1329, 3412]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![0, 0, 0, 359, 0], ![250, 152, 78, 191, 1]] where
  M :=![![![-26191, -32082, -22859, -1329, 3412], ![20472, 24989, 17769, 1025, -2658], ![-15948, -19398, -13856, -837, 2050], ![12300, 14802, 10515, 494, -1674], ![2952, 3294, 2021, -183, -531]]]
  hmulB := by decide  
  f := ![![![55, 114, 77, 33, -24]], ![![-144, -305, -213, -91, 66]], ![![396, 846, 594, 249, -182]], ![![-1092, -2334, -1635, -680, 498]], ![![-514, -1100, -772, -321, 235]]]
  g := ![![![-2449, -1534, -805, -1819, 3412], ![1908, 1195, 627, 1417, -2658], ![-1472, -922, -484, -1093, 2050], ![1200, 750, 393, 892, -1674], ![378, 234, 121, 282, -531]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 4 2 8 [357, 120, 137, 180, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [244, 134, 348, 30], [232, 294, 48, 127], [62, 289, 322, 202], [0, 1]]
 g := ![![[122, 329, 20, 30], [235, 192, 99, 72], [211, 259, 327, 283], [203, 214, 64], [236, 137, 173], [252, 345, 326, 55], [179, 1], []], ![[276, 172, 170, 194, 330, 246], [62, 90, 255, 104, 329, 188], [302, 125, 42, 226, 230, 88], [298, 289, 120], [30, 355, 254], [164, 141, 42, 288, 244, 296], [324, 118, 181, 16, 224, 110], [296, 326, 182]], ![[43, 168, 94, 205, 48, 217], [332, 177, 131, 92, 281, 222], [253, 69, 5, 28, 152, 92], [32, 205, 147], [234, 234, 8], [11, 219, 1, 38, 33, 99], [213, 238, 117, 225, 347, 147], [306, 358, 333]], ![[40, 157, 341, 258, 307, 222], [357, 90, 17, 134, 284, 185], [322, 218, 4, 172, 134, 169], [253, 69, 204], [293, 135, 345], [46, 344, 95, 172, 251, 107], [346, 336, 5, 134, 162, 123], [298, 191, 237]]]
 h' := ![![[244, 134, 348, 30], [111, 206, 39, 272], [63, 118, 62, 114], [101, 47, 136, 203], [316, 76, 209, 351], [145, 248, 353, 116], [358, 62, 128, 312], [0, 0, 1], [0, 1]], ![[232, 294, 48, 127], [250, 159, 22, 233], [130, 106, 326, 176], [1, 340, 60, 112], [29, 43, 97, 185], [317, 354, 56, 62], [204, 130, 19, 313], [175, 9, 54, 328], [244, 134, 348, 30]], ![[62, 289, 322, 202], [80, 349, 173, 259], [242, 166, 84, 18], [6, 85, 124, 96], [115, 226, 103, 295], [134, 203, 296, 38], [95, 340, 109, 158], [227, 251, 80, 147], [232, 294, 48, 127]], ![[0, 1], [208, 4, 125, 313], [71, 328, 246, 51], [88, 246, 39, 307], [165, 14, 309, 246], [80, 272, 13, 143], [31, 186, 103, 294], [132, 99, 224, 243], [62, 289, 322, 202]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [67, 92, 131], []]
 b := ![[], [], [259, 111, 203, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 4
  hpos := by decide
  P := [357, 120, 137, 180, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4410951819, 11993019080, 15425254904, 8442096204, 3591951284]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2489072059, -1487419432, -737456672, -1887522560, 3591951284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 16610312161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -114, -77, -33, 24]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-55, -114, -77, -33, 24]] 
 ![![359, 0, 0, 0, 0], ![336, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![354, 0, 0, 0, 1]] where
  M :=![![![-55, -114, -77, -33, 24], ![144, 305, 213, 91, -66], ![-396, -846, -594, -249, 182], ![1092, 2334, 1635, 680, -498], ![-1296, -2766, -1931, -801, 589]]]
  hmulB := by decide  
  f := ![![![26191, 32082, 22859, 1329, -3412]], ![![24456, 29957, 21345, 1241, -3186]], ![![13833, 16944, 12073, 702, -1802]], ![![2811, 3444, 2454, 143, -366]], ![![25818, 31626, 22535, 1311, -3363]]]
  g := ![![![127, -114, -77, -33, 24], ![-342, 305, 213, 91, -66], ![951, -846, -594, -249, 182], ![-2625, 2334, 1635, 680, -498], ![3108, -2766, -1931, -801, 589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-26191, -32082, -22859, -1329, 3412]] ![![-55, -114, -77, -33, 24]]
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


lemma PB441I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB441I7 : PrimesBelowBoundCertificateInterval O 307 359 441 where
  m := 9
  g := ![2, 3, 1, 2, 3, 2, 3, 1, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB441I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0]
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
    · exact ![30664297, 313, 313]
    · exact ![3201078401357]
    · exact ![12003612721, 331]
    · exact ![38272753, 337, 337]
    · exact ![41781923, 120409]
    · exact ![42508549, 349, 349]
    · exact ![5481173216993]
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
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I313N1, I313N2, I331N1, I337N1, I337N2, I349N1, I349N2, I359N1]
  Il := ![[I311N1], [I313N1, I313N2], [], [I331N1], [I337N1, I337N2], [], [I349N1, I349N2], [], [I359N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
