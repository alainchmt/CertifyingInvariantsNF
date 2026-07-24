
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35573, 76967, -14164, 4273, 15466]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![35573, 76967, -14164, 4273, 15466]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![264, 181, 1, 0, 0], ![317, 193, 0, 1, 0], ![74, 319, 0, 0, 1]] where
  M :=![![![35573, 76967, -14164, 4273, 15466], ![6920, 39846, 74320, -34319, -83456], ![-14818, -27399, 20345, -8367, -22646], ![-5912, -23185, -29854, 13982, 33568], ![5114, 14250, 7834, -3888, -8851]]]
  hmulB := by decide  
  f := ![![![-49353, 20445, -89314, 40713, 103910]], ![![22484, -8640, 38674, -20653, -56524]], ![![-19218, 8213, -35531, 15068, 37034]], ![![-24123, 10332, -44668, 18842, 46174]], ![![7488, -2674, 12272, -7513, -21595]]]
  g := ![![![2732, -6676, -14164, 4273, 15466], ![-5479, 42471, 74320, -34319, -83456], ![-2265, 10983, 20345, -8367, -22646], ![2054, -17187, -29854, 13982, 33568], ![-376, 4647, 7834, -3888, -8851]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [215, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [312, 466], [0, 1]]
 g := ![![[446, 371], [344, 410], [270], [174], [282, 47], [236], [327, 49], [312, 1]], ![[382, 96], [306, 57], [270], [174], [2, 420], [236], [204, 418], [157, 466]]]
 h' := ![![[312, 466], [293, 71], [177, 133], [279, 292], [80, 328], [275, 395], [212, 161], [168, 460], [0, 1]], ![[0, 1], [29, 396], [110, 334], [318, 175], [143, 139], [227, 72], [8, 306], [319, 7], [312, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361]]
 b := ![[], [329, 414]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [215, 155, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17179, 17718, 37944, 190284, 427350]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-218369, -385224, 37944, 190284, 427350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137579, -57318, 249953, -112467, -285210]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![137579, -57318, 249953, -112467, -285210]] 
 ![![467, 0, 0, 0, 0], ![362, 1, 0, 0, 0], ![183, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![332, 0, 0, 0, 1]] where
  M :=![![![137579, -57318, 249953, -112467, -285210], ![-60276, 25112, -109509, 49274, 124956], ![26408, -11002, 47978, -21587, -54744], ![-11570, 4821, -21019, 9463, 23994], ![10904, -4543, 19810, -8915, -22607]]]
  hmulB := by decide  
  f := ![![![-1391, -2311, 2785, -1226, -3270]], ![![-1080, -1797, 2153, -947, -2526]], ![![-543, -904, 1087, -482, -1290]], ![![-208, -336, 411, -158, -396]], ![![-986, -1643, 1978, -883, -2369]]]
  g := ![![![165916, -57318, 249953, -112467, -285210], ![-72691, 25112, -109509, 49274, 124956], ![31846, -11002, 47978, -21587, -54744], ![-13961, 4821, -21019, 9463, 23994], ![13152, -4543, 19810, -8915, -22607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -1, 12, -5, -12]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![7, -1, 12, -5, -12]] 
 ![![467, 0, 0, 0, 0], ![401, 1, 0, 0, 0], ![314, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![7, -1, 12, -5, -12], ![-2, 2, -4, -1, -6], ![-4, -3, 5, 15, 60], ![30, 11, -18, -100, -390], ![-16, -6, 10, 54, 211]]]
  hmulB := by decide  
  f := ![![![-27, -323, -442, 191, 468]], ![![-23, -277, -380, 164, 402]], ![![-18, -217, -297, 127, 312]], ![![-10, -123, -168, 64, 162]], ![![-3, -35, -48, 23, 55]]]
  g := ![![![-4, -1, 12, -5, -12], ![2, 2, -4, -1, -6], ![-13, -3, 5, 15, 60], ![83, 11, -18, -100, -390], ![-45, -6, 10, 54, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2

def I467N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6, -9, 7, 22]] i)))

def SI467N3: IdealEqSpanCertificate' Table ![![3, 6, -9, 7, 22]] 
 ![![467, 0, 0, 0, 0], ![457, 1, 0, 0, 0], ![367, 0, 1, 0, 0], ![401, 0, 0, 1, 0], ![174, 0, 0, 0, 1]] where
  M :=![![![3, 6, -9, 7, 22], ![8, 10, 5, -22, -80], ![-36, -14, 24, 111, 436], ![214, 75, -117, -705, -2750], ![-116, -41, 62, 383, 1493]]]
  hmulB := by decide  
  f := ![![![-1611, 685, -2985, 1456, 3614]], ![![-1575, 670, -2918, 1425, 3536]], ![![-1267, 540, -2345, 1154, 2858]], ![![-1385, 597, -2550, 1310, 3210]], ![![-600, 253, -1116, 527, 1319]]]
  g := ![![![-13, 6, -9, 7, 22], ![35, 10, 5, -22, -80], ![-263, -14, 24, 111, 436], ![1649, 75, -117, -705, -2750], ![-894, -41, 62, 383, 1493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N3 : Nat.card (O ⧸ I467N3) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N3)

lemma isPrimeI467N3 : Ideal.IsPrime I467N3 := prime_ideal_of_norm_prime hp467.out _ NI467N3
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![35573, 76967, -14164, 4273, 15466]] ![![137579, -57318, 249953, -112467, -285210]]
  ![![-5383, -7487, 5747, -2356, -6362]] where
 M := ![![![-5383, -7487, 5747, -2356, -6362]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![-5383, -7487, 5747, -2356, -6362]] ![![7, -1, 12, -5, -12]]
  ![![-14583, -14576, -27125, 12659, 30796]] where
 M := ![![![-14583, -14576, -27125, 12659, 30796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N2 : IdealMulLeCertificate' Table 
  ![![-14583, -14576, -27125, 12659, 30796]] ![![3, 6, -9, 7, 22]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![-47167, -166719, -164384, 77989, 184932]]]
 hmul := by decide  
 g := ![![![![-101, -357, -352, 167, 396]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1, I467N2, I467N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
    exact isPrimeI467N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0 ⊙ MulI467N1 ⊙ MulI467N2)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2957, -6766, -1034, 634, 1176]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![-2957, -6766, -1034, 634, 1176]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![0, 0, 0, 479, 0], ![15, 259, 360, 249, 1]] where
  M :=![![![-2957, -6766, -1034, 634, 1176], ![-92, -2323, -6040, 2688, 6636], ![1260, 2596, -895, -160, 84], ![404, 1100, 2032, -4119, -8148], ![-390, -986, -738, 1190, 2369]]]
  hmulB := by decide  
  f := ![![![77, 30, -46, -258, -1008]], ![![-492, -181, 264, 1616, 6300]], ![![3068, 1124, -1633, -10064, -39228]], ![![-19100, -6996, 10160, 62647, 244188]], ![![-7865, -2881, 4184, 25797, 100553]]]
  g := ![![![-43, -650, -886, -610, 1176], ![-208, -3593, -5000, -3444, 6636], ![0, -40, -65, -44, 84], ![256, 4408, 6128, 4227, -8148], ![-75, -1283, -1782, -1229, 2369]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 4 2 8 [41, 199, 301, 363, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [256, 305, 420, 385], [381, 201, 91, 227], [437, 451, 447, 346], [0, 1]]
 g := ![![[169, 61, 372, 442], [330, 227, 220, 99], [366, 78, 44, 64], [175, 424, 434, 180], [43, 242, 264, 244], [238, 304, 125], [217, 222, 116, 1], []], ![[135, 223, 86, 26, 423, 393], [284, 268, 440, 406, 92, 22], [31, 128, 31, 156, 193, 128], [86, 336, 260, 54, 393, 289], [212, 316, 39, 220, 97, 412], [169, 241, 64], [164, 252, 122, 225, 367, 173], [3, 303, 241, 191, 195, 2]], ![[430, 122, 302, 70, 359, 85], [434, 222, 475, 231, 422, 67], [472, 261, 462, 454, 451, 340], [23, 257, 42, 413, 41, 418], [285, 35, 315, 342, 151, 451], [390, 123, 245], [450, 419, 272, 347, 275, 229], [274, 375, 464, 385, 389, 382]], ![[56, 120, 230, 458, 127, 165], [144, 223, 131, 161, 392, 77], [285, 380, 208, 115, 451, 122], [290, 322, 431, 132, 432, 56], [241, 267, 375, 296, 96, 442], [416, 159, 218], [250, 405, 27, 141, 323, 189], [29, 450, 225, 107, 437, 211]]]
 h' := ![![[256, 305, 420, 385], [361, 446, 180, 311], [322, 229, 159, 305], [10, 419, 102, 471], [153, 342, 231, 132], [244, 34, 377, 438], [204, 405, 230, 369], [0, 0, 0, 1], [0, 1]], ![[381, 201, 91, 227], [366, 121, 118, 162], [172, 261, 98, 296], [33, 435, 205, 206], [93, 57, 151, 35], [237, 357, 20, 475], [287, 129, 419, 471], [118, 301, 232, 427], [256, 305, 420, 385]], ![[437, 451, 447, 346], [248, 135, 473, 202], [398, 364, 120, 212], [109, 290, 234, 404], [190, 101, 412, 335], [202, 323, 232, 160], [109, 240, 25, 325], [305, 135, 343, 44], [381, 201, 91, 227]], ![[0, 1], [429, 256, 187, 283], [136, 104, 102, 145], [280, 293, 417, 356], [128, 458, 164, 456], [381, 244, 329, 364], [216, 184, 284, 272], [405, 43, 383, 7], [437, 451, 447, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [407, 321, 222], []]
 b := ![[], [], [356, 45, 335, 286], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 4
  hpos := by decide
  P := [41, 199, 301, 363, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5232934821560165, 13542371807286256, 21253033987362783, 102750793484233369, 198440008066399434]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6225121202124325, -107270187301440850, -149096346283750383, -102941150762106943, 198440008066399434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 52643172481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -30, 46, 258, 1008]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-77, -30, 46, 258, 1008]] 
 ![![479, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![171, 0, 1, 0, 0], ![178, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![-77, -30, 46, 258, 1008], ![492, 181, -264, -1616, -6300], ![-3068, -1124, 1633, 10064, 39228], ![19100, 6996, -10160, -62647, -244188], ![-10358, -3794, 5510, 33974, 132425]]]
  hmulB := by decide  
  f := ![![![2957, 6766, 1034, -634, -1176]], ![![599, 1375, 222, -134, -252]], ![![1053, 2410, 371, -226, -420]], ![![1098, 2512, 380, -227, -420]], ![![1575, 3604, 552, -340, -631]]]
  g := ![![![-643, -30, 46, 258, 1008], ![4013, 181, -264, -1616, -6300], ![-24985, -1124, 1633, 10064, 39228], ![155526, 6996, -10160, -62647, -244188], ![-84343, -3794, 5510, 33974, 132425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI479N1 : Nat.card (O ⧸ I479N1) = 479 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI479N1)

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := prime_ideal_of_norm_prime hp479.out _ NI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![-2957, -6766, -1034, 634, 1176]] ![![-77, -30, 46, 258, 1008]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![-479, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3299, -7119, 1372, -423, -1500]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![-3299, -7119, 1372, -423, -1500]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![190, 166, 1, 0, 0], ![115, 393, 0, 1, 0], ![52, 99, 0, 0, 1]] where
  M :=![![![-3299, -7119, 1372, -423, -1500], ![-654, -3722, -6888, 3181, 7734], ![1372, 2527, -1913, 785, 2124], ![554, 2157, 2758, -1312, -3138], ![-476, -1322, -718, 362, 821]]]
  hmulB := by decide  
  f := ![![![39043, -16273, 70954, -31895, -80844]], ![![-17054, 7148, -31114, 13803, 34758]], ![![9434, -3919, 17105, -7749, -19716]], ![![-4545, 1930, -8368, 3598, 8916]], ![![706, -288, 1264, -597, -1549]]]
  g := ![![![-282, 164, 1372, -423, -1500], ![1109, -1799, -6888, 3181, 7734], ![337, -408, -1913, 785, 2124], ![-430, 761, 2758, -1312, -3138], ![106, -217, -718, 362, 821]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 2 2 8 [224, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [369, 486], [0, 1]]
 g := ![![[431, 280], [428, 70], [373, 278], [395], [225], [291, 146], [370, 200], [369, 1]], ![[20, 207], [447, 417], [198, 209], [395], [225], [108, 341], [146, 287], [251, 486]]]
 h' := ![![[369, 486], [67, 188], [212, 94], [431, 256], [367, 450], [74, 472], [397, 111], [134, 64], [0, 1]], ![[0, 1], [285, 299], [321, 393], [417, 231], [350, 37], [383, 15], [448, 376], [374, 423], [369, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [5, 322]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 2
  hpos := by decide
  P := [224, 118, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9494, 14211, 26455, 130476, 276173]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70640, -170422, 26455, 130476, 276173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 75, 114, -53, -128]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![15, 75, 114, -53, -128]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![447, 179, 1, 0, 0], ![342, 61, 0, 1, 0], ![108, 476, 0, 0, 1]] where
  M :=![![![15, 75, 114, -53, -128], ![-22, -38, 44, -19, -50], ![-12, -41, -45, 21, 52], ![10, 9, -30, 0, -2], ![-2, 4, 20, -4, -7]]]
  hmulB := by decide  
  f := ![![![-207, 77, -372, 167, 424]], ![![90, -40, 154, -77, -194]], ![![-157, 56, -285, 125, 318]], ![![-134, 49, -242, 107, 272]], ![![42, -22, 68, -38, -95]]]
  g := ![![![-39, 90, 114, -53, -128], ![-16, 35, 44, -19, -50], ![15, -37, -45, 21, 52], ![28, 13, -30, 0, -2], ![-14, 0, 20, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P1 : CertificateIrreducibleZModOfList' 487 2 2 8 [431, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [420, 486], [0, 1]]
 g := ![![[251, 200], [480, 138], [56, 460], [240], [375], [263, 91], [113, 433], [420, 1]], ![[0, 287], [0, 349], [404, 27], [240], [375], [10, 396], [322, 54], [353, 486]]]
 h' := ![![[420, 486], [95, 423], [214, 25], [411, 66], [347, 78], [118, 146], [484, 401], [144, 162], [0, 1]], ![[0, 1], [0, 64], [0, 462], [372, 421], [478, 409], [76, 341], [402, 86], [4, 325], [420, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [444, 304]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N1 : CertifiedPrimeIdeal' SI487N1 487 where
  n := 2
  hpos := by decide
  P := [431, 67, 1]
  hirr := P487P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-494133, 515987, 1095810, 5479493, 12250600]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7571607, -13061948, 1095810, 5479493, 12250600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N1 B_one_repr
lemma NI487N1 : Nat.card (O ⧸ I487N1) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N1

def I487N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23463, -9774, 42624, -19184, -48656]] i)))

def SI487N2: IdealEqSpanCertificate' Table ![![23463, -9774, 42624, -19184, -48656]] 
 ![![487, 0, 0, 0, 0], ![142, 1, 0, 0, 0], ![290, 0, 1, 0, 0], ![215, 0, 0, 1, 0], ![449, 0, 0, 0, 1]] where
  M :=![![![23463, -9774, 42624, -19184, -48656], ![-10288, 4279, -18670, 8432, 21424], ![4560, -1856, 8151, -3870, -10064], ![-2324, 690, -3402, 2745, 8548], ![2050, -704, 3278, -2140, -6283]]]
  hmulB := by decide  
  f := ![![![-89439, 42962, 768372, -344920, -860912]], ![![-26430, 11635, 223774, -100428, -250720]], ![![-53242, 25376, 456787, -205046, -511800]], ![![-39323, 19332, 339198, -152275, -380052]], ![![-82527, 39506, 708570, -318072, -793907]]]
  g := ![![![30845, -9774, 42624, -19184, -48656], ![-13626, 4279, -18670, 8432, 21424], ![6684, -1856, 8151, -3870, -10064], ![-7273, 690, -3402, 2745, 8548], ![4995, -704, 3278, -2140, -6283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N2 : Nat.card (O ⧸ I487N2) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N2)

lemma isPrimeI487N2 : Ideal.IsPrime I487N2 := prime_ideal_of_norm_prime hp487.out _ NI487N2
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![-3299, -7119, 1372, -423, -1500]] ![![15, 75, 114, -53, -128]]
  ![![89439, -42962, -768372, 344920, 860912]] where
 M := ![![![89439, -42962, -768372, 344920, 860912]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI487N1 : IdealMulLeCertificate' Table 
  ![![89439, -42962, -768372, 344920, 860912]] ![![23463, -9774, 42624, -19184, -48656]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![-487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1, I487N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
    exact isPrimeI487N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0 ⊙ MulI487N1)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![294977, -122915, 535903, -241130, -611494]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![294977, -122915, 535903, -241130, -611494]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![253, 117, 5, 1, 0], ![148, 389, 47, 0, 1]] where
  M :=![![![294977, -122915, 535903, -241130, -611494], ![-129234, 53847, -234811, 105657, 267938], ![56624, -23577, 102880, -46270, -117352], ![-24812, 10354, -45035, 20402, 51644], ![23380, -9747, 42464, -19143, -48521]]]
  hmulB := by decide  
  f := ![![![-25, 24, 43, 115, 466]], ![![236, 90, -97, -798, -3092]], ![![-1496, -562, 788, 4889, 19048]], ![![47, 35, -3, -143, -544]], ![![26, 21, 17, -96, -355]]]
  g := ![![![309169, 541671, 62081, -241130, -611494], ![-135469, -237344, -27202, 105657, 267938], ![59330, 103951, 11914, -46270, -117352], ![-26130, -45756, -5243, 20402, 51644], ![24537, 42983, 4926, -19143, -48521]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [359, 232, 447, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [453, 139, 66], [82, 351, 425], [0, 1]]
 g := ![![[394, 230, 415], [391, 95, 147], [478, 39], [261, 105, 349], [367, 462], [144, 30, 197], [278, 447, 463], [1]], ![[382, 392, 7, 259], [159, 412, 29, 466], [314, 178], [311, 143, 207, 287], [461, 240], [181, 85, 3, 448], [139, 107, 431, 62], [114, 273, 434, 261]], ![[444, 65, 111, 402], [289, 404, 4, 139], [153, 388], [384, 100, 463, 65], [235, 402], [101, 304, 108, 418], [434, 2, 216, 108], [468, 459, 246, 230]]]
 h' := ![![[453, 139, 66], [57, 172, 293], [98, 90, 191], [82, 328, 299], [76, 168, 412], [350, 450, 453], [362, 148, 213], [132, 259, 44], [0, 1]], ![[82, 351, 425], [392, 294, 283], [289, 448, 313], [24, 301, 410], [111, 336, 53], [241, 328, 159], [477, 59, 79], [438, 441, 132], [453, 139, 66]], ![[0, 1], [123, 25, 406], [239, 444, 478], [34, 353, 273], [147, 478, 26], [166, 204, 370], [163, 284, 199], [376, 282, 315], [82, 351, 425]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [419, 50], []]
 b := ![[], [263, 316, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [359, 232, 447, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![853834297, -456814974, -1373584272, -7061044804, -17463946280]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8904200039, 15517638554, 1740808788, -7061044804, -17463946280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -24, -43, -115, -466]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![25, -24, -43, -115, -466]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![359, 486, 1, 0, 0], ![322, 334, 0, 1, 0], ![391, 427, 0, 0, 1]] where
  M :=![![![25, -24, -43, -115, -466], ![-236, -90, 97, 798, 3092], ![1496, 562, -788, -4889, -19048], ![-9270, -3393, 4943, 30387, 118478], ![5026, 1837, -2680, -16483, -64259]]]
  hmulB := by decide  
  f := ![![![-294977, 122915, -535903, 241130, 611494]], ![![129234, -53847, 234811, -105657, -267938]], ![![-87873, 36620, -159621, 71818, 182130]], ![![-105486, 43958, -191627, 86220, 218652]], ![![-122559, 51073, -222640, 100174, 254039]]]
  g := ![![![478, 526, -43, -115, -466], ![-3057, -3328, 97, 798, 3092], ![18954, 20672, -788, -4889, -19048], ![-117909, -128605, 4943, 30387, 118478], ![63951, 69752, -2680, -16483, -64259]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P1 : CertificateIrreducibleZModOfList' 491 2 2 8 [153, 213, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [278, 490], [0, 1]]
 g := ![![[425, 138], [479, 354], [298], [74, 351], [473], [446, 183], [464, 463], [278, 1]], ![[0, 353], [200, 137], [298], [434, 140], [473], [256, 308], [45, 28], [65, 490]]]
 h' := ![![[278, 490], [363, 223], [419, 438], [462, 388], [420, 85], [11, 209], [203, 316], [183, 44], [0, 1]], ![[0, 1], [0, 268], [415, 53], [306, 103], [482, 406], [175, 282], [162, 175], [140, 447], [278, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [275, 323]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N1 : CertifiedPrimeIdeal' SI491N1 491 where
  n := 2
  hpos := by decide
  P := [153, 213, 1]
  hirr := P491P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34267, -11046, 20556, 119752, 454020]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-455185, -496670, 20556, 119752, 454020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N1 B_one_repr
lemma NI491N1 : Nat.card (O ⧸ I491N1) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N1
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![294977, -122915, 535903, -241130, -611494]] ![![25, -24, -43, -115, -466]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![-491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 5, 10, -5, -12]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![13, 5, 10, -5, -12]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![341, 483, 1, 0, 0], ![466, 85, 0, 1, 0], ![380, 34, 0, 0, 1]] where
  M :=![![![13, 5, 10, -5, -12], ![-2, 8, 2, -3, -6], ![0, -5, 5, -13, -24], ![2, -13, -20, -72, -138], ![0, 4, 6, 20, 41]]]
  hmulB := by decide  
  f := ![![![31, -33, -32, 15, 36]], ![![6, 46, -24, 7, 18]], ![![27, 22, -45, 17, 42]], ![![30, -23, -34, 15, 36]], ![![24, -22, -26, 12, 29]]]
  g := ![![![7, -8, 10, -5, -12], ![6, -1, 2, -3, -6], ![27, -1, 5, -13, -24], ![186, 41, -20, -72, -138], ![-54, -12, 6, 20, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 2 2 8 [132, 330, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 498], [0, 1]]
 g := ![![[252, 155], [388, 104], [51], [165], [470, 195], [378, 43], [66, 196], [169, 1]], ![[0, 344], [0, 395], [51], [165], [491, 304], [160, 456], [256, 303], [338, 498]]]
 h' := ![![[169, 498], [181, 244], [162, 64], [126, 71], [335, 313], [4, 368], [270, 404], [147, 485], [0, 1]], ![[0, 1], [0, 255], [0, 435], [149, 428], [338, 186], [320, 131], [183, 95], [276, 14], [169, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [370]]
 b := ![[], [86, 185]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 2
  hpos := by decide
  P := [132, 330, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17806, 20927, 42269, 203026, 451869]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-562629, -106244, 42269, 203026, 451869]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![335, -1163, -5983, 2708, 6708]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![335, -1163, -5983, 2708, 6708]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![435, 258, 1, 0, 0], ![45, 238, 0, 1, 0], ![147, 254, 0, 0, 1]] where
  M :=![![![335, -1163, -5983, 2708, 6708], ![1292, 3043, 253, -195, -300], ![90, 1097, 2758, -1262, -3090], ![-566, -1172, 401, -156, -474], ![204, 251, -678, 301, 775]]]
  hmulB := by decide  
  f := ![![![14429, -6006, 26225, -11757, -29844]], ![![-6330, 2672, -11433, 5420, 13554]], ![![9311, -3856, 16961, -7448, -19014]], ![![-1721, 737, -3088, 1548, 3816]], ![![1031, -411, 1909, -712, -1907]]]
  g := ![![![2996, -1615, -5983, 2708, 6708], ![-112, 121, 253, -195, -300], ![-1380, 751, 2758, -1262, -3090], ![-197, 106, 401, -156, -474], ![336, -187, -678, 301, 775]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [406, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [383, 498], [0, 1]]
 g := ![![[428, 279], [261, 127], [482], [194], [39, 261], [361, 365], [79, 287], [383, 1]], ![[0, 220], [0, 372], [482], [194], [202, 238], [436, 134], [220, 212], [267, 498]]]
 h' := ![![[383, 498], [321, 334], [325, 248], [70, 116], [134, 427], [140, 135], [361, 234], [190, 76], [0, 1]], ![[0, 1], [0, 165], [0, 251], [87, 383], [3, 72], [448, 364], [163, 265], [356, 423], [383, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [402]]
 b := ![[], [181, 201]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal' SI499N1 499 where
  n := 2
  hpos := by decide
  P := [406, 116, 1]
  hirr := P499P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1712, 5638, 8968, 43299, 83323]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36272, -67690, 8968, 43299, 83323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N1 B_one_repr
lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1183, 493, -2149, 968, 2454]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![-1183, 493, -2149, 968, 2454]] 
 ![![499, 0, 0, 0, 0], ![257, 1, 0, 0, 0], ![318, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-1183, 493, -2149, 968, 2454], ![518, -215, 943, -417, -1062], ![-228, 101, -404, 226, 540], ![88, -2, 239, 198, 312], ![-90, 29, -186, 1, 49]]]
  hmulB := by decide  
  f := ![![![-12097, -13914, 42803, -18777, -47874]], ![![-6251, -7228, 22000, -9649, -24606]], ![![-7702, -8866, 27230, -11945, -30456]], ![![-2656, -3039, 9447, -4145, -10566]], ![![-54, -67, 176, -77, -197]]]
  g := ![![![890, 493, -2149, 968, 2454], ![-393, -215, 943, -417, -1062], ![153, 101, -404, 226, 540], ![-196, -2, 239, 198, 312], ![103, 29, -186, 1, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![13, 5, 10, -5, -12]] ![![335, -1163, -5983, 2708, 6708]]
  ![![12097, 13914, -42803, 18777, 47874]] where
 M := ![![![12097, 13914, -42803, 18777, 47874]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![12097, 13914, -42803, 18777, 47874]] ![![-1183, 493, -2149, 968, 2454]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1, I499N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
    exact isPrimeI499N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0 ⊙ MulI499N1)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![534201, -222559, 970535, -436694, -1107432]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![534201, -222559, 970535, -436694, -1107432]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![0, 0, 503, 0, 0], ![188, 305, 168, 1, 0], ![106, 194, 441, 0, 1]] where
  M :=![![![534201, -222559, 970535, -436694, -1107432], ![-234044, 97507, -425209, 191329, 485196], ![102538, -42715, 186298, -83792, -212514], ![-44930, 18746, -81577, 36918, 93474], ![42340, -17647, 76910, -34661, -87859]]]
  hmulB := by decide  
  f := ![![![-73, 104, 839, -377, -936]], ![![-182, -450, -91, 46, 78]], ![![-14, -136, -390, 223, 606]], ![![-142, -279, 128, -39, -102]], ![![-98, -271, -200, 134, 365]]]
  g := ![![![397655, 691473, 1118713, -436694, -1107432], ![-174224, -302954, -490139, 191329, 485196], ![76306, 132687, 214676, -83792, -212514], ![-33586, -58400, -94445, 36918, 93474], ![31554, 54868, 88759, -34661, -87859]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 3 2 8 [353, 331, 253, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 138, 95], [122, 364, 408], [0, 1]]
 g := ![![[249, 499, 486], [61, 165, 22], [178, 368, 48], [152, 253], [379, 346, 134], [25, 180, 26], [403, 298, 128], [1]], ![[268, 451, 41, 466], [489, 443, 150, 146], [200, 437, 304, 297], [50, 373], [432, 461, 76, 205], [422, 164, 394, 92], [469, 379, 302, 205], [484, 433, 426, 263]], ![[109, 428, 158, 251], [48, 430, 358, 40], [468, 440, 325, 478], [346, 150], [182, 226, 268, 245], [464, 133, 351, 333], [384, 230, 336, 153], [493, 96, 164, 240]]]
 h' := ![![[128, 138, 95], [96, 204, 363], [41, 113, 81], [286, 106, 78], [11, 18, 399], [229, 166, 188], [90, 203, 480], [150, 172, 250], [0, 1]], ![[122, 364, 408], [439, 271, 109], [445, 11, 482], [352, 32, 234], [30, 484, 70], [90, 290, 201], [172, 371, 350], [313, 337, 201], [128, 138, 95]], ![[0, 1], [266, 28, 31], [226, 379, 443], [158, 365, 191], [171, 1, 34], [327, 47, 114], [165, 432, 176], [27, 497, 52], [122, 364, 408]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [491, 134], []]
 b := ![[], [430, 333, 491], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 3
  hpos := by decide
  P := [353, 331, 253, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56073620, -9500483, 43018415, 245047849, 810827502]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-262570148, -461331272, -792644033, 245047849, 810827502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 127263527 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 104, 839, -377, -936]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![-73, 104, 839, -377, -936]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![214, 335, 1, 0, 0], ![239, 158, 0, 1, 0], ![29, 466, 0, 0, 1]] where
  M :=![![![-73, 104, 839, -377, -936], ![-182, -450, -91, 46, 78], ![-14, -136, -390, 223, 606], ![160, 209, -73, -235, -936], ![-74, -61, 110, 97, 433]]]
  hmulB := by decide  
  f := ![![![534201, -222559, 970535, -436694, -1107432]], ![![-234044, 97507, -425209, 191329, 485196]], ![![71604, -29832, 130091, -58531, -148434]], ![![180219, -75083, 327422, -147322, -373602]], ![![-185945, 77468, -337823, 152009, 385483]]]
  g := ![![![-124, 427, 839, -377, -936], ![12, -27, -91, 46, 78], ![25, -372, -390, 223, 606], ![197, 990, -73, -235, -936], ![-118, -505, 110, 97, 433]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P1 : CertificateIrreducibleZModOfList' 503 2 2 8 [152, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [342, 502], [0, 1]]
 g := ![![[375, 392], [413, 262], [409, 150], [361], [297, 73], [210, 113], [148, 378], [342, 1]], ![[138, 111], [483, 241], [403, 353], [361], [113, 430], [125, 390], [153, 125], [181, 502]]]
 h' := ![![[342, 502], [99, 186], [204, 187], [238, 469], [126, 484], [272, 24], [139, 144], [328, 116], [0, 1]], ![[0, 1], [333, 317], [277, 316], [179, 34], [167, 19], [432, 479], [93, 359], [263, 387], [342, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [432]]
 b := ![[], [286, 216]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N1 : CertifiedPrimeIdeal' SI503N1 503 where
  n := 2
  hpos := by decide
  P := [152, 161, 1]
  hirr := P503P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53018, 32675, 90308, 462767, 1123372]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-323177, -1246181, 90308, 462767, 1123372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N1 B_one_repr
lemma NI503N1 : Nat.card (O ⧸ I503N1) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N1
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![534201, -222559, 970535, -436694, -1107432]] ![![-73, 104, 839, -377, -936]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16661, 41829, 11299, -6190, -12924]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![16661, 41829, 11299, -6190, -12924]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![473, 434, 165, 1, 0], ![59, 409, 374, 0, 1]] where
  M :=![![![16661, 41829, 11299, -6190, -12924], ![-544, 10471, 36183, -16387, -40272], ![-7498, -16931, 1582, -764, -3630], ![-2102, -8262, -15593, 10374, 29622], ![2404, 6493, 5714, -4453, -13003]]]
  hmulB := by decide  
  f := ![![![174169, -72536, 316481, -142191, -360732]], ![![-76350, 31978, -138377, 63626, 160422]], ![![33170, -12724, 62434, -19267, -54882]], ![![107471, -44237, 196318, -84003, -215982]], ![![-16761, 7923, -28588, 20438, 46661]]]
  g := ![![![7283, 15745, 11525, -6190, -12924], ![19895, 46353, 34974, -16387, -40272], ![1116, 3535, 2918, -764, -3630], ![-13078, -32664, -25159, 10374, 29622], ![5650, 14258, 11009, -4453, -13003]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 3 2 8 [128, 177, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [432, 470, 180], [490, 38, 329], [0, 1]]
 g := ![![[442, 426, 486], [129, 256], [257, 489, 102], [472, 63, 447], [121, 439, 187], [360, 321, 357], [116, 296, 54], [1]], ![[189, 439, 427, 67], [55, 409], [360, 272, 452, 127], [228, 308, 166, 125], [453, 467, 166, 9], [159, 236, 111, 30], [405, 338, 15, 253], [35, 119, 237, 387]], ![[36, 57, 360, 500], [177, 37], [407, 44, 437, 116], [502, 502, 367, 372], [351, 411, 103, 84], [57, 464, 471, 158], [309, 375, 33, 480], [61, 232, 291, 122]]]
 h' := ![![[432, 470, 180], [376, 19, 221], [189, 438, 16], [155, 199, 155], [291, 381, 363], [239, 489, 291], [422, 211, 322], [381, 332, 413], [0, 1]], ![[490, 38, 329], [62, 3, 111], [78, 13, 44], [210, 25, 481], [348, 364, 425], [284, 410, 332], [313, 186, 334], [141, 25, 122], [432, 470, 180]], ![[0, 1], [263, 487, 177], [280, 58, 449], [157, 285, 382], [332, 273, 230], [326, 119, 395], [236, 112, 362], [94, 152, 483], [490, 38, 329]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [260, 103], []]
 b := ![[], [181, 384, 302], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 3
  hpos := by decide
  P := [128, 177, 96, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40847574, 59011056, 110105291, 543515849, 1151641978]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-638645817, -1388700268, -1022169174, 543515849, 1151641978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 131872229 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-174169, 72536, -316481, 142191, 360732]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-174169, 72536, -316481, 142191, 360732]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![283, 344, 1, 0, 0], ![376, 35, 0, 1, 0], ![28, 338, 0, 0, 1]] where
  M :=![![![-174169, 72536, -316481, 142191, 360732], ![76350, -31978, 138377, -63626, -160422], ![-33170, 12724, -62434, 19267, 54882], ![16348, -13903, 15643, -64187, -123780], ![-14250, 7795, -22206, 24965, 53093]]]
  hmulB := by decide  
  f := ![![![-16661, -41829, -11299, 6190, 12924]], ![![544, -10471, -36183, 16387, 40272]], ![![-8881, -30300, -30739, 14518, 34410]], ![![-12266, -31603, -10804, 5679, 12258]], ![![-560, -9267, -24660, 11231, 27479]]]
  g := ![![![50738, -35289, -316481, 142191, 360732], ![-20961, 17320, 138377, -63626, -160422], ![17396, 4451, -62434, 19267, 54882], ![45559, 76010, 15643, -64187, -123780], ![-9044, -21950, -22206, 24965, 53093]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [267, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [361, 508], [0, 1]]
 g := ![![[134, 16], [81], [372, 417], [392, 452], [279, 37], [277, 410], [419, 402], [361, 1]], ![[311, 493], [81], [245, 92], [175, 57], [402, 472], [168, 99], [476, 107], [213, 508]]]
 h' := ![![[361, 508], [440, 4], [440, 9], [190, 442], [330, 31], [355, 449], [107, 135], [323, 259], [0, 1]], ![[0, 1], [357, 505], [126, 500], [435, 67], [323, 478], [73, 60], [487, 374], [166, 250], [361, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [432]]
 b := ![[], [205, 216]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N1 : CertifiedPrimeIdeal' SI509N1 509 where
  n := 2
  hpos := by decide
  P := [267, 148, 1]
  hirr := P509P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79112, 68812, 155156, 800264, 1845368]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-779092, -1385164, 155156, 800264, 1845368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N1 B_one_repr
lemma NI509N1 : Nat.card (O ⧸ I509N1) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![16661, 41829, 11299, -6190, -12924]] ![![-174169, 72536, -316481, 142191, 360732]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![-509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135, -331, -458, 301, 676]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![-135, -331, -458, 301, 676]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![0, 0, 521, 0, 0], ![0, 0, 0, 521, 0], ![184, 455, 192, 49, 1]] where
  M :=![![![-135, -331, -458, 301, 676], ![74, 166, -104, 603, 1150], ![-56, 677, 825, 3247, 5776], ![-718, 3191, 4642, 21368, 38182], ![178, -868, -1264, -5576, -9949]]]
  hmulB := by decide  
  f := ![![![-7, 5, -12, 7, 20]], ![![6, 0, 6, -13, -46]], ![![-20, -7, 7, 61, 236]], ![![114, 41, -60, -372, -1450]], ![![6, 3, -2, -21, -81]]]
  g := ![![![-239, -591, -250, -63, 676], ![-406, -1004, -424, -107, 1150], ![-2040, -5043, -2127, -537, 5776], ![-13486, -33339, -14062, -3550, 38182], ![3514, 8687, 3664, 925, -9949]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 4 2 9 [441, 40, 518, 432, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 94, 247, 499], [125, 133, 357, 202], [337, 293, 438, 341], [0, 1]]
 g := ![![[80, 226, 295, 2], [204, 320, 55], [15, 106, 212], [15, 353, 267, 261], [139, 117, 353], [366, 389, 490], [390, 69, 106], [1], []], ![[469, 14, 398, 512, 386, 123], [248, 21, 45], [456, 244, 416], [137, 299, 54, 403, 440, 474], [6, 270, 13], [344, 284, 53], [360, 7, 202], [62, 353, 101], [464, 427, 484]], ![[179, 91, 519, 468, 322, 333], [346, 37, 416], [21, 330, 160], [321, 420, 377, 3, 182, 260], [460, 262, 81], [57, 487, 464], [161, 254, 49], [312, 194, 449], [147, 97, 166]], ![[76, 403, 491, 460, 431, 200], [268, 15, 4], [445, 47, 456], [4, 140, 180, 138, 194, 246], [209, 180, 416], [112, 298, 477], [67, 226, 155], [180, 26, 325], [276, 48, 98]]]
 h' := ![![[148, 94, 247, 499], [140, 456, 380, 249], [114, 218, 193, 497], [158, 45, 28, 279], [226, 377, 479, 385], [33, 256, 214, 443], [88, 192, 113, 392], [80, 481, 3, 89], [0, 0, 1], [0, 1]], ![[125, 133, 357, 202], [327, 152, 244, 258], [90, 475, 248, 76], [275, 98, 472, 471], [104, 224, 282, 222], [183, 133, 436, 137], [167, 128, 479, 121], [148, 188, 404, 413], [151, 181, 259, 100], [148, 94, 247, 499]], ![[337, 293, 438, 341], [419, 259, 479, 59], [450, 94, 125, 471], [401, 397, 162, 224], [249, 252, 112, 431], [490, 491, 357, 512], [180, 173, 249, 166], [357, 342, 405, 514], [293, 223, 76, 64], [125, 133, 357, 202]], ![[0, 1], [100, 175, 460, 476], [208, 255, 476, 519], [515, 502, 380, 68], [319, 189, 169, 4], [154, 162, 35, 471], [234, 28, 201, 363], [105, 31, 230, 26], [189, 117, 185, 357], [337, 293, 438, 341]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [498, 18, 8], []]
 b := ![[], [], [127, 89, 234, 392], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 4
  hpos := by decide
  P := [441, 40, 518, 432, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6134872181, 11503821771, 19691935643, 96251866608, 195436147693]
  a := ![-2, 3, -1, 18, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69033370533, -170656321264, -71984737853, -18196006469, 195436147693]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 73680216481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -5, 12, -7, -20]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![7, -5, 12, -7, -20]] 
 ![![521, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![235, 0, 1, 0, 0], ![315, 0, 0, 1, 0], ![202, 0, 0, 0, 1]] where
  M :=![![![7, -5, 12, -7, -20], ![-6, 0, -6, 13, 46], ![20, 7, -7, -61, -236], ![-114, -41, 60, 372, 1450], ![62, 22, -32, -202, -787]]]
  hmulB := by decide  
  f := ![![![135, 331, 458, -301, -676]], ![![11, 27, 38, -26, -58]], ![![61, 148, 205, -142, -316]], ![![83, 194, 268, -223, -482]], ![![52, 130, 180, -106, -243]]]
  g := ![![![7, -5, 12, -7, -20], ![-23, 0, -6, 13, 46], ![131, 7, -7, -61, -236], ![-811, -41, 60, 372, 1450], ![440, 22, -32, -202, -787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N1)

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := prime_ideal_of_norm_prime hp521.out _ NI521N1
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![-135, -331, -458, 301, 676]] ![![7, -5, 12, -7, -20]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![-521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2563281, -1067912, 4656954, -2095418, -5313856]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![2563281, -1067912, 4656954, -2095418, -5313856]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![148, 82, 76, 1, 0], ![519, 208, 419, 0, 1]] where
  M :=![![![2563281, -1067912, 4656954, -2095418, -5313856], ![-1123020, 467863, -2040310, 917984, 2327996], ![492028, -205036, 893819, -402558, -1020604], ![-215488, 89470, -392106, 173957, 442832], ![203136, -84550, 369216, -165482, -420095]]]
  hmulB := by decide  
  f := ![![![-237, -420, 234, 2, 104]], ![![100, -235, -518, -356, -1684]], ![![-972, -256, 381, 3534, 13676]], ![![-180, -188, 34, 417, 1592]], ![![-981, -718, 335, 2714, 10477]]]
  g := ![![![5871083, 2439844, 4570582, -2095418, -5313856], ![-2572112, -1068891, -2002366, 917984, 2327996], ![1127656, 468624, 877861, -402558, -1020604], ![-489084, -203220, -380802, 173957, 442832], ![464099, 192858, 361311, -165482, -420095]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 3 2 9 [213, 40, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [180, 277, 308], [172, 245, 215], [0, 1]]
 g := ![![[338, 30, 66], [313, 122, 190], [520, 391], [384, 134, 410], [150, 473], [369, 141], [243, 247], [352, 1], []], ![[146, 321, 396, 4], [482, 275, 78, 44], [8, 451], [339, 174, 464, 91], [355, 465], [86, 296], [112, 102], [398, 403], [281, 201]], ![[469, 79, 185, 414], [201, 229, 444, 3], [431, 153], [111, 113, 415, 35], [172, 54], [423, 240], [319, 515], [449, 371], [374, 201]]]
 h' := ![![[180, 277, 308], [275, 354, 211], [415, 442, 425], [319, 204, 310], [134, 30, 55], [154, 508, 280], [469, 428, 229], [336, 351, 436], [0, 0, 1], [0, 1]], ![[172, 245, 215], [354, 242, 166], [38, 520, 204], [255, 230, 187], [290, 181, 226], [283, 485, 174], [351, 193, 172], [103, 151, 498], [266, 166, 245], [180, 277, 308]], ![[0, 1], [206, 450, 146], [416, 84, 417], [395, 89, 26], [415, 312, 242], [502, 53, 69], [301, 425, 122], [236, 21, 112], [130, 357, 277], [172, 245, 215]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 393], []]
 b := ![[], [289, 83, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 3
  hpos := by decide
  P := [213, 40, 171, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70755069, 214011079, 324285964, 1560396711, 2946082692]
  a := ![-5, 4, 10, 49, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3365251215, -1415915333, -2586375740, 1560396711, 2946082692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 143055667 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, 530, 442, -212, -498]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![169, 530, 442, -212, -498]] 
 ![![523, 0, 0, 0, 0], ![142, 1, 0, 0, 0], ![233, 0, 1, 0, 0], ![386, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![169, 530, 442, -212, -498], ![-74, -43, 392, -174, -438], ![-90, -248, -127, 62, 138], ![14, -28, -200, 99, 258], ![12, 58, 102, -52, -133]]]
  hmulB := by decide  
  f := ![![![-120485, 50190, -218906, 98460, 249714]], ![![-32612, 13585, -59252, 26650, 67590]], ![![-53721, 22378, -97605, 43898, 111336]], ![![-88904, 37032, -161532, 72635, 184230]], ![![-28815, 12004, -52352, 23552, 59729]]]
  g := ![![![-65, 530, 442, -212, -498], ![70, -43, 392, -174, -438], ![45, -248, -127, 62, 138], ![-38, -28, -200, 99, 258], ![9, 58, 102, -52, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N1 : Nat.card (O ⧸ I523N1) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N1)

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := prime_ideal_of_norm_prime hp523.out _ NI523N1

def I523N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -2, 0, 10, 38]] i)))

def SI523N2: IdealEqSpanCertificate' Table ![![-3, -2, 0, 10, 38]] 
 ![![523, 0, 0, 0, 0], ![305, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![398, 0, 0, 1, 0], ![448, 0, 0, 0, 1]] where
  M :=![![![-3, -2, 0, 10, 38], ![18, 7, -10, -58, -226], ![-110, -40, 59, 360, 1406], ![686, 250, -366, -2257, -8782], ![-372, -136, 198, 1222, 4759]]]
  hmulB := by decide  
  f := ![![![8007, -2610, 14172, -6394, -16174]], ![![4663, -1519, 8254, -3724, -9420]], ![![1059, -346, 1875, -846, -2140]], ![![6092, -1986, 10782, -4865, -12306]], ![![6860, -2236, 12142, -5478, -13857]]]
  g := ![![![-39, -2, 0, 10, 38], ![235, 7, -10, -58, -226], ![-1463, -40, 59, 360, 1406], ![9144, 250, -366, -2257, -8782], ![-4954, -136, 198, 1222, 4759]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N2 : Nat.card (O ⧸ I523N2) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N2)

lemma isPrimeI523N2 : Ideal.IsPrime I523N2 := prime_ideal_of_norm_prime hp523.out _ NI523N2
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![2563281, -1067912, 4656954, -2095418, -5313856]] ![![169, 530, 442, -212, -498]]
  ![![-8007, 2610, -14172, 6394, 16174]] where
 M := ![![![-8007, 2610, -14172, 6394, 16174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI523N1 : IdealMulLeCertificate' Table 
  ![![-8007, 2610, -14172, 6394, 16174]] ![![-3, -2, 0, 10, 38]]
  ![![523, 0, 0, 0, 0]] where
 M := ![![![-523, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC523 : ContainsPrimesAboveP 523 ![I523N0, I523N1, I523N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
    exact isPrimeI523N1
    exact isPrimeI523N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 523 (by decide) (𝕀 ⊙ MulI523N0 ⊙ MulI523N1)


lemma PB953I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB953I10 : PrimesBelowBoundCertificateInterval O 463 523 953 where
  m := 9
  g := ![4, 2, 3, 2, 3, 2, 2, 2, 3]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB953I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2, I467N3]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1, I487N2]
    · exact ![I491N0, I491N1]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1]
    · exact ![I509N0, I509N1]
    · exact ![I521N0, I521N1]
    · exact ![I523N0, I523N1, I523N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![218089, 467, 467, 467]
    · exact ![52643172481, 479]
    · exact ![237169, 237169, 487]
    · exact ![118370771, 241081]
    · exact ![249001, 249001, 499]
    · exact ![127263527, 253009]
    · exact ![131872229, 259081]
    · exact ![73680216481, 521]
    · exact ![143055667, 523, 523]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
      exact NI467N3
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
      exact NI487N2
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
      exact NI499N2
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
      exact NI523N2
  β := ![I467N1, I467N2, I467N3, I479N1, I487N2, I499N2, I521N1, I523N1, I523N2]
  Il := ![[I467N1, I467N2, I467N3], [I479N1], [I487N2], [], [I499N2], [], [], [I521N1], [I523N1, I523N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
