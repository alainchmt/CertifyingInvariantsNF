
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 0, 0, 0, 0]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![421, 0, 0, 0, 0]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]] where
  M :=![![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![0, 0, 0, 421, 0], ![0, 0, 0, 0, 421]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 5 2 8 [11, 11, 266, 157, 316, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [192, 414, 31, 353, 378], [316, 375, 100, 41, 28], [267, 92, 266, 280, 30], [172, 381, 24, 168, 406], [0, 1]]
 g := ![![[327, 99, 48, 199, 4], [165, 157, 208, 124], [78, 180, 270, 346, 346], [13, 219, 38, 266], [67, 413, 286, 190], [231, 4, 123, 172, 190], [105, 1], []], ![[273, 290, 364, 33, 57, 234, 410, 164], [389, 63, 16, 33], [369, 175, 186, 14, 64, 230, 119, 253], [31, 158, 125, 217], [403, 33, 153, 55], [4, 257, 317, 355, 270, 119, 402, 304], [113, 398, 156, 175], [97, 290, 195, 342, 153, 40, 215, 62]], ![[313, 346, 135, 77, 178, 408, 209, 313], [53, 125, 103, 385], [328, 40, 365, 173, 376, 8, 31, 252], [274, 234, 43, 152], [197, 171, 412, 363], [100, 263, 319, 183, 75, 221, 308, 109], [404, 14, 368, 142], [49, 88, 140, 55, 214, 291, 8, 60]], ![[391, 98, 249, 329, 99, 0, 387, 298], [179, 163, 53, 139], [274, 309, 398, 98, 416, 123, 177, 6], [414, 382, 386, 254], [187, 296, 353, 289], [83, 297, 259, 319, 141, 312, 22, 88], [103, 389, 345, 49], [335, 162, 257, 133, 58, 306, 291, 56]], ![[249, 96, 190, 326, 137, 372, 119, 400], [284, 111, 314, 225], [253, 26, 99, 164, 74, 116, 322, 140], [399, 113, 58, 85], [239, 64, 397, 308], [310, 125, 187, 3, 102, 44, 110, 131], [405, 357, 259, 64], [147, 2, 102, 117, 3, 261, 258, 414]]]
 h' := ![![[192, 414, 31, 353, 378], [125, 304, 312, 371, 419], [405, 64, 371, 112, 236], [139, 65, 188, 286, 205], [330, 210, 24, 257, 275], [406, 238, 209, 187, 78], [108, 97, 266, 89, 343], [0, 0, 0, 1], [0, 1]], ![[316, 375, 100, 41, 28], [240, 288, 315, 248, 171], [272, 409, 172, 262, 36], [69, 400, 279, 0, 300], [350, 365, 35, 176, 304], [346, 221, 237, 283, 359], [377, 214, 287, 167, 69], [232, 28, 183, 52, 177], [192, 414, 31, 353, 378]], ![[267, 92, 266, 280, 30], [196, 223, 181, 245, 232], [217, 103, 119, 157, 247], [12, 182, 175, 56, 3], [105, 248, 266, 110, 75], [194, 176, 271, 71, 28], [236, 180, 351, 229, 414], [7, 221, 62, 219, 259], [316, 375, 100, 41, 28]], ![[172, 381, 24, 168, 406], [382, 25, 231, 31, 173], [81, 395, 376, 232, 308], [306, 377, 107, 268, 40], [93, 74, 294, 262, 268], [179, 409, 184, 263, 404], [355, 7, 207, 391, 118], [15, 335, 199, 403, 414], [267, 92, 266, 280, 30]], ![[0, 1], [350, 2, 224, 368, 268], [37, 292, 225, 79, 15], [129, 239, 93, 232, 294], [27, 366, 223, 37, 341], [69, 219, 362, 38, 394], [90, 344, 152, 387, 319], [309, 258, 398, 167, 413], [172, 381, 24, 168, 406]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 137, 289, 32], [], [], []]
 b := ![[], [409, 234, 110, 128, 363], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 5
  hpos := by decide
  P := [11, 11, 266, 157, 316, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1030476525023374, -2303604831988413, -3751273924003359, -18223139333044484, -35986848798468015]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2447687707894, -5471745444153, -8910389368179, -43285366586804, -85479450827715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 13225450646101 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def PBC421 : ContainsPrimesAboveP 421 ![I421N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![421, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 421 (by decide) 𝕀

instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135237, -56338, 245658, -110586, -280506]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![135237, -56338, 245658, -110586, -280506]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![0, 0, 0, 431, 0], ![355, 243, 155, 284, 1]] where
  M :=![![![135237, -56338, 245658, -110586, -280506], ![-59334, 24651, -107590, 48732, 123990], ![26526, -10602, 46857, -23086, -61086], ![-14914, 3440, -18774, 20911, 68850], ![12638, -3762, 18448, -15060, -46771]]]
  hmulB := by decide  
  f := ![![![35, 90, 34, -26, -54]], ![![-2, 9, 66, -84, -174]], ![![-6, -86, -69, -318, -570]], ![![66, -324, -470, -2055, -3666]], ![![69, -165, -269, -1536, -2761]]]
  g := ![![![231357, 158020, 101448, 184578, -280506], ![-102264, -69849, -44840, -81588, 123990], ![50376, 34416, 22077, 40198, -61086], ![-56744, -38810, -24804, -45319, 68850], ![38553, 26361, 16863, 30784, -46771]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 4 2 8 [183, 118, 339, 155, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [239, 80, 143, 300], [150, 158, 226, 95], [318, 192, 62, 36], [0, 1]]
 g := ![![[319, 2, 308, 297], [49, 338, 234, 8], [330, 272, 127, 174], [41, 418, 275, 125], [290, 61, 276], [25, 336, 303, 240], [412, 276, 1], []], ![[28, 50, 316, 70, 118, 116], [139, 221, 275, 398, 63, 61], [399, 149, 51, 406, 84, 69], [428, 390, 209, 12, 133, 304], [414, 3, 120], [126, 168, 330, 182, 426, 149], [296, 11, 149], [427, 230, 282, 386, 245, 5]], ![[36, 308, 399, 424, 168, 122], [245, 282, 76, 284, 134, 357], [365, 350, 203, 350, 58, 61], [168, 232, 99, 1, 59, 49], [386, 118, 198], [244, 262, 365, 129, 286, 57], [221, 205, 69], [63, 123, 233, 423, 165, 116]], ![[69, 393, 291, 67, 187, 76], [269, 300, 229, 362, 291, 225], [78, 286, 307, 385, 79, 30], [213, 290, 69, 90, 303, 171], [32, 398, 403], [323, 277, 356, 240, 239, 5], [283, 174, 123], [412, 248, 385, 347, 196, 108]]]
 h' := ![![[239, 80, 143, 300], [84, 376, 137, 177], [381, 14, 272, 55], [255, 25, 147, 164], [346, 358, 18, 43], [166, 191, 216, 172], [29, 6, 412, 204], [0, 0, 0, 1], [0, 1]], ![[150, 158, 226, 95], [343, 178, 120, 294], [207, 108, 328, 324], [99, 301, 272, 17], [80, 219, 417, 256], [88, 135, 10, 219], [101, 121, 366, 201], [295, 412, 106, 48], [239, 80, 143, 300]], ![[318, 192, 62, 36], [262, 188, 193, 38], [142, 204, 149, 265], [416, 85, 275, 124], [364, 412, 350, 249], [230, 115, 284, 206], [294, 426, 15, 355], [378, 132, 334, 86], [150, 158, 226, 95]], ![[0, 1], [357, 120, 412, 353], [31, 105, 113, 218], [100, 20, 168, 126], [343, 304, 77, 314], [335, 421, 352, 265], [108, 309, 69, 102], [120, 318, 422, 296], [318, 192, 62, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [144, 271, 305], []]
 b := ![[], [], [172, 149, 266, 269], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 4
  hpos := by decide
  P := [183, 118, 339, 155, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5255363297506876, 13586266496777484, 21327221533838751, 103112855855258798, 199170141183372462]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-164061845669129306, -112261619584832322, -71577829841969589, -131000480835783110, 199170141183372462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 34507149121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 90, 34, -26, -54]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![35, 90, 34, -26, -54]] 
 ![![431, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![349, 0, 1, 0, 0], ![375, 0, 0, 1, 0], ![388, 0, 0, 0, 1]] where
  M :=![![![35, 90, 34, -26, -54], ![-2, 9, 66, -84, -174], ![-6, -86, -69, -318, -570], ![66, -324, -470, -2055, -3666], ![-14, 94, 128, 536, 955]]]
  hmulB := by decide  
  f := ![![![135237, -56338, 245658, -110586, -280506]], ![![49125, -20465, 89236, -40170, -101892]], ![![109569, -45644, 199029, -89600, -227280]], ![![117631, -49010, 213696, -96169, -243900]], ![![121774, -50726, 221192, -99588, -252629]]]
  g := ![![![11, 90, 34, -26, -54], ![173, 9, 66, -84, -174], ![877, -86, -69, -318, -570], ![5587, -324, -470, -2055, -3666], ![-1464, 94, 128, 536, 955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![135237, -56338, 245658, -110586, -280506]] ![![35, 90, 34, -26, -54]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2795, -1160, 5084, -2260, -5750]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![2795, -1160, 5084, -2260, -5750]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![226, 96, 1, 0, 0], ![387, 103, 0, 1, 0], ![108, 416, 0, 0, 1]] where
  M :=![![![2795, -1160, 5084, -2260, -5750], ![-1230, 535, -2190, 1164, 2830], ![502, -66, 1197, 618, 778], ![-458, 1120, 1010, 7035, 12730], ![280, -360, 26, -1974, -3667]]]
  hmulB := by decide  
  f := ![![![-45, -440, -920, 344, 730]], ![![42, 299, -138, 548, 2038]], ![![-12, -162, -511, 294, 806]], ![![-43, -327, -848, 479, 1298]], ![![36, 180, -366, 590, 2053]]]
  g := ![![![807, 4932, 5084, -2260, -5750], ![-606, -2509, -2190, 1164, 2830], ![-1370, -1160, 1197, 618, 778], ![-9991, -14125, 1010, 7035, 12730], ![2666, 3986, 26, -1974, -3667]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 2 2 8 [367, 220, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 432], [0, 1]]
 g := ![![[141, 164], [432], [177], [111], [177, 106], [198, 235], [34], [213, 1]], ![[0, 269], [432], [177], [111], [239, 327], [25, 198], [34], [426, 432]]]
 h' := ![![[213, 432], [267, 200], [375, 254], [46, 266], [424, 120], [78, 381], [181, 318], [202, 403], [0, 1]], ![[0, 1], [0, 233], [352, 179], [414, 167], [4, 313], [260, 52], [367, 115], [307, 30], [213, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [9, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 2
  hpos := by decide
  P := [367, 220, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8943, 13905, 25741, 126804, 267707]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-193561, -293035, 25741, 126804, 267707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![387, 685, -395, 158, 438]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![387, 685, -395, 158, 438]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![429, 314, 1, 0, 0], ![390, 124, 0, 1, 0], ![81, 154, 0, 0, 1]] where
  M :=![![![387, 685, -395, 158, 438], ![122, 545, 721, -337, -810], ![-136, -215, 344, -148, -384], ![-88, -284, -275, 132, 312], ![62, 151, 46, -25, -53]]]
  hmulB := by decide  
  f := ![![![-25, -16, 35, 109, 426]], ![![208, 84, -115, -668, -2664]], ![![123, 44, -47, -366, -1470]], ![![56, 17, -11, -153, -618]], ![![59, 23, -29, -184, -737]]]
  g := ![![![168, 87, -395, 158, 438], ![-259, -137, 721, -337, -810], ![-136, -71, 344, -148, -384], ![95, 50, -275, 132, 312], ![-13, -7, 46, -25, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P1 : CertificateIrreducibleZModOfList' 433 2 2 8 [30, 236, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [197, 432], [0, 1]]
 g := ![![[412, 389], [398], [179], [229], [342, 264], [244, 331], [109], [197, 1]], ![[404, 44], [398], [179], [229], [390, 169], [68, 102], [109], [394, 432]]]
 h' := ![![[197, 432], [57, 186], [90, 239], [162, 79], [132, 82], [41, 162], [349, 214], [152, 242], [0, 1]], ![[0, 1], [327, 247], [409, 194], [137, 354], [265, 351], [346, 271], [73, 219], [196, 191], [197, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [376]]
 b := ![[], [101, 188]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N1 : CertifiedPrimeIdeal' SI433N1 433 where
  n := 2
  hpos := by decide
  P := [30, 236, 1]
  hirr := P433P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-498928, 519874, 1104260, 5518363, 12343043]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8374537, -6769800, 1104260, 5518363, 12343043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N1 B_one_repr
lemma NI433N1 : Nat.card (O ⧸ I433N1) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N1

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-388283, 161766, -705430, 317410, 804934]] i)))

def SI433N2: IdealEqSpanCertificate' Table ![![-388283, 161766, -705430, 317410, 804934]] 
 ![![433, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![337, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![388, 0, 0, 0, 1]] where
  M :=![![![-388283, 161766, -705430, 317410, 804934], ![170114, -70873, 309062, -139064, -352658], ![-74530, 31050, -135407, 60922, 154498], ![32654, -13608, 59318, -26721, -67742], ![-30774, 12822, -55908, 25164, 63809]]]
  hmulB := by decide  
  f := ![![![-1187, -1218, 2606, 190, 2134]], ![![-59, -67, 132, -6, 48]], ![![-957, -960, 2043, 260, 2096]], ![![93, -42, 148, -671, -2476]], ![![-1178, -1134, 2396, 544, 3369]]]
  g := ![![![-213261, 161766, -705430, 317410, 804934], ![93435, -70873, 309062, -139064, -352658], ![-40927, 31050, -135407, 60922, 154498], ![17987, -13608, 59318, -26721, -67742], ![-16916, 12822, -55908, 25164, 63809]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N2 : Nat.card (O ⧸ I433N2) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N2)

lemma isPrimeI433N2 : Ideal.IsPrime I433N2 := prime_ideal_of_norm_prime hp433.out _ NI433N2
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![2795, -1160, 5084, -2260, -5750]] ![![387, 685, -395, 158, 438]]
  ![![91101, -37095, 165511, -74472, -188816]] where
 M := ![![![91101, -37095, 165511, -74472, -188816]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N1 : IdealMulLeCertificate' Table 
  ![![91101, -37095, 165511, -74472, -188816]] ![![-388283, 161766, -705430, 317410, 804934]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![-50640068347, 21097611075, -92002586465, 41396809120, 104979981402]]]
 hmul := by decide  
 g := ![![![![-116951659, 48724275, -212477105, 95604640, 242447994]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1, I433N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
    exact isPrimeI433N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0 ⊙ MulI433N1)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1448917, 603663, -2632351, 1184568, 3003906]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-1448917, 603663, -2632351, 1184568, 3003906]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![303, 198, 1, 0, 0], ![149, 170, 0, 1, 0], ![134, 39, 0, 0, 1]] where
  M :=![![![-1448917, 603663, -2632351, 1184568, 3003906], ![634770, -264349, 1153461, -518131, -1314546], ![-278284, 116639, -504196, 232510, 585780], ![120760, -45774, 228389, -66206, -192840], ![-114550, 46535, -210470, 85123, 222403]]]
  hmulB := by decide  
  f := ![![![-5815, -21086, -23731, 10985, 25938]], ![![3968, 5170, -14069, 7386, 20424]], ![![-2211, -12196, -22709, 10888, 27030]], ![![-471, -5167, -13468, 6682, 17088]], ![![-1406, -5975, -8513, 3959, 9529]]]
  g := ![![![494600, 463053, -2632351, 1184568, 3003906], ![-217570, -203417, 1153461, -518131, -1314546], ![89646, 85593, -504196, 232510, 585780], ![-76027, -60344, 228389, -66206, -192840], ![48229, 42312, -210470, 85123, 222403]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 2 2 8 [175, 364, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 438], [0, 1]]
 g := ![![[125, 291], [213, 204], [111, 83], [177], [420, 398], [157, 58], [199], [75, 1]], ![[0, 148], [148, 235], [190, 356], [177], [418, 41], [117, 381], [199], [150, 438]]]
 h' := ![![[75, 438], [40, 58], [330, 39], [43, 31], [252, 242], [182, 129], [125, 136], [45, 182], [0, 1]], ![[0, 1], [0, 381], [182, 400], [173, 408], [403, 197], [199, 310], [228, 303], [86, 257], [75, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [234, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 2
  hpos := by decide
  P := [175, 364, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-97972, 48580, 153860, 789752, 1971824]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-976344, -550284, 153860, 789752, 1971824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2405, 4491, -3188, 1357, 3642]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![2405, 4491, -3188, 1357, 3642]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![266, 384, 1, 0, 0], ![143, 314, 0, 1, 0], ![328, 281, 0, 0, 1]] where
  M :=![![![2405, 4491, -3188, 1357, 3642], ![928, 3762, 4920, -1971, -4920], ![-978, -1043, 2769, 933, 858], ![-1008, -45, 898, 13482, 24600], ![514, 514, -454, -3448, -6203]]]
  hmulB := by decide  
  f := ![![![34539, -10451, 50934, -40623, -125490]], ![![-44244, -6084, -6830, 113283, 427164]], ![![-17316, -11497, 24675, 73009, 291906]], ![![-23165, -8766, 13166, 76865, 300006]], ![![-1010, -11156, 32896, 37239, 160489]]]
  g := ![![![-1226, -503, -3188, 1357, 3642], ![1339, 264, 4920, -1971, -4920], ![-2625, -3641, 2769, 933, 858], ![-23318, -26175, 898, 13482, 24600], ![6034, 6835, -454, -3448, -6203]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P1 : CertificateIrreducibleZModOfList' 439 2 2 8 [362, 378, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 438], [0, 1]]
 g := ![![[35, 406], [189, 357], [120, 142], [14], [112, 373], [329, 265], [142], [61, 1]], ![[217, 33], [16, 82], [2, 297], [14], [37, 66], [251, 174], [142], [122, 438]]]
 h' := ![![[61, 438], [66, 388], [21, 364], [391, 153], [283, 392], [310, 246], [262, 325], [307, 286], [0, 1]], ![[0, 1], [28, 51], [275, 75], [66, 286], [50, 47], [390, 193], [332, 114], [193, 153], [61, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [164, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N1 : CertifiedPrimeIdeal' SI439N1 439 where
  n := 2
  hpos := by decide
  P := [362, 378, 1]
  hirr := P439P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34718, -10716, 21876, 123712, 467880]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-403210, -407132, 21876, 123712, 467880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N1 B_one_repr
lemma NI439N1 : Nat.card (O ⧸ I439N1) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N1

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -58, 111, -47, -122]] i)))

def SI439N2: IdealEqSpanCertificate' Table ![![-41, -58, 111, -47, -122]] 
 ![![439, 0, 0, 0, 0], ![296, 1, 0, 0, 0], ![184, 0, 1, 0, 0], ![411, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-41, -58, 111, -47, -122], ![-28, -88, -77, 44, 100], ![12, 16, -56, 71, 148], ![6, 83, 81, 263, 466], ![-6, -29, -12, -73, -133]]]
  hmulB := by decide  
  f := ![![![759565, -316449, 1379979, -620928, -1574642]], ![![511386, -213053, 929087, -418047, -1060146]], ![![318692, -132773, 579000, -260524, -660676]], ![![710973, -296205, 1291698, -581204, -1473902]], ![![109141, -45470, 198287, -89221, -226261]]]
  g := ![![![54, -58, 111, -47, -122], ![36, -88, -77, 44, 100], ![-75, 16, -56, 71, 148], ![-403, 83, 81, 263, 466], ![112, -29, -12, -73, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N2 : Nat.card (O ⧸ I439N2) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N2)

lemma isPrimeI439N2 : Ideal.IsPrime I439N2 := prime_ideal_of_norm_prime hp439.out _ NI439N2
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-1448917, 603663, -2632351, 1184568, 3003906]] ![![2405, 4491, -3188, 1357, 3642]]
  ![![-43703, 138176, 158177, 894263, 1609050]] where
 M := ![![![-43703, 138176, 158177, 894263, 1609050]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N1 : IdealMulLeCertificate' Table 
  ![![-43703, 138176, 158177, 894263, 1609050]] ![![-41, -58, 111, -47, -122]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![-4467703, 20467497, 28778206, 137094871, 245282470]]]
 hmul := by decide  
 g := ![![![![-10177, 46623, 65554, 312289, 558730]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1, I439N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
    exact isPrimeI439N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0 ⊙ MulI439N1)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35701, 14878, -64853, 29215, 74064]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![-35701, 14878, -64853, 29215, 74064]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![48, 84, 1, 0, 0], ![398, 80, 0, 1, 0], ![187, 117, 0, 0, 1]] where
  M :=![![![-35701, 14878, -64853, 29215, 74064], ![15634, -6486, 28459, -12582, -32058], ![-6894, 3052, -12174, 6913, 16542], ![2716, 19, 7249, 6095, 9132], ![-2752, 847, -5612, 65, 1811]]]
  hmulB := by decide  
  f := ![![![-20071, -4415, 128875, -57540, -144336]], ![![-29256, -77611, -32699, 16711, 37032]], ![![-7714, -15223, 7618, -3000, -8454]], ![![-23284, -17908, 109885, -48682, -122994]], ![![-16213, -22385, 45790, -19886, -51175]]]
  g := ![![![-50565, -12506, -64853, 29215, 74064], ![21788, 5328, 28459, -12582, -32058], ![-11890, -3302, -12174, 6913, 16542], ![-10110, -4887, 7249, 6095, 9132], ![-221, 576, -5612, 65, 1811]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 2 2 8 [218, 424, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 442], [0, 1]]
 g := ![![[132, 89], [234, 196], [351], [263, 42], [430, 40], [186, 100], [71], [19, 1]], ![[51, 354], [414, 247], [351], [175, 401], [304, 403], [314, 343], [71], [38, 442]]]
 h' := ![![[19, 442], [376, 48], [93, 429], [256, 237], [176, 186], [208, 406], [130, 433], [288, 143], [0, 1]], ![[0, 1], [402, 395], [270, 14], [329, 206], [166, 257], [391, 37], [383, 10], [347, 300], [19, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [417]]
 b := ![[], [345, 430]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 2
  hpos := by decide
  P := [218, 424, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18096, 21679, 43491, 206880, 460987]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-385211, -167308, 43491, 206880, 460987]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 52, 30, -16, -36]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![11, 52, 30, -16, -36]] 
 ![![443, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![430, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![11, 52, 30, -16, -36], ![-4, -5, 40, -26, -60], ![-8, -30, -23, -42, -72], ![12, -50, -84, -305, -540], ![-2, 18, 26, 78, 137]]]
  hmulB := by decide  
  f := ![![![-2391, -856, 1162, 7732, 30084]], ![![-361, -129, 174, 1166, 4536]], ![![-2526, -906, 1237, 8178, 31824]], ![![937, 346, -514, -3089, -12048]], ![![-984, -358, 510, 3214, 12521]]]
  g := ![![![-31, 52, 30, -16, -36], ![-27, -5, 40, -26, -60], ![42, -30, -23, -42, -72], ![199, -50, -84, -305, -540], ![-56, 18, 26, 78, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N1 : Nat.card (O ⧸ I443N1) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N1)

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := prime_ideal_of_norm_prime hp443.out _ NI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 4, 1, 6]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![1, -1, 4, 1, 6]] 
 ![![443, 0, 0, 0, 0], ![316, 1, 0, 0, 0], ![262, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![313, 0, 0, 0, 1]] where
  M :=![![![1, -1, 4, 1, 6], ![4, 2, -4, -15, -60], ![-30, -11, 17, 101, 390], ![188, 71, -98, -606, -2388], ![-102, -38, 54, 332, 1301]]]
  hmulB := by decide  
  f := ![![![-901, -1755, 2174, -927, -2430]], ![![-644, -1256, 1546, -659, -1728]], ![![-532, -1037, 1283, -547, -1434]], ![![-99, -192, 242, -103, -270]], ![![-637, -1241, 1536, -655, -1717]]]
  g := ![![![-6, -1, 4, 1, 6], ![45, 2, -4, -15, -60], ![-289, -11, 17, 101, 390], ![1762, 71, -98, -606, -2388], ![-961, -38, 54, 332, 1301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2

def I443N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -11, 49, -34, -102]] i)))

def SI443N3: IdealEqSpanCertificate' Table ![![-9, -11, 49, -34, -102]] 
 ![![443, 0, 0, 0, 0], ![413, 1, 0, 0, 0], ![429, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![167, 0, 0, 0, 1]] where
  M :=![![![-9, -11, 49, -34, -102], ![-34, -43, -11, 83, 306], ![140, 49, -100, -436, -1716], ![-844, -296, 457, 2784, 10860], ![458, 163, -242, -1513, -5897]]]
  hmulB := by decide  
  f := ![![![-3620279, 1508272, -6577283, 2959463, 7505034]], ![![-3371533, 1404640, -6125364, 2756121, 6989370]], ![![-3507437, 1461260, -6372273, 2867218, 7271106]], ![![-187273, 78021, -340236, 153088, 388224]], ![![-1365403, 568851, -2480649, 1116174, 2830555]]]
  g := ![![![3, -11, 49, -34, -102], ![-69, -43, -11, 83, 306], ![721, 49, -100, -436, -1716], ![-4407, -296, 457, 2784, 10860], ![2385, 163, -242, -1513, -5897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N3 : Nat.card (O ⧸ I443N3) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N3)

lemma isPrimeI443N3 : Ideal.IsPrime I443N3 := prime_ideal_of_norm_prime hp443.out _ NI443N3
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![-35701, 14878, -64853, 29215, 74064]] ![![11, 52, 30, -16, -36]]
  ![![269053, -112850, 487313, -225369, -567360]] where
 M := ![![![269053, -112850, 487313, -225369, -567360]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![269053, -112850, 487313, -225369, -567360]] ![![1, -1, 4, 1, 6]]
  ![![699611, -296715, 1260655, -609490, -1516800]] where
 M := ![![![699611, -296715, 1260655, -609490, -1516800]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N2 : IdealMulLeCertificate' Table 
  ![![699611, -296715, 1260655, -609490, -1516800]] ![![-9, -11, 49, -34, -102]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![-1329, 5759, 7974, 38541, 69108]]]
 hmul := by decide  
 g := ![![![![-3, 13, 18, 87, 156]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1, I443N2, I443N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
    exact isPrimeI443N2
    exact isPrimeI443N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0 ⊙ MulI443N1 ⊙ MulI443N2)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1699, 709, -3085, 1388, 3520]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![-1699, 709, -3085, 1388, 3520]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![4, 116, 1, 0, 0], ![434, 18, 0, 1, 0], ![143, 362, 0, 0, 1]] where
  M :=![![![-1699, 709, -3085, 1388, 3520], ![744, -311, 1353, -609, -1544], ![-326, 135, -594, 264, 670], ![142, -62, 257, -126, -302], ![-134, 57, -244, 111, 275]]]
  hmulB := by decide  
  f := ![![![-171, -394, -7, 13, 8]], ![![-18, -158, -363, 166, 410]], ![![-6, -44, -94, 43, 106]], ![![-166, -387, -21, 19, 24]], ![![-69, -253, -295, 138, 333]]]
  g := ![![![-2439, -2095, -3085, 1388, 3520], ![1070, 919, 1353, -609, -1544], ![-464, -397, -594, 264, 670], ![216, 182, 257, -126, -302], ![-193, -163, -244, 111, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 2 2 8 [292, 215, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [234, 448], [0, 1]]
 g := ![![[236, 429], [442], [254], [251], [440], [97], [0, 265], [234, 1]], ![[46, 20], [442], [254], [251], [440], [97], [48, 184], [19, 448]]]
 h' := ![![[234, 448], [67, 97], [244, 56], [35, 178], [405, 196], [412, 248], [0, 411], [369, 135], [0, 1]], ![[0, 1], [315, 352], [327, 393], [379, 271], [22, 253], [74, 201], [88, 38], [80, 314], [234, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [326]]
 b := ![[], [236, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 2
  hpos := by decide
  P := [292, 215, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1628, 5341, 8572, 41319, 79066]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65200, -67605, 8572, 41319, 79066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46201, 19246, -83931, 37775, 95808]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![-46201, 19246, -83931, 37775, 95808]] 
 ![![449, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![230, 0, 0, 0, 1]] where
  M :=![![![-46201, 19246, -83931, 37775, 95808], ![20258, -8426, 36763, -16604, -42186], ![-8978, 3654, -16052, 7611, 19794], ![4572, -1367, 6693, -5429, -16836], ![-4034, 1389, -6454, 4215, 12353]]]
  hmulB := by decide  
  f := ![![![-11925, -28471, -3329, 1810, 3060]], ![![-2365, -5666, -718, 379, 660]], ![![-4263, -10190, -1209, 614, 1038]], ![![-1025, -2495, -316, -98, -198]], ![![-6114, -14585, -1700, 995, 1691]]]
  g := ![![![-26181, 19246, -83931, 37775, 95808], ![11585, -8426, 36763, -16604, -42186], ![-5789, 3654, -16052, 7611, 19794], ![6977, -1367, 6693, -5429, -16836], ![-4664, 1389, -6454, 4215, 12353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N1 : Nat.card (O ⧸ I449N1) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N1)

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := prime_ideal_of_norm_prime hp449.out _ NI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 17, -72, 25, 54]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![-37, 17, -72, 25, 54]] 
 ![![449, 0, 0, 0, 0], ![105, 1, 0, 0, 0], ![200, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![443, 0, 0, 0, 1]] where
  M :=![![![-37, 17, -72, 25, 54], ![4, -12, 38, 29, 132], ![74, 33, -57, -261, -1026], ![-504, -187, 276, 1662, 6480], ![272, 102, -152, -900, -3511]]]
  hmulB := by decide  
  f := ![![![-1101, -255, 6970, -3105, -7794]], ![![-261, -69, 1626, -724, -1818]], ![![-490, -115, 3097, -1379, -3462]], ![![-251, -54, 1600, -709, -1782]], ![![-1087, -253, 6878, -3065, -7693]]]
  g := ![![![-31, 17, -72, 25, 54], ![-151, -12, 38, 29, 132], ![1090, 33, -57, -261, -1026], ![-6855, -187, 276, 1662, 6480], ![3715, 102, -152, -900, -3511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2

def I449N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 20, -111, 53, 132]] i)))

def SI449N3: IdealEqSpanCertificate' Table ![![-57, 20, -111, 53, 132]] 
 ![![449, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![435, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![-57, 20, -111, 53, 132], ![26, -4, 47, -2, -18], ![-14, 24, 8, 121, 222], ![-20, 107, 165, 733, 1308], ![2, -27, -50, -189, -335]]]
  hmulB := by decide  
  f := ![![![1219, 523, -649, -3872, -15096]], ![![361, 156, -192, -1145, -4464]], ![![1283, 544, -683, -4086, -15930]], ![![-228, -58, 121, 790, 3078]], ![![654, 259, -348, -2113, -8237]]]
  g := ![![![50, 20, -111, 53, 132], ![-39, -4, 47, -2, -18], ![-112, 24, 8, 121, 222], ![-770, 107, 165, 733, 1308], ![205, -27, -50, -189, -335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N3 : Nat.card (O ⧸ I449N3) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N3)

lemma isPrimeI449N3 : Ideal.IsPrime I449N3 := prime_ideal_of_norm_prime hp449.out _ NI449N3
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![-1699, 709, -3085, 1388, 3520]] ![![-46201, 19246, -83931, 37775, 95808]]
  ![![112701807, -46953694, 204755960, -92130548, -233637964]] where
 M := ![![![112701807, -46953694, 204755960, -92130548, -233637964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![112701807, -46953694, 204755960, -92130548, -233637964]] ![![-37, 17, -72, 25, 54]]
  ![![-6321570611, 2633661875, -11484920916, 5167779313, 13105335574]] where
 M := ![![![-6321570611, 2633661875, -11484920916, 5167779313, 13105335574]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N2 : IdealMulLeCertificate' Table 
  ![![-6321570611, 2633661875, -11484920916, 5167779313, 13105335574]] ![![-57, 20, -111, 53, 132]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![512448711289, -213495835711, 931013886563, -418912184026, -1062337753640]]]
 hmul := by decide  
 g := ![![![![1141311161, -475491839, 2073527587, -932989274, -2366008360]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1, I449N2, I449N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
    exact isPrimeI449N2
    exact isPrimeI449N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0 ⊙ MulI449N1 ⊙ MulI449N2)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 91, -472, 203, 520]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![-199, 91, -472, 203, 520]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![0, 0, 457, 0, 0], ![168, 74, 373, 1, 0], ![355, 220, 401, 0, 1]] where
  M :=![![![-199, 91, -472, 203, 520], ![114, 4, 180, -141, -314], ![-32, -27, -105, -333, -584], ![82, -365, -442, -2262, -4058], ![-32, 102, 86, 606, 1097]]]
  hmulB := by decide  
  f := ![![![9, 7, -14, -19, -80]], ![![-42, -10, 30, 143, 562]], ![![276, 101, -143, -911, -3548]], ![![218, 82, -115, -715, -2786]], ![![231, 90, -123, -752, -2931]]]
  g := ![![![-479, -283, -623, 203, 520], ![296, 174, 391, -141, -314], ![576, 335, 784, -333, -584], ![3984, 2319, 5406, -2262, -4058], ![-1075, -626, -1457, 606, 1097]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 3 2 8 [117, 453, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 90, 376], [192, 366, 81], [0, 1]]
 g := ![![[96, 272, 260], [152, 107], [235, 410], [268, 20, 24], [138, 4], [430, 151], [439, 2, 157], [1]], ![[277, 448, 257, 450], [100, 8], [434, 6], [165, 394, 244, 268], [190, 98], [72, 38], [308, 105, 381, 311], [46, 176, 194, 50]], ![[180, 304, 135, 6], [217, 100], [275, 350], [127, 37, 12, 2], [140, 57], [212, 36], [265, 400, 389, 24], [176, 392, 231, 407]]]
 h' := ![![[193, 90, 376], [190, 385, 122], [178, 14, 150], [177, 89, 180], [427, 26, 350], [11, 122, 455], [278, 130, 279], [340, 4, 385], [0, 1]], ![[192, 366, 81], [209, 311, 214], [435, 95, 297], [253, 214, 175], [197, 231, 319], [374, 58, 354], [301, 256, 184], [92, 188, 287], [193, 90, 376]], ![[0, 1], [350, 218, 121], [356, 348, 10], [86, 154, 102], [324, 200, 245], [131, 277, 105], [370, 71, 451], [302, 265, 242], [192, 366, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [368, 15], []]
 b := ![[], [331, 310, 271], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 3
  hpos := by decide
  P := [117, 453, 72, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53351801, -9345000, 40564374, 231443618, 768847536]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-682443665, -407620636, -863448068, 231443618, 768847536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 95443993 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 14, 231, -105, -262]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![81, 14, 231, -105, -262]] 
 ![![457, 0, 0, 0, 0], ![250, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![81, 14, 231, -105, -262], ![-52, -24, -39, 18, 44], ![8, -34, -14, 3, 8], ![2, 11, -33, -11, -10], ![4, -1, 26, -5, -17]]]
  hmulB := by decide  
  f := ![![![-5639, -2075, 3005, 18490, 72074]], ![![-3008, -1107, 1603, 9863, 38446]], ![![-1823, -670, 971, 5978, 23302]], ![![878, 318, -465, -2882, -11232]], ![![-2206, -809, 1174, 7235, 28201]]]
  g := ![![![4, 14, 231, -105, -262], ![11, -24, -39, 18, 44], ![20, -34, -14, 3, 8], ![7, 11, -33, -11, -10], ![-2, -1, 26, -5, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-439, -1426, -1301, 621, 1466]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![-439, -1426, -1301, 621, 1466]] 
 ![![457, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![321, 0, 1, 0, 0], ![274, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![-439, -1426, -1301, 621, 1466], ![224, 182, -1029, 460, 1160], ![240, 684, 402, -169, -400], ![-62, 71, 577, -71, -298], ![-22, -153, -296, 87, 241]]]
  hmulB := by decide  
  f := ![![![-222839, 92675, -404359, 182682, 464210]], ![![-141679, 58924, -257094, 116141, 295112]], ![![-156635, 65128, -284185, 128452, 326486]], ![![-133454, 55588, -242423, 109132, 276820]], ![![-109324, 45419, -198236, 89771, 228383]]]
  g := ![![![730, -1426, -1301, 621, 1466], ![-237, 182, -1029, 460, 1160], ![-420, 684, 402, -169, -400], ![-262, 71, 577, -71, -298], ![135, -153, -296, 87, 241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![-199, 91, -472, 203, 520]] ![![81, 14, 231, -105, -262]]
  ![![-22141, 12791, -36089, 16284, 41496]] where
 M := ![![![-22141, 12791, -36089, 16284, 41496]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![-22141, 12791, -36089, 16284, 41496]] ![![-439, -1426, -1301, 621, 1466]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![2001203, 4023428, -1751224, 687328, 1962358]]]
 hmul := by decide  
 g := ![![![![4379, 8804, -3832, 1504, 4294]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1, I457N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
    exact isPrimeI457N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0 ⊙ MulI457N1)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6403, -16493, -5594, 2943, 6348]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![-6403, -16493, -5594, 2943, 6348]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![0, 0, 0, 461, 0], ![317, 360, 392, 368, 1]] where
  M :=![![![-6403, -16493, -5594, 2943, 6348], ![462, -3460, -14012, 6349, 15690], ![2992, 6811, -103, -219, -72], ![366, 2773, 6226, -3394, -7974], ![-706, -2384, -2432, 1292, 2995]]]
  hmulB := by decide  
  f := ![![![65, -29, 124, -47, -108]], ![![-14, 18, -62, -27, -138]], ![![-84, -41, 75, 307, 1212]], ![![598, 223, -332, -1978, -7710]], ![![439, 137, -164, -1369, -5297]]]
  g := ![![![-4379, -4993, -5410, -5061, 6348], ![-10788, -12260, -13372, -12511, 15690], ![56, 71, 61, 57, -72], ![5484, 6233, 6794, 6358, -7974], ![-2061, -2344, -2552, -2388, 2995]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 4 2 8 [447, 45, 446, 126, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [179, 212, 92, 70], [145, 256, 211, 57], [11, 453, 158, 334], [0, 1]]
 g := ![![[375, 15, 50, 36], [291, 203, 317], [96, 319, 451, 356], [174, 283, 353, 113], [122, 428, 26], [341, 377, 245], [227, 217, 335, 1], []], ![[442, 416, 358, 347, 302, 49], [411, 182, 400], [282, 159, 30, 262, 90, 144], [347, 267, 276, 223, 63, 141], [72, 275, 126], [297, 395, 93], [348, 277, 104, 241, 296, 335], [328, 392, 209, 366, 115, 16]], ![[103, 73, 77, 441, 228, 241], [177, 279, 258], [93, 296, 328, 30, 305, 106], [154, 140, 88, 379, 34, 197], [93, 276, 58], [359, 90, 165], [4, 105, 164, 62, 33, 129], [338, 316, 408, 455, 215, 332]], ![[239, 161, 144, 358, 268, 375], [392, 406, 391], [97, 315, 338, 151, 93, 419], [441, 52, 2, 420, 243, 230], [407, 320, 130], [97, 375, 166], [19, 258, 154, 139, 188, 34], [360, 343, 193, 214, 259, 301]]]
 h' := ![![[179, 212, 92, 70], [63, 212, 459, 6], [422, 250, 76, 346], [131, 351, 45, 109], [158, 355, 190, 389], [260, 396, 299, 165], [412, 199, 174, 160], [0, 0, 0, 1], [0, 1]], ![[145, 256, 211, 57], [203, 106, 53, 108], [177, 18, 372, 441], [208, 108, 192, 210], [12, 269, 459, 87], [159, 357, 9, 257], [407, 351, 133, 75], [20, 441, 35, 329], [179, 212, 92, 70]], ![[11, 453, 158, 334], [243, 285, 19, 228], [158, 253, 328, 388], [339, 352, 351, 81], [450, 428, 295, 321], [158, 246, 81, 320], [277, 371, 172, 318], [154, 31, 386, 431], [145, 256, 211, 57]], ![[0, 1], [312, 319, 391, 119], [109, 401, 146, 208], [412, 111, 334, 61], [186, 331, 439, 125], [375, 384, 72, 180], [441, 1, 443, 369], [378, 450, 40, 161], [11, 453, 158, 334]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 246, 282], []]
 b := ![[], [], [338, 273, 405, 359], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 4
  hpos := by decide
  P := [447, 45, 446, 126, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2103556280843, 1744447135481, 4123597950410, 20823083203075, 48292297131804]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33212064527251, -37708205033219, -41055220992878, -38504863907377, 48292297131804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 45165175441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, -29, 124, -47, -108]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![65, -29, 124, -47, -108]] 
 ![![461, 0, 0, 0, 0], ![235, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![264, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![65, -29, 124, -47, -108], ![-14, 18, -62, -27, -138], ![-84, -41, 75, 307, 1212], ![598, 223, -332, -1978, -7710], ![-322, -122, 184, 1070, 4175]]]
  hmulB := by decide  
  f := ![![![-6403, -16493, -5594, 2943, 6348]], ![![-3263, -8415, -2882, 1514, 3270]], ![![-1313, -3384, -1153, 606, 1308]], ![![-3666, -9439, -3190, 1678, 3618]], ![![-696, -1794, -612, 322, 695]]]
  g := ![![![28, -29, 124, -47, -108], ![34, 18, -62, -27, -138], ![-302, -41, 75, 307, 1212], ![1925, 223, -332, -1978, -7710], ![-1042, -122, 184, 1070, 4175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N1 : Nat.card (O ⧸ I461N1) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N1)

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := prime_ideal_of_norm_prime hp461.out _ NI461N1
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![-6403, -16493, -5594, 2943, 6348]] ![![65, -29, 124, -47, -108]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![461, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0)
instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![463, 0, 0, 0, 0]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![0, 0, 0, 0, 463]] where
  M :=![![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![0, 0, 0, 0, 463]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 5 2 8 [47, 152, 261, 182, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [426, 380, 225, 207, 351], [461, 140, 365, 182, 149], [258, 238, 217, 281, 122], [229, 167, 119, 256, 304], [0, 1]]
 g := ![![[119, 131, 256, 210, 79], [70, 358, 337, 422, 444], [399, 74, 46, 20, 47], [238, 189, 278, 91, 373], [135, 76, 376, 89], [321, 92, 10, 321], [43, 448, 1], []], ![[287, 353, 243, 124, 399, 109, 103, 9], [121, 325, 102, 218, 375, 196, 452, 55], [307, 317, 345, 17, 346, 38, 147, 70], [306, 92, 298, 58, 295, 443, 183, 268], [449, 43, 375, 55], [101, 63, 263, 268], [14, 76, 334, 31, 140, 190, 302, 161], [228, 454, 296, 10, 361, 326, 324, 277]], ![[330, 225, 408, 58, 439, 380, 123, 135], [380, 382, 337, 17, 335, 370, 229, 218], [310, 122, 281, 298, 178, 379, 257, 42], [29, 454, 387, 445, 39, 254, 283, 259], [279, 51, 30, 33], [291, 400, 165, 437], [289, 295, 113, 192, 317, 125, 340, 423], [339, 108, 412, 26, 240, 233, 418, 277]], ![[436, 211, 5, 9, 458, 342, 375, 133], [71, 18, 340, 138, 430, 185, 45, 276], [109, 84, 299, 91, 397, 292, 190, 376], [286, 254, 299, 292, 177, 436, 183, 2], [352, 111, 114, 410], [413, 313, 24, 116], [333, 264, 405, 10, 113, 30, 101, 111], [141, 346, 46, 371, 82, 161, 19, 425]], ![[298, 316, 162, 93, 97, 55, 202, 63], [84, 53, 432, 460, 434, 332, 429, 201], [403, 328, 354, 329, 14, 202, 448, 309], [186, 397, 27, 81, 193, 21, 133, 332], [64, 400, 67, 286], [97, 14, 306, 359], [303, 461, 325, 94, 11, 9, 40, 347], [41, 254, 114, 59, 34, 323, 450, 87]]]
 h' := ![![[426, 380, 225, 207, 351], [414, 432, 381, 343, 81], [230, 151, 109, 362, 295], [389, 350, 382, 296, 343], [31, 99, 8, 73, 77], [47, 16, 28, 200, 355], [294, 188, 270, 104, 435], [0, 0, 0, 1], [0, 1]], ![[461, 140, 365, 182, 149], [379, 10, 181, 269, 133], [137, 129, 85, 170, 450], [130, 233, 193, 47, 418], [119, 109, 276, 221, 392], [336, 288, 458, 162, 38], [180, 197, 299, 442, 350], [210, 379, 300, 367, 153], [426, 380, 225, 207, 351]], ![[258, 238, 217, 281, 122], [196, 302, 155, 208, 132], [333, 447, 4, 11, 61], [223, 208, 357, 197, 374], [269, 161, 397, 171, 140], [176, 304, 153, 129, 212], [278, 457, 186, 351, 433], [264, 173, 40, 390, 297], [461, 140, 365, 182, 149]], ![[229, 167, 119, 256, 304], [233, 316, 311, 194, 15], [360, 40, 81, 445, 403], [206, 366, 402, 0, 42], [102, 79, 146, 348, 104], [442, 452, 204, 337, 372], [83, 344, 312, 88, 231], [234, 18, 247, 106, 404], [258, 238, 217, 281, 122]], ![[0, 1], [18, 329, 361, 375, 102], [418, 159, 184, 401, 180], [76, 232, 55, 386, 212], [134, 15, 99, 113, 213], [144, 329, 83, 98, 412], [252, 203, 322, 404, 403], [83, 356, 339, 62, 72], [229, 167, 119, 256, 304]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168, 385, 322, 49], [], [], []]
 b := ![[], [326, 339, 184, 211, 203], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 5
  hpos := by decide
  P := [47, 152, 261, 182, 15, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-447958095162855, 1056229603661279, 1696222951495976, 8225335878192965, 16110374276178206]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-967512084585, 2281273442033, 3663548491352, 17765304272555, 34795624786562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 21276733558543 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def PBC463 : ContainsPrimesAboveP 463 ![I463N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![463, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 463 (by decide) 𝕀



lemma PB953I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB953I9 : PrimesBelowBoundCertificateInterval O 419 463 953 where
  m := 9
  g := ![1, 2, 3, 3, 4, 4, 3, 2, 1]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB953I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1, I433N2]
    · exact ![I439N0, I439N1, I439N2]
    · exact ![I443N0, I443N1, I443N2, I443N3]
    · exact ![I449N0, I449N1, I449N2, I449N3]
    · exact ![I457N0, I457N1, I457N2]
    · exact ![I461N0, I461N1]
    · exact ![I463N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![13225450646101]
    · exact ![34507149121, 431]
    · exact ![187489, 187489, 433]
    · exact ![192721, 192721, 439]
    · exact ![196249, 443, 443, 443]
    · exact ![201601, 449, 449, 449]
    · exact ![95443993, 457, 457]
    · exact ![45165175441, 461]
    · exact ![21276733558543]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
      exact NI433N2
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
      exact NI443N2
      exact NI443N3
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
      exact NI449N2
      exact NI449N3
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
      exact NI457N2
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
  β := ![I431N1, I433N2, I439N2, I443N1, I443N2, I443N3, I449N1, I449N2, I449N3, I457N1, I457N2, I461N1]
  Il := ![[], [I431N1], [I433N2], [I439N2], [I443N1, I443N2, I443N3], [I449N1, I449N2, I449N3], [I457N1, I457N2], [I461N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
