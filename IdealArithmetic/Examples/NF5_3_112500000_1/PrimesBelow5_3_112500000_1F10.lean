
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467, 0, 0, 0, 0]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![467, 0, 0, 0, 0]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![0, 0, 0, 467, 0], ![0, 0, 0, 0, 467]] where
  M :=![![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![0, 0, 0, 467, 0], ![0, 0, 0, 0, 467]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 5 2 8 [188, 145, 154, 345, 413, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [356, 174, 423, 231, 252], [380, 388, 197, 163, 363], [343, 416, 72, 151, 161], [376, 422, 242, 389, 158], [0, 1]]
 g := ![![[326, 119, 21, 272, 173], [181, 12, 421, 150, 280], [451, 454, 55, 156], [404, 271, 429, 389], [71, 33, 128, 127, 7], [252, 78, 146, 27], [236, 54, 1], []], ![[78, 446, 463, 427, 324, 423, 241, 193], [171, 311, 46, 92, 364, 386, 125, 236], [367, 354, 436, 227], [13, 28, 335, 161], [289, 211, 224, 429, 91, 356, 84, 449], [217, 199, 374, 248], [411, 268, 185, 442, 226, 137, 212, 236], [67, 178, 259, 344, 4, 245, 7, 319]], ![[333, 183, 33, 240, 183, 265, 137, 204], [9, 419, 444, 96, 436, 407, 250, 390], [396, 196, 340, 84], [218, 344, 313, 465], [451, 48, 103, 24, 215, 353, 173, 387], [236, 106, 79, 199], [371, 226, 250, 296, 358, 183, 224, 40], [437, 392, 325, 396, 200, 166, 283, 139]], ![[315, 244, 36, 452, 86, 45, 389, 95], [462, 127, 148, 284, 190, 16, 67, 208], [460, 16, 47, 422], [451, 425, 60, 89], [390, 240, 100, 84, 296, 424, 102, 113], [18, 100, 90, 342], [125, 371, 141, 69, 25, 308, 42, 149], [463, 145, 146, 260, 190, 329, 218, 169]], ![[314, 105, 145, 42, 328, 318, 371, 28], [442, 127, 340, 258, 396, 337, 297, 381], [2, 25, 75, 175], [268, 283, 400, 287], [81, 91, 119, 144, 225, 427, 389, 177], [255, 200, 338, 209], [272, 145, 410, 299, 152, 54, 257, 95], [403, 95, 291, 28, 59, 80, 346, 30]]]
 h' := ![![[356, 174, 423, 231, 252], [63, 407, 196, 449, 226], [399, 332, 286, 330, 41], [367, 265, 217, 198, 256], [195, 151, 305, 268, 250], [267, 208, 454, 284, 53], [464, 460, 3, 250, 31], [0, 0, 0, 1], [0, 1]], ![[380, 388, 197, 163, 363], [92, 305, 405, 303, 452], [109, 316, 50, 107, 281], [359, 17, 132, 460, 244], [466, 153, 234, 158, 377], [340, 267, 306, 259, 457], [290, 335, 311, 92, 46], [225, 290, 51, 234, 186], [356, 174, 423, 231, 252]], ![[343, 416, 72, 151, 161], [242, 204, 336, 265, 463], [246, 333, 192, 65, 203], [446, 27, 265, 344, 317], [56, 297, 85, 419, 341], [193, 247, 326, 461, 403], [453, 409, 333, 106, 40], [3, 131, 42, 131, 171], [380, 388, 197, 163, 363]], ![[376, 422, 242, 389, 158], [42, 202, 348, 165, 395], [321, 388, 152, 290, 339], [261, 315, 165, 192, 319], [276, 367, 257, 419, 137], [368, 343, 282, 384, 215], [463, 258, 392, 24, 376], [422, 157, 208, 83, 131], [343, 416, 72, 151, 161]], ![[0, 1], [45, 283, 116, 219, 332], [236, 32, 254, 142, 70], [335, 310, 155, 207, 265], [331, 433, 53, 137, 296], [199, 336, 33, 13, 273], [186, 406, 362, 462, 441], [57, 356, 166, 18, 446], [376, 422, 242, 389, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [455, 376, 381, 6], [], [], []]
 b := ![[], [291, 86, 377, 338, 189], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 5
  hpos := by decide
  P := [188, 145, 154, 345, 413, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2090297433545, -1064666195578, -896979765850, -957883202854, -372271412553]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4476011635, -2279799134, -1920727550, -2051141762, -797155059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 22211833167107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def PBC467 : ContainsPrimesAboveP 467 ![I467N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![467, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 467 (by decide) 𝕀

instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, -17, 8, 38, -22]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![223, -17, 8, 38, -22]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![456, 225, 357, 1, 0], ![59, 237, 355, 0, 1]] where
  M :=![![![223, -17, 8, 38, -22], ![-512, 55, -62, -116, 76], ![850, 59, 69, 82, -116], ![-884, -35, -32, -95, 86], ![372, -149, 18, 134, -47]]]
  hmulB := by decide  
  f := ![![![69, 1, 2, 14, -10]], ![![-236, -9, -14, -56, 28]], ![![322, -13, 5, 70, -56]], ![![194, -13, -1, 39, -38]], ![![131, -14, -3, 26, -29]]]
  g := ![![![-33, -7, -12, 38, -22], ![100, 17, 30, -116, 76], ![-62, 19, 25, 82, -116], ![78, 2, 7, -95, 86], ![-121, -40, -65, 134, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [452, 461, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 126, 401], [187, 352, 78], [0, 1]]
 g := ![![[167, 302, 7], [363, 260, 35], [362, 254, 126], [350, 155, 112], [242, 293, 274], [252, 55], [389, 450, 214], [1]], ![[403, 368, 345, 466], [54, 110, 334, 15], [17, 373, 216, 173], [73, 467, 324, 327], [401, 128, 241, 105], [435, 233], [40, 70, 463, 189], [279, 474, 128, 137]], ![[350, 257, 447, 113], [362, 345, 101, 402], [120, 296, 50, 177], [380, 128, 240, 188], [433, 130, 236, 34], [472, 250], [186, 60, 4, 435], [330, 290, 301, 342]]]
 h' := ![![[198, 126, 401], [221, 416, 38], [194, 97, 122], [349, 312, 242], [307, 355, 152], [365, 98, 194], [444, 242, 318], [27, 18, 385], [0, 1]], ![[187, 352, 78], [189, 18, 88], [25, 50, 411], [308, 28, 15], [136, 393, 427], [220, 99, 290], [410, 414, 134], [66, 386, 475], [198, 126, 401]], ![[0, 1], [347, 45, 353], [190, 332, 425], [427, 139, 222], [318, 210, 379], [41, 282, 474], [229, 302, 27], [183, 75, 98], [187, 352, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 435], []]
 b := ![[], [448, 434, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [452, 461, 94, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3754886412, -1944413822, -1688187218, -1793420492, -698891296]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1785552076, 1184159570, 1851084214, -1793420492, -698891296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -1, -2, -14, 10]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-69, -1, -2, -14, 10]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![261, 367, 1, 0, 0], ![237, 370, 0, 1, 0], ![425, 256, 0, 0, 1]] where
  M :=![![![-69, -1, -2, -14, 10], ![236, 9, 14, 56, -28], ![-322, 13, -5, -70, 56], ![392, 17, 26, 93, -50], ![-300, 17, 12, -50, 57]]]
  hmulB := by decide  
  f := ![![![-223, 17, -8, -38, 22]], ![![512, -55, 62, 116, -76]], ![![269, -33, 43, 68, -46]], ![![287, -34, 44, 71, -48]], ![![75, -14, 26, 28, -21]]]
  g := ![![![-1, 7, -2, -14, 10], ![-10, -39, 14, 56, -28], ![-13, 28, -5, -70, 56], ![-15, -65, 26, 93, -50], ![-33, -1, 12, -50, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [475, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [465, 478], [0, 1]]
 g := ![![[236, 115], [403, 394], [97, 386], [384, 392], [59, 345], [242], [64, 243], [465, 1]], ![[63, 364], [156, 85], [441, 93], [165, 87], [19, 134], [242], [15, 236], [451, 478]]]
 h' := ![![[465, 478], [175, 383], [388, 407], [99, 156], [236, 256], [402, 102], [256, 338], [423, 200], [0, 1]], ![[0, 1], [82, 96], [438, 72], [310, 323], [5, 223], [411, 377], [314, 141], [18, 279], [465, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [244]]
 b := ![[], [375, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [475, 14, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4424, 2056, 2066, 2274, 866]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3010, -3798, 2066, 2274, 866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![223, -17, 8, 38, -22]] ![![-69, -1, -2, -14, 10]]
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

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90450, -2435, 5524, 13184, -10193]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![90450, -2435, 5524, 13184, -10193]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![181, 45, 269, 1, 0], ![483, 455, 215, 0, 1]] where
  M :=![![![90450, -2435, 5524, 13184, -10193], ![-233584, 6373, -14208, -33996, 26368], ![302208, -8030, 18533, 44108, -33996], ![-299623, 8187, -18218, -43597, 33827], ![204875, -5279, 12682, 29998, -22954]]]
  hmulB := by decide  
  f := ![![![252, 175, -26, -90, -5]], ![![-172, 143, 288, 4, -180]], ![![-1872, -1038, 251, 500, 4]], ![![-955, -495, 155, 243, -16]], ![![-733, -149, 353, 134, -171]]]
  g := ![![![5395, 8300, -2771, 13184, -10193], ![-13996, -21481, 7108, -33996, 26368], ![17944, 27670, -9317, 44108, -33996], ![-17961, -27559, 9110, -43597, 33827], ![12037, 18663, -6410, 29998, -22954]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [296, 352, 458, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 328, 188], [412, 158, 299], [0, 1]]
 g := ![![[434, 98, 177], [64, 460, 61], [110, 166, 85], [427, 143], [420, 66], [297, 477, 156], [432, 77, 354], [1]], ![[186, 171, 460, 239], [8, 191, 319, 217], [32, 138, 462, 429], [483, 242], [377, 383], [357, 331, 242, 300], [322, 234, 192, 26], [331, 244, 180, 44]], ![[366, 353, 213, 111], [96, 124, 257, 178], [401, 486, 482, 78], [185, 254], [41, 4], [223, 375, 96, 439], [219, 2, 35, 391], [198, 302, 441, 443]]]
 h' := ![![[104, 328, 188], [49, 452, 385], [69, 196, 388], [300, 159, 77], [59, 276, 205], [235, 50, 287], [209, 420, 390], [191, 135, 29], [0, 1]], ![[412, 158, 299], [212, 301, 193], [9, 481, 265], [162, 159, 176], [88, 375, 27], [354, 53, 202], [300, 185, 324], [292, 266, 255], [104, 328, 188]], ![[0, 1], [481, 221, 396], [42, 297, 321], [14, 169, 234], [81, 323, 255], [464, 384, 485], [470, 369, 260], [186, 86, 203], [412, 158, 299]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 34], []]
 b := ![[], [247, 297, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [296, 352, 458, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![701237868, 376269322, 333006858, 354649547, 151054100]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-280183697, -173126439, -261898055, 354649547, 151054100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![252, 175, -26, -90, -5]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![252, 175, -26, -90, -5]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![167, 168, 1, 0, 0], ![8, 466, 0, 1, 0], ![106, 346, 0, 0, 1]] where
  M :=![![![252, 175, -26, -90, -5], ![-172, 143, 288, 4, -180], ![-1872, -1038, 251, 500, 4], ![611, 47, -288, -49, 137], ![2053, 1017, -536, -592, 178]]]
  hmulB := by decide  
  f := ![![![90450, -2435, 5524, 13184, -10193]], ![![-233584, 6373, -14208, -33996, 26368]], ![![-48942, 1347, -2969, -7116, 5531]], ![![-222641, 6075, -13542, -32403, 25133]], ![![-145847, 3987, -8866, -21222, 16468]]]
  g := ![![![12, 99, -26, -90, -5], ![-60, 25, 288, 4, -180], ![-99, -570, 251, 500, 4], ![71, 49, -288, -49, 137], ![159, 627, -536, -592, 178]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P1 : CertificateIrreducibleZModOfList' 487 2 2 8 [137, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [409, 486], [0, 1]]
 g := ![![[61, 32], [198, 89], [110, 375], [169], [83], [42, 369], [474, 382], [409, 1]], ![[0, 455], [74, 398], [80, 112], [169], [83], [480, 118], [385, 105], [331, 486]]]
 h' := ![![[409, 486], [146, 364], [27, 24], [274, 146], [138, 13], [90, 358], [320, 112], [459, 103], [0, 1]], ![[0, 1], [0, 123], [103, 463], [87, 341], [98, 474], [412, 129], [350, 375], [217, 384], [409, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [253]]
 b := ![[], [307, 370]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N1 : CertifiedPrimeIdeal' SI487N1 487 where
  n := 2
  hpos := by decide
  P := [137, 78, 1]
  hirr := P487P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12210, 15903, 11561, 10360, 10886]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6479, -21603, 11561, 10360, 10886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N1 B_one_repr
lemma NI487N1 : Nat.card (O ⧸ I487N1) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![90450, -2435, 5524, 13184, -10193]] ![![252, 175, -26, -90, -5]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -194, -46, 88, 44]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-137, -194, -46, 88, 44]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![204, 185, 385, 1, 0], ![158, 5, 144, 0, 1]] where
  M :=![![![-137, -194, -46, 88, 44], ![964, 393, -392, -276, 176], ![1720, 1332, 177, -548, -276], ![-1412, -562, 302, 283, -76], ![-2504, -1816, 162, 892, 119]]]
  hmulB := by decide  
  f := ![![![5, -46, -34, -24, -28]], ![![-740, -237, -216, -268, -48]], ![![-792, -612, -501, -476, -268]], ![![-900, -589, -489, -485, -240]], ![![-242, -199, -162, -152, -89]]]
  g := ![![![-51, -34, -82, 88, 44], ![60, 103, 164, -276, 176], ![320, 212, 511, -548, -276], ![-96, -107, -199, 283, -76], ![-414, -341, -734, 892, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [465, 380, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [327, 78, 391], [91, 412, 100], [0, 1]]
 g := ![![[107, 13, 44], [103, 102, 395], [19, 437], [141, 70, 13], [430, 48], [7, 88, 293], [44, 343, 419], [1]], ![[244, 101, 172, 166], [424, 490, 404, 72], [197, 93], [148, 14, 380, 353], [477, 233], [147, 132, 31, 458], [410, 223, 383, 122], [426, 170, 469, 167]], ![[115, 463, 242, 224], [407, 126, 122, 117], [277, 215], [385, 398, 449, 17], [390, 444], [374, 391, 266, 386], [446, 433, 358, 45], [294, 285, 464, 324]]]
 h' := ![![[327, 78, 391], [223, 148, 59], [398, 371, 262], [229, 25, 442], [114, 397, 133], [182, 340, 39], [162, 239, 463], [26, 111, 418], [0, 1]], ![[91, 412, 100], [183, 23, 179], [399, 80, 140], [396, 192, 389], [441, 35, 366], [36, 313, 235], [89, 242, 407], [474, 177, 68], [327, 78, 391]], ![[0, 1], [273, 320, 253], [339, 40, 89], [216, 274, 151], [85, 59, 483], [16, 329, 217], [192, 10, 112], [165, 203, 5], [91, 412, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 4], []]
 b := ![[], [227, 230, 275], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [465, 380, 73, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17580791, 978264, -158028, -5433324, 2265228]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1492691, 2026104, 3595680, -5433324, 2265228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -9, -2, 2, 3]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![-16, -9, -2, 2, 3]] 
 ![![491, 0, 0, 0, 0], ![282, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![276, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-16, -9, -2, 2, 3], ![68, 15, -16, -4, 4], ![32, 58, 3, -36, -4], ![-9, -21, 16, 23, -11], ![-159, -79, 8, 28, 10]]]
  hmulB := by decide  
  f := ![![![230, -519, -340, -276, -301]], ![![116, -303, -200, -164, -174]], ![![-14, -23, -17, -16, -11]], ![![107, -299, -198, -163, -171]], ![![-39, -33, -26, -26, -14]]]
  g := ![![![4, -9, -2, 2, 3], ![-6, 15, -16, -4, 4], ![-13, 58, 3, -36, -4], ![-1, -21, 16, 23, -11], ![29, -79, 8, 28, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N1 : Nat.card (O ⧸ I491N1) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N1)

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := prime_ideal_of_norm_prime hp491.out _ NI491N1

def I491N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 0, 22, 4, -12]] i)))

def SI491N2: IdealEqSpanCertificate' Table ![![-33, 0, 22, 4, -12]] 
 ![![491, 0, 0, 0, 0], ![356, 1, 0, 0, 0], ![462, 0, 1, 0, 0], ![317, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-33, 0, 22, 4, -12], ![-244, -159, 20, 76, 8], ![116, -58, -131, 0, 76], ![192, 148, 2, -69, -20], ![76, 198, 122, -72, -93]]]
  hmulB := by decide  
  f := ![![![35869, 236, 1786, 7252, -4708]], ![![25784, 169, 1284, 5212, -3384]], ![![34094, 226, 1697, 6896, -4476]], ![![22803, 148, 1136, 4607, -2992]], ![![13314, 90, 662, 2696, -1749]]]
  g := ![![![-19, 0, 22, 4, -12], ![44, -159, 20, 76, 8], ![138, -58, -131, 0, 76], ![-57, 148, 2, -69, -20], ![-178, 198, 122, -72, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI491N2 : Nat.card (O ⧸ I491N2) = 491 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI491N2)

lemma isPrimeI491N2 : Ideal.IsPrime I491N2 := prime_ideal_of_norm_prime hp491.out _ NI491N2
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-137, -194, -46, 88, 44]] ![![-16, -9, -2, 2, 3]]
  ![![-20260, -9669, 5000, 5414, -1531]] where
 M := ![![![-20260, -9669, 5000, 5414, -1531]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI491N1 : IdealMulLeCertificate' Table 
  ![![-20260, -9669, 5000, 5414, -1531]] ![![-33, 0, 22, 4, -12]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![4530948, 1745505, -1470054, -1079218, 579871]]]
 hmul := by decide  
 g := ![![![![9228, 3555, -2994, -2198, 1181]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1, I491N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
    exact isPrimeI491N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0 ⊙ MulI491N1)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3422, 138, 124, 894, -521]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![3422, 138, 124, 894, -521]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![267, 279, 123, 1, 0], ![170, 444, 48, 0, 1]] where
  M :=![![![3422, 138, 124, 894, -521], ![-12256, -497, -518, -3128, 1788], ![20938, 613, 773, 5150, -3128], ![-22417, -806, -966, -5565, 3231], ![21517, 474, 752, 5128, -3228]]]
  hmulB := by decide  
  f := ![![![-100, -150, -68, 56, 55]], ![![1184, 519, -326, -300, 112]], ![![1018, 1109, 305, -454, -300]], ![![857, 482, -143, -249, 18]], ![![1113, 514, -284, -290, 90]]]
  g := ![![![-294, -36, -170, 894, -521], ![1040, 157, 598, -3128, 1788], ![-1648, -95, -967, 5150, -3128], ![1832, 235, 1059, -5565, 3231], ![-1601, 6, -952, 5128, -3228]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [282, 154, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 212, 282], [451, 286, 217], [0, 1]]
 g := ![![[467, 359, 492], [468, 281, 247], [158, 364], [132, 30], [28, 455, 24], [323, 218, 180], [287, 135, 36], [1]], ![[159, 10, 340, 270], [203, 31, 437, 100], [356, 451], [257, 196], [183, 299, 400, 423], [314, 243, 477, 74], [96, 171, 473, 136], [335, 486, 364, 209]], ![[421, 395, 288, 470], [171, 146, 203, 398], [169, 209], [325, 81], [219, 331, 376, 403], [24, 172, 391, 148], [316, 67, 234, 248], [346, 242, 85, 290]]]
 h' := ![![[42, 212, 282], [259, 53, 196], [378, 288, 321], [460, 262, 433], [88, 80, 476], [231, 293, 460], [403, 250, 300], [217, 345, 493], [0, 1]], ![[451, 286, 217], [194, 465, 144], [272, 433, 368], [234, 457, 118], [94, 69, 14], [276, 237, 115], [390, 321, 113], [77, 132, 265], [42, 212, 282]], ![[0, 1], [87, 480, 159], [266, 277, 309], [100, 279, 447], [369, 350, 9], [54, 468, 423], [150, 427, 86], [418, 22, 240], [451, 286, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258, 63], []]
 b := ![[], [38, 246, 451], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [282, 154, 6, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343909184, 177121259, 156461591, 165731289, 62301834]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-109213741, -147743332, -46531012, 165731289, 62301834]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -18, -18, -42, 12]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-151, -18, -18, -42, 12]] 
 ![![499, 0, 0, 0, 0], ![299, 1, 0, 0, 0], ![459, 0, 1, 0, 0], ![144, 0, 0, 1, 0], ![173, 0, 0, 0, 1]] where
  M :=![![![-151, -18, -18, -42, 12], ![252, -67, -48, 24, -84], ![-1056, -216, -199, -336, 24], ![474, -96, -66, 59, -138], ![-1374, -384, -342, -486, -37]]]
  hmulB := by decide  
  f := ![![![-1393, -810, 594, 546, -264]], ![![-845, -493, 354, 330, -156]], ![![-1257, -738, 539, 498, -240]], ![![-402, -228, 174, 155, -78]], ![![-497, -282, 216, 192, -97]]]
  g := ![![![35, -18, -18, -42, 12], ![107, -67, -48, 24, -84], ![399, -216, -199, -336, 24], ![150, -96, -66, 59, -138], ![695, -384, -342, -486, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N1)

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := prime_ideal_of_norm_prime hp499.out _ NI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, -9, 24, 56, -42]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![379, -9, 24, 56, -42]] 
 ![![499, 0, 0, 0, 0], ![462, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![379, -9, 24, 56, -42], ![-960, 33, -54, -136, 112], ![1290, -17, 91, 198, -136], ![-1230, 43, -68, -173, 144], ![910, 7, 78, 152, -85]]]
  hmulB := by decide  
  f := ![![![-1919, 121, -146, -604, 318]], ![![-1762, 113, -134, -556, 292]], ![![-274, 13, -19, -82, 44]], ![![-428, 29, -34, -137, 72]], ![![-304, 19, -24, -96, 51]]]
  g := ![![![-1, -9, 24, 56, -42], ![-10, 33, -54, -136, 112], ![-20, -17, 91, 198, -136], ![-14, 43, -68, -173, 144], ![-38, 7, 78, 152, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![3422, 138, 124, 894, -521]] ![![-151, -18, -18, -42, 12]]
  ![![526720, 16614, 26282, 123876, -71647]] where
 M := ![![![526720, 16614, 26282, 123876, -71647]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![526720, 16614, 26282, 123876, -71647]] ![![379, -9, 24, 56, -42]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![14970, 186127, 123752, 119760, 92315]]]
 hmul := by decide  
 g := ![![![![30, 373, 248, 240, 185]]]]
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

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1423, 422, -574, -302, 258]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![1423, 422, -574, -302, 258]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![376, 441, 1, 0, 0], ![436, 227, 0, 1, 0], ![91, 184, 0, 0, 1]] where
  M :=![![![1423, 422, -574, -302, 258], ![5044, 4017, 212, -1808, -604], ![-7036, -1206, 3625, 1236, -1808], ![-3312, -3352, -778, 1395, 828], ![3324, -2204, -4186, 226, 2525]]]
  hmulB := by decide  
  f := ![![![19793, 166, 958, 4078, -2634]], ![![-61300, -793, -3020, -12944, 8156]], ![![-38760, -569, -1923, -8260, 5156]], ![![-10704, -217, -542, -2349, 1424]], ![![-18671, -258, -924, -3960, 2483]]]
  g := ![![![647, 546, -574, -302, 258], ![1528, 859, 212, -1808, -604], ![-3468, -3077, 3625, 1236, -1808], ![-784, -257, -778, 1395, 828], ![2483, 2640, -4186, 226, 2525]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [85, 244, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [259, 502], [0, 1]]
 g := ![![[281, 432], [139, 161], [98, 323], [329], [116, 219], [395, 231], [462, 355], [259, 1]], ![[0, 71], [89, 342], [257, 180], [329], [501, 284], [367, 272], [358, 148], [15, 502]]]
 h' := ![![[259, 502], [257, 234], [221, 302], [466, 62], [200, 143], [126, 468], [467, 57], [117, 97], [0, 1]], ![[0, 1], [0, 269], [474, 201], [428, 441], [15, 360], [115, 35], [140, 446], [90, 406], [259, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [339, 312]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 2
  hpos := by decide
  P := [85, 244, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![550, 855, -110, -1379, -201]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1315, 794, -110, -1379, -201]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, -1, 8, 26, -18]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![145, -1, 8, 26, -18]] 
 ![![503, 0, 0, 0, 0], ![210, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![156, 0, 0, 1, 0], ![270, 0, 0, 0, 1]] where
  M :=![![![145, -1, 8, 26, -18], ![-416, 1, -22, -76, 52], ![602, -1, 31, 114, -76], ![-612, 1, -32, -117, 78], ![500, 3, 26, 98, -65]]]
  hmulB := by decide  
  f := ![![![107, 49, 118, 122, 18]], ![![46, 21, 50, 52, 8]], ![![24, 11, 21, 22, 4]], ![![36, 17, 38, 39, 6]], ![![66, 31, 68, 70, 11]]]
  g := ![![![1, -1, 8, 26, -18], ![-2, 1, -22, -76, 52], ![2, -1, 31, 114, -76], ![-2, 1, -32, -117, 78], ![0, 3, 26, 98, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N1 : Nat.card (O ⧸ I503N1) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N1)

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := prime_ideal_of_norm_prime hp503.out _ NI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 0, 0, 4, -3]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![16, 0, 0, 4, -3]] 
 ![![503, 0, 0, 0, 0], ![441, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![387, 0, 0, 1, 0], ![343, 0, 0, 0, 1]] where
  M :=![![![16, 0, 0, 4, -3], ![-72, -7, -6, -20, 8], ![90, -7, -5, 18, -20], ![-129, -10, -10, -35, 15], ![77, -16, -12, 10, -24]]]
  hmulB := by decide  
  f := ![![![-490, -100, 80, 38, -15]], ![![-430, -89, 70, 34, -13]], ![![-86, -17, 13, 6, -2]], ![![-375, -76, 62, 29, -12]], ![![-337, -68, 56, 26, -11]]]
  g := ![![![-1, 0, 0, 4, -3], ![17, -7, -6, -20, 8], ![7, -7, -5, 18, -20], ![27, -10, -10, -35, 15], ![25, -16, -12, 10, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2

def I503N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -5, -2, -2, -3]] i)))

def SI503N3: IdealEqSpanCertificate' Table ![![10, -5, -2, -2, -3]] 
 ![![503, 0, 0, 0, 0], ![479, 1, 0, 0, 0], ![215, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![488, 0, 0, 0, 1]] where
  M :=![![![10, -5, -2, -2, -3], ![-76, -17, -20, -20, -4], ![-68, -56, -41, -48, -20], ![-87, -25, -28, -25, -9], ![-185, -99, -80, -92, -32]]]
  hmulB := by decide  
  f := ![![![-148, 189, 276, -40, -171]], ![![-148, 176, 264, -36, -163]], ![![-64, 77, 115, -16, -71]], ![![-27, 47, 62, -11, -39]], ![![-137, 191, 270, -42, -168]]]
  g := ![![![9, -5, -2, -2, -3], ![33, -17, -20, -20, -4], ![101, -56, -41, -48, -20], ![50, -25, -28, -25, -9], ![180, -99, -80, -92, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N3 : Nat.card (O ⧸ I503N3) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N3)

lemma isPrimeI503N3 : Ideal.IsPrime I503N3 := prime_ideal_of_norm_prime hp503.out _ NI503N3
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![1423, 422, -574, -302, 258]] ![![145, -1, 8, 26, -18]]
  ![![-941, 45, 678, 108, -372]] where
 M := ![![![-941, 45, 678, 108, -372]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![-941, 45, 678, 108, -372]] ![![16, 0, 0, 4, -3]]
  ![![148, -189, -276, 40, 171]] where
 M := ![![![148, -189, -276, 40, 171]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N2 : IdealMulLeCertificate' Table 
  ![![148, -189, -276, 40, 171]] ![![10, -5, -2, -2, -3]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![-503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1, I503N2, I503N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
    exact isPrimeI503N2
    exact isPrimeI503N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0 ⊙ MulI503N1 ⊙ MulI503N2)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1488, -14, 26, 320, -243]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![1488, -14, 26, 320, -243]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![306, 450, 474, 1, 0], ![334, 25, 268, 0, 1]] where
  M :=![![![1488, -14, 26, 320, -243], ![-5780, -405, -462, -1456, 640], ![7218, -507, -227, 1350, -1456], ![-9765, -612, -740, -2447, 1123], ![5861, -1092, -738, 754, -1644]]]
  hmulB := by decide  
  f := ![![![1866, -58, 118, 278, -213]], ![![-4876, 109, -306, -700, 556]], ![![6366, -133, 359, 894, -700]], ![![2727, -62, 134, 379, -287]], ![![4345, -103, 252, 620, -482]]]
  g := ![![![-30, -271, -170, 320, -243], ![444, 1255, 1018, -1456, 640], ![158, -1123, -491, 1350, -1456], ![715, 2107, 1686, -2447, 1123], ![637, -588, 162, 754, -1644]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 3 2 8 [109, 70, 268, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 148, 307], [128, 360, 202], [0, 1]]
 g := ![![[55, 210, 158], [470, 310], [66, 243, 223], [81, 21, 185], [437, 207, 409], [463, 177, 472], [336, 384, 55], [1]], ![[387, 476, 82, 312], [362, 25], [135, 192, 286, 366], [47, 446, 204, 354], [307, 394, 41, 334], [232, 329, 344, 446], [298, 114, 440, 86], [133, 284, 157, 338]], ![[290, 96, 311, 423], [417, 406], [81, 441, 175, 76], [264, 2, 205, 200], [155, 236, 373, 312], [183, 477, 361, 205], [389, 288, 223, 139], [286, 21, 100, 171]]]
 h' := ![![[113, 148, 307], [222, 499, 61], [441, 378, 58], [333, 253, 188], [213, 469, 328], [433, 282, 44], [24, 459, 245], [400, 439, 241], [0, 1]], ![[128, 360, 202], [411, 208, 57], [26, 299, 5], [69, 124, 286], [499, 261, 437], [107, 14, 105], [214, 139, 63], [146, 139, 118], [113, 148, 307]], ![[0, 1], [73, 311, 391], [494, 341, 446], [289, 132, 35], [73, 288, 253], [338, 213, 360], [44, 420, 201], [456, 440, 150], [128, 360, 202]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183, 278], []]
 b := ![[], [346, 317, 208], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 3
  hpos := by decide
  P := [109, 70, 268, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104720058, 58110331, 51322726, 54048438, 24359016]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48271146, -48865741, -63056686, 54048438, 24359016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 131872229 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1866, -58, 118, 278, -213]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![1866, -58, 118, 278, -213]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![424, 106, 1, 0, 0], ![487, 277, 0, 1, 0], ![109, 172, 0, 0, 1]] where
  M :=![![![1866, -58, 118, 278, -213], ![-4876, 109, -306, -700, 556], ![6366, -133, 359, 894, -700], ![-6237, 182, -368, -913, 695], ![4173, -136, 294, 636, -496]]]
  hmulB := by decide  
  f := ![![![1488, -14, 26, 320, -243]], ![![-5780, -405, -462, -1456, 640]], ![![50, -97, -75, -34, -72]], ![![-1741, -235, -228, -491, 118]], ![![-1623, -142, -152, -422, 161]]]
  g := ![![![-315, -104, 118, 278, -213], ![796, 257, -306, -700, 556], ![-992, -325, 359, 894, -700], ![1019, 339, -368, -913, 695], ![-739, -240, 294, 636, -496]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P1 : CertificateIrreducibleZModOfList' 509 2 2 8 [428, 342, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 508], [0, 1]]
 g := ![![[222, 465], [342], [271, 275], [241, 224], [82, 187], [331, 359], [141, 116], [167, 1]], ![[0, 44], [342], [386, 234], [492, 285], [262, 322], [222, 150], [171, 393], [334, 508]]]
 h' := ![![[167, 508], [240, 90], [64, 318], [179, 481], [25, 407], [343, 218], [223, 195], [293, 484], [0, 1]], ![[0, 1], [0, 419], [234, 191], [84, 28], [297, 102], [101, 291], [212, 314], [190, 25], [167, 508]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [358, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N1 : CertifiedPrimeIdeal' SI509N1 509 where
  n := 2
  hpos := by decide
  P := [428, 342, 1]
  hirr := P509P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11973, 13235, 7598, 4767, 14067]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13879, -8904, 7598, 4767, 14067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N1 B_one_repr
lemma NI509N1 : Nat.card (O ⧸ I509N1) = 259081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![1488, -14, 26, 320, -243]] ![![1866, -58, 118, 278, -213]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB519I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 518 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 518 (by omega)

def PB519I10 : PrimesBelowBoundCertificateInterval O 463 518 519 where
  m := 7
  g := ![1, 2, 2, 3, 3, 4, 2]
  P := ![467, 479, 487, 491, 499, 503, 509]
  hP := PB519I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1, I491N2]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1, I503N2, I503N3]
    · exact ![I509N0, I509N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![22211833167107]
    · exact ![109902239, 229441]
    · exact ![115501303, 237169]
    · exact ![118370771, 491, 491]
    · exact ![124251499, 499, 499]
    · exact ![253009, 503, 503, 503]
    · exact ![131872229, 259081]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
      exact NI491N2
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
      exact NI499N2
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
      exact NI503N3
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
  β := ![I491N1, I491N2, I499N1, I499N2, I503N1, I503N2, I503N3]
  Il := ![[], [], [], [I491N1, I491N2], [I499N1, I499N2], [I503N1, I503N2, I503N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
