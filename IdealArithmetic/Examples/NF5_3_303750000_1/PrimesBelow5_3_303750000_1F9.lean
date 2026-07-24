
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, -5, 6, -7]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![5, 5, -5, 6, -7]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![60, 399, 1, 0, 0], ![244, 184, 0, 1, 0], ![346, 293, 0, 0, 1]] where
  M :=![![![5, 5, -5, 6, -7], ![8, -9, 42, -24, 34], ![-4, 22, -43, 34, -36], ![44, -40, 230, -137, 198], ![14, 50, -28, 44, -31]]]
  hmulB := by decide  
  f := ![![![139, -21, 73, 16, -37]], ![![-84, -129, -130, 4, 54]], ![![-60, -125, -113, 6, 46]], ![![44, -68, -14, 11, 2]], ![![56, -107, -30, 16, 7]]]
  g := ![![![3, 7, -5, 6, -7], ![-20, -53, 42, -24, 34], ![16, 51, -43, 34, -36], ![-116, -296, 230, -137, 198], ![4, 29, -28, 44, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 2 2 8 [404, 406, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 420], [0, 1]]
 g := ![![[199, 99], [418], [25, 409], [155], [112], [58, 317], [45], [15, 1]], ![[0, 322], [418], [266, 12], [155], [112], [182, 104], [45], [30, 420]]]
 h' := ![![[15, 420], [386, 283], [4, 41], [104, 339], [327, 24], [144, 310], [114, 321], [255, 242], [0, 1]], ![[0, 1], [0, 138], [198, 380], [137, 82], [266, 397], [163, 111], [298, 100], [96, 179], [15, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [250]]
 b := ![[], [115, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 2
  hpos := by decide
  P := [404, 406, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83102, 85350, 144516, -6923, 87626]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-88402, -194720, 144516, -6923, 87626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 20, 24, 1, -11]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![15, 20, 24, 1, -11]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![242, 173, 1, 0, 0], ![261, 14, 0, 1, 0], ![359, 109, 0, 0, 1]] where
  M :=![![![15, 20, 24, 1, -11], ![20, -52, 49, 11, -14], ![-40, -30, -81, 0, 24], ![-32, 73, -47, -46, 58], ![22, 85, 31, -3, -21]]]
  hmulB := by decide  
  f := ![![![309, 54, 104, 21, -21]], ![![108, 196, 175, 41, 126]], ![![222, 112, 132, 29, 40]], ![![197, 43, 73, 15, -7]], ![![293, 99, 136, 29, 16]]]
  g := ![![![-5, -7, 24, 1, -11], ![-23, -17, 49, 11, -14], ![26, 27, -81, 0, 24], ![6, 6, -47, -46, 58], ![2, -7, 31, -3, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P1 : CertificateIrreducibleZModOfList' 421 2 2 8 [15, 368, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 420], [0, 1]]
 g := ![![[221, 393], [240], [200, 314], [327], [31], [69, 190], [254], [53, 1]], ![[0, 28], [240], [2, 107], [327], [31], [35, 231], [254], [106, 420]]]
 h' := ![![[53, 420], [51, 285], [368, 161], [378, 387], [157, 300], [228, 118], [83, 343], [47, 268], [0, 1]], ![[0, 1], [0, 136], [60, 260], [260, 34], [59, 121], [167, 303], [159, 78], [358, 153], [53, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [387]]
 b := ![[], [240, 404]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N1 : CertifiedPrimeIdeal' SI421N1 421 where
  n := 2
  hpos := by decide
  P := [15, 368, 1]
  hirr := P421P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159712, 165791, 280086, -18844, 184872]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-306584, -161939, 280086, -18844, 184872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N1 B_one_repr
lemma NI421N1 : Nat.card (O ⧸ I421N1) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -5, -17, -3, 10]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![-69, -5, -17, -3, 10]] 
 ![![421, 0, 0, 0, 0], ![240, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![282, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![-69, -5, -17, -3, 10], ![4, -6, -5, -1, -4], ![28, -2, 3, 0, -8], ![12, -33, -21, -6, -28], ![-12, -27, -21, -5, -17]]]
  hmulB := by decide  
  f := ![![![-29, 167, -271, 195, -250]], ![![-16, 94, -151, 109, -140]], ![![-5, 27, -46, 33, -42]], ![![-18, 105, -165, 118, -152]], ![![-16, 91, -149, 107, -137]]]
  g := ![![![2, -5, -17, -3, 10], ![7, -6, -5, -1, -4], ![5, -2, 3, 0, -8], ![41, -33, -21, -6, -28], ![31, -27, -21, -5, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![5, 5, -5, 6, -7]] ![![15, 20, 24, 1, -11]]
  ![![29, -167, 271, -195, 250]] where
 M := ![![![29, -167, 271, -195, 250]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![29, -167, 271, -195, 250]] ![![-69, -5, -17, -3, 10]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-421, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1, I421N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
    exact isPrimeI421N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0 ⊙ MulI421N1)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54933, 2661, 12961, 2308, -8653]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![54933, 2661, 12961, 2308, -8653]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![264, 109, 221, 1, 0], ![343, 268, 227, 0, 1]] where
  M :=![![![54933, 2661, 12961, 2308, -8653], ![-7368, -361, -1738, -308, 1158], ![-25380, -1232, -5991, -1068, 4000], ![-29348, -1418, -6938, -1231, 4614], ![-5126, -248, -1208, -218, 805]]]
  hmulB := by decide  
  f := ![![![9, -7, 21, 2, -9]], ![![-28, -67, -50, 8, -2]], ![![-28, 12, -45, -20, 20]], ![![-16, -15, -23, -7, 4]], ![![-25, -41, -38, -4, 2]]]
  g := ![![![5600, 4803, 3404, 2308, -8653], ![-750, -643, -456, -308, 1158], ![-2588, -2220, -1573, -1068, 4000], ![-2986, -2561, -1815, -1231, 4614], ![-519, -446, -315, -218, 805]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 3 2 8 [416, 194, 416, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [236, 392, 392], [210, 38, 39], [0, 1]]
 g := ![![[418, 120, 138], [389, 321, 273], [3, 87, 405], [423, 260, 297], [109, 212], [320, 135, 1], [141, 225], [1]], ![[11, 337, 370, 183], [16, 27, 89, 116], [279, 12, 245, 307], [429, 384, 411, 22], [201, 24], [30, 180, 252, 285], [37, 223], [388, 292, 276, 159]], ![[66, 348, 111, 279], [191, 77, 160, 137], [326, 45, 288, 344], [90, 398, 402, 201], [421, 352], [375, 62, 353, 356], [154, 151], [310, 181, 333, 272]]]
 h' := ![![[236, 392, 392], [232, 334, 210], [45, 38, 370], [311, 399, 336], [375, 228, 177], [59, 30, 387], [185, 371, 430], [15, 237, 15], [0, 1]], ![[210, 38, 39], [328, 264, 126], [238, 199, 79], [318, 100, 224], [30, 93, 420], [110, 417, 175], [196, 368, 147], [266, 80, 378], [236, 392, 392]], ![[0, 1], [224, 264, 95], [21, 194, 413], [224, 363, 302], [287, 110, 265], [303, 415, 300], [299, 123, 285], [12, 114, 38], [210, 38, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 333], []]
 b := ![[], [24, 137, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 3
  hpos := by decide
  P := [416, 194, 416, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-503661, -646723, -501406, -349514, 9943]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![205006, 80709, 172817, -349514, 9943]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 80062991 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -7, 21, 2, -9]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![9, -7, 21, 2, -9]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![85, 376, 1, 0, 0], ![142, 373, 0, 1, 0], ![181, 99, 0, 0, 1]] where
  M :=![![![9, -7, 21, 2, -9], ![-28, -67, -50, 8, -2], ![-28, 12, -45, -20, 20], ![-32, 34, -62, 3, -102], ![-2, -38, 34, -14, -55]]]
  hmulB := by decide  
  f := ![![![54933, 2661, 12961, 2308, -8653]], ![![-7368, -361, -1738, -308, 1158]], ![![4347, 207, 1026, 184, -687]], ![![11654, 561, 2750, 491, -1838]], ![![21365, 1034, 5041, 898, -3366]]]
  g := ![![![-1, -18, 21, 2, -9], ![8, 37, -50, 8, -2], ![7, 52, -45, -20, 20], ![54, 75, -62, 3, -102], ![21, -5, 34, -14, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P1 : CertificateIrreducibleZModOfList' 431 2 2 8 [158, 377, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 430], [0, 1]]
 g := ![![[327, 244], [110, 121], [291, 318], [342, 123], [41], [127, 207], [276], [54, 1]], ![[142, 187], [179, 310], [223, 113], [88, 308], [41], [99, 224], [276], [108, 430]]]
 h' := ![![[54, 430], [291, 109], [139, 11], [270, 201], [264, 135], [191, 104], [340, 352], [88, 172], [0, 1]], ![[0, 1], [143, 322], [302, 420], [349, 230], [227, 296], [204, 327], [384, 79], [325, 259], [54, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [251, 294]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N1 : CertifiedPrimeIdeal' SI431N1 431 where
  n := 2
  hpos := by decide
  P := [158, 377, 1]
  hirr := P431P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![441562, 506670, 796110, -108621, 684459]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-407635, -756558, 796110, -108621, 684459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N1 B_one_repr
lemma NI431N1 : Nat.card (O ⧸ I431N1) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![54933, 2661, 12961, 2308, -8653]] ![![9, -7, 21, 2, -9]]
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

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, -39, -185, -34, 125]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![-789, -39, -185, -34, 125]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![299, 338, 1, 0, 0], ![283, 380, 0, 1, 0], ![146, 198, 0, 0, 1]] where
  M :=![![![-789, -39, -185, -34, 125], ![104, 5, 18, 8, -22], ![364, 14, 91, 10, -52], ![412, 24, 62, 37, -98], ![70, -6, 20, -4, -9]]]
  hmulB := by decide  
  f := ![![![73, 87, 141, 4, -57]], ![![68, -311, 166, 76, -82]], ![![103, -183, 226, 62, -103]], ![![107, -215, 237, 69, -109]], ![![56, -112, 124, 36, -57]]]
  g := ![![![106, 117, -185, -34, 125], ![-10, -11, 18, 8, -22], ![-51, -56, 91, 10, -52], ![-33, -36, 62, 37, -98], ![-8, -8, 20, -4, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 2 2 8 [161, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [306, 432], [0, 1]]
 g := ![![[380, 78], [329], [223], [136], [31, 274], [109, 79], [211], [306, 1]], ![[0, 355], [329], [223], [136], [306, 159], [35, 354], [211], [179, 432]]]
 h' := ![![[306, 432], [322, 98], [391, 187], [211, 400], [205, 60], [204, 131], [359, 265], [96, 380], [0, 1]], ![[0, 1], [0, 335], [24, 246], [72, 33], [379, 373], [21, 302], [45, 168], [332, 53], [306, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [391]]
 b := ![[], [182, 412]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 2
  hpos := by decide
  P := [161, 127, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![180313, 193799, 329423, -40612, 253847]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-286110, -337137, 329423, -40612, 253847]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-279, -14, -56, -17, 53]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![-279, -14, -56, -17, 53]] 
 ![![433, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![165, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![-279, -14, -56, -17, 53], ![44, 30, -15, 31, -30], ![144, 0, 89, -26, 28], ![192, 175, -91, 174, -154], ![78, 43, 119, -25, 81]]]
  hmulB := by decide  
  f := ![![![-1441, 12032, -3944, -2617, 1787]], ![![-108, 1374, -337, -283, 158]], ![![-214, 1642, -573, -362, 258]], ![![-637, 4515, -1673, -1009, 749]], ![![-323, 2411, -859, -534, 386]]]
  g := ![![![5, -14, -56, -17, 53], ![-7, 30, -15, 31, -30], ![-8, 0, 89, -26, 28], ![-42, 175, -91, 174, -154], ![-28, 43, 119, -25, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1

def I433N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2279, -106, -542, -91, 355]] i)))

def SI433N2: IdealEqSpanCertificate' Table ![![-2279, -106, -542, -91, 355]] 
 ![![433, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![103, 0, 0, 0, 1]] where
  M :=![![![-2279, -106, -542, -91, 355], ![316, 14, 109, -5, -18], ![1056, 74, 221, 72, -192], ![1280, 61, 501, -48, -18], ![242, 73, 51, 49, -43]]]
  hmulB := by decide  
  f := ![![![12407, 25788, 22610, -1267, -8791]], ![![4428, 8958, 8091, -407, -3150]], ![![824, 1788, 1495, -98, -580]], ![![2253, 5101, 4069, -307, -1575]], ![![2983, 6349, 5423, -332, -2106]]]
  g := ![![![5, -106, -542, -91, 355], ![-7, 14, 109, -5, -18], ![-8, 74, 221, 72, -192], ![-42, 61, 501, -48, -18], ![-28, 73, 51, 49, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N2 : Nat.card (O ⧸ I433N2) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N2)

lemma isPrimeI433N2 : Ideal.IsPrime I433N2 := prime_ideal_of_norm_prime hp433.out _ NI433N2

def I433N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -135, -117, -28, -85]] i)))

def SI433N3: IdealEqSpanCertificate' Table ![![-65, -135, -117, -28, -85]] 
 ![![433, 0, 0, 0, 0], ![181, 1, 0, 0, 0], ![425, 0, 1, 0, 0], ![322, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![-65, -135, -117, -28, -85], ![-496, -677, -620, -146, -394], ![-452, -602, -553, -130, -348], ![-3108, -4258, -3896, -917, -2478], ![-2262, -3112, -2846, -670, -1813]]]
  hmulB := by decide  
  f := ![![![-219, 123, -1019, 502, -507]], ![![-91, 50, -419, 204, -205]], ![![-215, 125, -1008, 500, -507]], ![![-158, 72, -714, 343, -340]], ![![-131, 75, -613, 304, -308]]]
  g := ![![![242, -135, -117, -28, -85], ![1231, -677, -620, -146, -394], ![1095, -602, -553, -130, -348], ![7738, -4258, -3896, -917, -2478], ![5655, -3112, -2846, -670, -1813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N3 : Nat.card (O ⧸ I433N3) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N3)

lemma isPrimeI433N3 : Ideal.IsPrime I433N3 := prime_ideal_of_norm_prime hp433.out _ NI433N3
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![-789, -39, -185, -34, 125]] ![![-279, -14, -56, -17, 53]]
  ![![194997, 9301, 46273, 7973, -30466]] where
 M := ![![![194997, 9301, 46273, 7973, -30466]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N1 : IdealMulLeCertificate' Table 
  ![![194997, 9301, 46273, 7973, -30466]] ![![-2279, -106, -542, -91, 355]]
  ![![-389762091, -18852931, -92007525, -16335114, 61338625]] where
 M := ![![![-389762091, -18852931, -92007525, -16335114, 61338625]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI433N2 : IdealMulLeCertificate' Table 
  ![![-389762091, -18852931, -92007525, -16335114, 61338625]] ![![-65, -135, -117, -28, -85]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![-11705444447, -561038966, -2756979414, -490734488, 1847936616]]]
 hmul := by decide  
 g := ![![![![-27033359, -1295702, -6367158, -1133336, 4267752]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1, I433N2, I433N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
    exact isPrimeI433N2
    exact isPrimeI433N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0 ⊙ MulI433N1 ⊙ MulI433N2)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 0, 0, 0, 0]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![439, 0, 0, 0, 0]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![0, 0, 0, 439, 0], ![0, 0, 0, 0, 439]] where
  M :=![![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![0, 0, 0, 439, 0], ![0, 0, 0, 0, 439]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 5 2 8 [358, 184, 305, 201, 207, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 37, 80, 111, 23], [339, 231, 412, 187, 334], [293, 297, 395, 70, 415], [426, 312, 430, 71, 106], [0, 1]]
 g := ![![[44, 157, 153, 269, 380], [156, 82, 76, 146, 152], [416, 111, 79, 198, 408], [184, 167, 405, 250], [204, 428, 269, 53, 433], [364, 411, 134, 203, 274], [232, 1], []], ![[155, 27, 267, 272, 334, 243, 64, 213], [301, 158, 69, 431, 373, 434, 296, 293], [402, 434, 229, 180, 327, 330, 379, 340], [401, 197, 182, 126], [427, 172, 352, 78, 318, 219, 281, 277], [378, 92, 68, 409, 258, 181, 336, 43], [265, 386, 243, 245], [140, 326, 260, 77, 178, 269, 92, 314]], ![[421, 63, 4, 33, 303, 288, 213, 109], [50, 53, 367, 233, 82, 289, 329, 232], [384, 324, 30, 266, 236, 352, 394, 377], [138, 435, 160, 234], [256, 301, 289, 124, 287, 259, 2, 250], [286, 171, 347, 160, 379, 117, 326, 398], [293, 332, 210, 140], [87, 340, 50, 415, 370, 210, 179, 18]], ![[79, 338, 193, 222, 399, 417, 260, 81], [256, 323, 16, 361, 75, 98, 95, 95], [312, 378, 327, 211, 323, 348, 73, 130], [323, 50, 106, 254], [326, 333, 435, 280, 369, 436, 377, 361], [270, 256, 423, 149, 258, 189, 13, 22], [280, 275, 39, 171], [329, 139, 121, 350, 412, 228, 401, 224]], ![[198, 152, 361, 135, 350, 242, 192, 127], [66, 32, 13, 31, 218, 372, 92, 382], [186, 112, 151, 183, 11, 335, 168, 98], [414, 402, 252, 76], [176, 364, 102, 114, 206, 186, 423, 129], [90, 12, 388, 203, 405, 111, 29, 113], [192, 420, 130, 331], [168, 362, 152, 209, 290, 128, 172, 9]]]
 h' := ![![[52, 37, 80, 111, 23], [344, 362, 59, 399, 281], [332, 29, 184, 270, 213], [358, 232, 322, 204, 59], [281, 417, 306, 150, 108], [71, 319, 378, 7, 260], [354, 415, 174, 36, 65], [0, 0, 0, 1], [0, 1]], ![[339, 231, 412, 187, 334], [363, 67, 283, 322, 55], [179, 268, 97, 134, 52], [269, 310, 48, 214, 54], [374, 137, 321, 62, 141], [436, 300, 363, 192, 77], [236, 264, 362, 329, 331], [54, 75, 358, 356, 95], [52, 37, 80, 111, 23]], ![[293, 297, 395, 70, 415], [409, 349, 78, 336, 80], [294, 434, 291, 104, 132], [319, 88, 98, 424, 130], [217, 195, 414, 398, 371], [320, 251, 418, 234, 259], [301, 177, 2, 223, 215], [65, 64, 350, 140, 214], [339, 231, 412, 187, 334]], ![[426, 312, 430, 71, 106], [322, 15, 386, 157, 195], [309, 252, 80, 328, 337], [395, 292, 75, 138, 122], [198, 400, 250, 11, 80], [134, 114, 234, 258, 119], [123, 117, 135, 232, 228], [244, 429, 24, 239, 267], [293, 297, 395, 70, 415]], ![[0, 1], [376, 85, 72, 103, 267], [88, 334, 226, 42, 144], [2, 395, 335, 337, 74], [195, 168, 26, 257, 178], [1, 333, 363, 187, 163], [196, 344, 205, 58, 39], [436, 310, 146, 142, 302], [426, 312, 430, 71, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 367, 210, 77], [], [], []]
 b := ![[], [337, 116, 383, 358, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 5
  hpos := by decide
  P := [358, 184, 305, 201, 207, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![807517674634, -2436799698620, 6748290071240, -4741505947880, 5889732478656]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1839448006, -5550796580, 15371959160, -10800696920, 13416247104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 16305067506199 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def PBC439 : ContainsPrimesAboveP 439 ![I439N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![439, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 439 (by decide) 𝕀

instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 320, 170, -19, -81]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![103, 320, 170, -19, -81]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![387, 160, 4, 1, 0], ![165, 139, 79, 0, 1]] where
  M :=![![![103, 320, 170, -19, -81], ![440, -290, 953, 127, -314], ![-400, -664, -803, 74, 216], ![-708, 303, -1191, -534, 926], ![6, 1029, -147, -113, -41]]]
  hmulB := by decide  
  f := ![![![-621, 38, -94, -13, 147]], ![![344, 354, 341, 79, 190]], ![![536, 326, 357, 80, 132]], ![![-409, 169, 49, 19, 201]], ![![-25, 187, 139, 35, 140]]]
  g := ![![![47, 33, 15, -19, -81], ![7, 52, 57, 127, -314], ![-146, -96, -41, 74, 216], ![120, -97, -163, -534, 926], ![114, 56, 8, -113, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [93, 363, 196, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [307, 302, 267], [383, 140, 176], [0, 1]]
 g := ![![[192, 350, 130], [144, 136, 90], [347, 59], [142, 195, 12], [362, 9, 41], [230, 242, 250], [228, 318], [1]], ![[400, 362, 154, 315], [13, 202, 361, 17], [331, 420], [146, 89, 276, 47], [29, 69, 320, 437], [110, 358, 366, 36], [210, 265], [356, 300, 406, 225]], ![[50, 270, 431, 343], [231, 306, 171, 334], [24, 105], [57, 147, 245, 18], [424, 104, 206, 290], [197, 229, 384, 408], [311, 160], [156, 180, 139, 218]]]
 h' := ![![[307, 302, 267], [341, 168, 243], [36, 219, 166], [84, 317, 67], [2, 142, 101], [317, 89, 421], [292, 366, 129], [350, 80, 247], [0, 1]], ![[383, 140, 176], [169, 92, 22], [409, 240, 201], [418, 98, 103], [98, 441, 223], [223, 433, 305], [187, 259, 159], [15, 152, 122], [307, 302, 267]], ![[0, 1], [12, 183, 178], [204, 427, 76], [211, 28, 273], [417, 303, 119], [360, 364, 160], [69, 261, 155], [295, 211, 74], [383, 140, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [336, 325], []]
 b := ![[], [5, 407, 246], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [93, 363, 196, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3519688259, 4248743343, 5427674541, 166227888, 3790023493]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1548903794, -1239641048, -665122106, 166227888, 3790023493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -18, 54, -37, 47]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![7, -18, 54, -37, 47]] 
 ![![443, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![394, 0, 1, 0, 0], ![163, 0, 0, 1, 0], ![137, 0, 0, 0, 1]] where
  M :=![![![7, -18, 54, -37, 47], ![-16, 106, -227, 175, -202], ![40, -110, 317, -220, 276], ![-84, 605, -1271, 988, -1134], ![78, -85, 409, -247, 347]]]
  hmulB := by decide  
  f := ![![![-3501, 432, -1258, -307, 723]], ![![-1150, 146, -409, -101, 236]], ![![-3110, 380, -1117, -272, 642]], ![![-1289, 153, -471, -113, 269]], ![![-1085, 135, -395, -96, 226]]]
  g := ![![![-43, -18, 54, -37, 47], ![165, 106, -227, 175, -202], ![-250, -110, 317, -220, 276], ![918, 605, -1271, 988, -1134], ![-352, -85, 409, -247, 347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N1 : Nat.card (O ⧸ I443N1) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N1)

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := prime_ideal_of_norm_prime hp443.out _ NI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 17, -27, -7, 10]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![-13, 17, -27, -7, 10]] 
 ![![443, 0, 0, 0, 0], ![293, 1, 0, 0, 0], ![172, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![409, 0, 0, 0, 1]] where
  M :=![![![-13, 17, -27, -7, 10], ![40, 70, 77, -3, -36], ![12, -74, 33, 16, -20], ![-104, -171, -175, -6, 32], ![-80, -27, -145, -23, 31]]]
  hmulB := by decide  
  f := ![![![-473675, -22933, -111763, -19891, 74594]], ![![-313145, -15161, -73886, -13150, 49314]], ![![-183416, -8880, -43277, -7702, 28884]], ![![-136292, -6599, -32157, -5724, 21464]], ![![-437221, -21168, -103162, -18360, 68853]]]
  g := ![![![-8, 17, -27, -7, 10], ![-42, 70, 77, -3, -36], ![50, -74, 33, 16, -20], ![153, -171, -175, -6, 32], ![52, -27, -145, -23, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![103, 320, 170, -19, -81]] ![![7, -18, 54, -37, 47]]
  ![![-2321, 8756, -22168, 16024, -19440]] where
 M := ![![![-2321, 8756, -22168, 16024, -19440]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![-2321, 8756, -22168, 16024, -19440]] ![![-13, 17, -27, -7, 10]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![3101, -1329, 19935, -13733, 15062]]]
 hmul := by decide  
 g := ![![![![7, -3, 45, -31, 34]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1, I443N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
    exact isPrimeI443N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0 ⊙ MulI443N1)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -73, 71, 20, -39]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![31, -73, 71, 20, -39]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![64, 431, 1, 0, 0], ![146, 78, 0, 1, 0], ![110, 366, 0, 0, 1]] where
  M :=![![![31, -73, 71, 20, -39], ![-184, -287, -322, -8, 82], ![-76, 188, -149, -64, 24], ![36, 114, 198, -69, -358], ![30, -240, 180, 10, -281]]]
  hmulB := by decide  
  f := ![![![813, -1003, 2741, -1870, 2211]], ![![-1324, 4725, -12022, 8692, -10538]], ![![-1152, 4379, -11115, 8052, -9770]], ![![18, 554, -1348, 1011, -1244]], ![![-876, 3590, -9088, 6598, -8013]]]
  g := ![![![-7, -40, 71, 20, -39], ![28, 243, -322, -8, 82], ![36, 135, -149, -64, 24], ![82, 114, 198, -69, -358], ![40, 54, 180, 10, -281]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 2 2 8 [105, 387, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 448], [0, 1]]
 g := ![![[55, 186], [186], [199], [194], [25], [287], [89, 57], [62, 1]], ![[362, 263], [186], [199], [194], [25], [287], [31, 392], [124, 448]]]
 h' := ![![[62, 448], [370, 138], [12, 311], [409, 358], [141, 207], [269, 444], [84, 319], [225, 147], [0, 1]], ![[0, 1], [395, 311], [436, 138], [155, 91], [403, 242], [408, 5], [106, 130], [359, 302], [62, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [315, 294]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 2
  hpos := by decide
  P := [105, 387, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![419, 1292, 1848, -2091, 4451]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-673, -5036, 1848, -2091, 4451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -28, -56, -11, 13]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![-173, -28, -56, -11, 13]] 
 ![![449, 0, 0, 0, 0], ![219, 1, 0, 0, 0], ![303, 0, 1, 0, 0], ![168, 0, 0, 1, 0], ![317, 0, 0, 0, 1]] where
  M :=![![![-173, -28, -56, -11, 13], ![-52, -100, -87, -21, -62], ![8, -86, -65, -16, -64], ![-376, -631, -559, -134, -382], ![-322, -463, -421, -99, -273]]]
  hmulB := by decide  
  f := ![![![-59, -2162, 72, 389, -73]], ![![-37, -1058, 19, 188, -29]], ![![-37, -1446, 53, 261, -51]], ![![-8, -803, 55, 148, -38]], ![![-37, -1537, 61, 278, -56]]]
  g := ![![![46, -28, -56, -11, 13], ![159, -100, -87, -21, -62], ![137, -86, -65, -16, -64], ![1004, -631, -559, -134, -382], ![739, -463, -421, -99, -273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N1 : Nat.card (O ⧸ I449N1) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N1)

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := prime_ideal_of_norm_prime hp449.out _ NI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, -326, 544, 132, -226]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![257, -326, 544, 132, -226]] 
 ![![449, 0, 0, 0, 0], ![337, 1, 0, 0, 0], ![260, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![257, -326, 544, 132, -226], ![-840, -1573, -1546, 54, 604], ![-376, 1286, -867, -342, 372], ![1416, 2696, 2602, -99, -1016], ![1188, 92, 2374, 316, -963]]]
  hmulB := by decide  
  f := ![![![-90551, -4214, -21144, -3816, 14466]], ![![-67935, -3159, -15862, -2862, 10854]], ![![-52340, -2434, -12219, -2206, 8364]], ![![-16621, -758, -3874, -695, 2662]], ![![-39703, -1838, -9262, -1672, 6351]]]
  g := ![![![5, -326, 544, 132, -226], ![1799, -1573, -1546, 54, 604], ![-564, 1286, -867, -342, 372], ![-3063, 2696, 2602, -99, -1016], ![-1077, 92, 2374, 316, -963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2

def I449N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 66, 74, -1, -29]] i)))

def SI449N3: IdealEqSpanCertificate' Table ![![39, 66, 74, -1, -29]] 
 ![![449, 0, 0, 0, 0], ![415, 1, 0, 0, 0], ![169, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![351, 0, 0, 0, 1]] where
  M :=![![![39, 66, 74, -1, -29], ![72, -146, 157, 47, -66], ![-120, -118, -231, -12, 92], ![-124, 245, -271, -80, 114], ![62, 263, 101, -31, -37]]]
  hmulB := by decide  
  f := ![![![-471, 268, -42, 115, 141]], ![![-433, 250, -35, 106, 133]], ![![-175, 104, -15, 45, 53]], ![![-32, 41, 19, 10, 30]], ![![-359, 223, -23, 94, 116]]]
  g := ![![![-66, 66, 74, -1, -29], ![123, -146, 157, 47, -66], ![125, -118, -231, -12, 92], ![-206, 245, -271, -80, 114], ![-249, 263, 101, -31, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N3 : Nat.card (O ⧸ I449N3) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N3)

lemma isPrimeI449N3 : Ideal.IsPrime I449N3 := prime_ideal_of_norm_prime hp449.out _ NI449N3
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![31, -73, 71, 20, -39]] ![![-173, -28, -56, -11, 13]]
  ![![4039, 5763, 5239, 1237, 3392]] where
 M := ![![![4039, 5763, 5239, 1237, 3392]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![4039, 5763, 5239, 1237, 3392]] ![![257, -326, 544, 132, -226]]
  ![![8527, 2457, 16687, 2021, -6342]] where
 M := ![![![8527, 2457, 16687, 2021, -6342]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N2 : IdealMulLeCertificate' Table 
  ![![8527, 2457, 16687, 2021, -6342]] ![![39, 66, 74, -1, -29]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![-2136791, -2937807, -4026183, -58370, 1590807]]]
 hmul := by decide  
 g := ![![![![-4759, -6543, -8967, -130, 3543]]]]
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

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1625, -129, 617, 133, -352]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![1625, -129, 617, 133, -352]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![0, 0, 457, 0, 0], ![0, 0, 0, 457, 0], ![59, 51, 415, 245, 1]] where
  M :=![![![1625, -129, 617, 133, -352], ![-696, -834, -953, -1, 360], ![-876, 668, -577, -214, 264], ![-136, 1145, 1127, -100, -560], ![380, -175, 1085, 145, -559]]]
  hmulB := by decide  
  f := ![![![-11, 43, -109, 79, -96]], ![![52, -198, 501, -363, 440]], ![![-68, 254, -647, 468, -568]], ![![292, -1115, 2821, -2046, 2480]], ![![99, -383, 965, -701, 849]]]
  g := ![![![49, 39, 321, 189, -352], ![-48, -42, -329, -193, 360], ![-36, -28, -241, -142, 264], ![72, 65, 511, 300, -560], ![73, 62, 510, 300, -559]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 4 2 8 [37, 4, 88, 143, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [388, 197, 10, 446], [215, 40, 178, 415], [168, 219, 269, 53], [0, 1]]
 g := ![![[323, 75, 267, 157], [454, 12, 25], [178, 234, 214], [101, 400, 228, 197], [113, 88, 448], [345, 130, 163], [165, 253, 314, 1], []], ![[424, 77, 178, 9, 15, 90], [402, 239, 441], [431, 142, 425], [277, 126, 36, 386, 248, 172], [39, 201, 260], [329, 305, 272], [98, 246, 178, 102, 286, 46], [155, 260, 456, 246, 195, 40]], ![[269, 265, 366, 155, 183, 38], [219, 25, 48], [1, 76, 423], [134, 256, 442, 322, 110, 406], [275, 74, 450], [241, 328, 94], [146, 28, 86, 12, 298, 102], [5, 391, 115, 315, 52, 403]], ![[148, 171, 162, 137, 8, 78], [221, 163, 24], [353, 308, 224], [251, 192, 173, 394, 335, 53], [347, 41, 51], [111, 304, 230], [353, 193, 261, 96, 291, 122], [85, 196, 222, 171, 77, 352]]]
 h' := ![![[388, 197, 10, 446], [279, 52, 39, 385], [432, 100, 313, 5], [376, 218, 425, 118], [314, 196, 280, 45], [421, 352, 379, 327], [293, 33, 270, 376], [0, 0, 0, 1], [0, 1]], ![[215, 40, 178, 415], [208, 174, 446, 245], [456, 400, 212, 436], [306, 139, 371, 148], [277, 9, 446, 287], [231, 58, 451, 122], [396, 342, 142, 27], [280, 273, 367, 263], [388, 197, 10, 446]], ![[168, 219, 269, 53], [264, 298, 299, 59], [75, 145, 15, 123], [392, 269, 296, 364], [171, 281, 353, 124], [381, 18, 135, 286], [212, 378, 422, 195], [268, 71, 442, 439], [215, 40, 178, 415]], ![[0, 1], [125, 390, 130, 225], [361, 269, 374, 350], [444, 288, 279, 284], [196, 428, 292, 1], [349, 29, 406, 179], [228, 161, 80, 316], [311, 113, 105, 211], [168, 219, 269, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [89, 436, 6], []]
 b := ![[], [], [210, 0, 448, 196], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 4
  hpos := by decide
  P := [37, 4, 88, 143, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7411729191659, 8602256274647, 11948267226455, -77023764930, 8353144982469]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1062196553116, -913365728296, -7559314880740, -4478331607155, 8353144982469]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 43617904801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -43, 109, -79, 96]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![11, -43, 109, -79, 96]] 
 ![![457, 0, 0, 0, 0], ![323, 1, 0, 0, 0], ![115, 0, 1, 0, 0], ![310, 0, 0, 1, 0], ![236, 0, 0, 0, 1]] where
  M :=![![![11, -43, 109, -79, 96], ![-52, 198, -501, 363, -440], ![68, -254, 647, -468, 568], ![-292, 1115, -2821, 2046, -2480], ![80, -295, 755, -545, 663]]]
  hmulB := by decide  
  f := ![![![-1625, 129, -617, -133, 352]], ![![-1147, 93, -434, -94, 248]], ![![-407, 31, -154, -33, 88]], ![![-1102, 85, -421, -90, 240]], ![![-840, 67, -321, -69, 183]]]
  g := ![![![7, -43, 109, -79, 96], ![-33, 198, -501, 363, -440], ![41, -254, 647, -468, 568], ![-186, 1115, -2821, 2046, -2480], ![46, -295, 755, -545, 663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![1625, -129, 617, 133, -352]] ![![11, -43, 109, -79, 96]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![-457, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9307, -644, -2344, -427, 1327]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![-9307, -644, -2344, -427, 1327]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![0, 0, 0, 461, 0], ![372, 242, 437, 411, 1]] where
  M :=![![![-9307, -644, -2344, -427, 1327], ![512, -926, -613, -163, -762], ![3600, -662, 199, -8, -1180], ![412, -5953, -4473, -1136, -4366], ![-2426, -4483, -3933, -933, -2775]]]
  hmulB := by decide  
  f := ![![![-1, 18, -4, -3, 1]], ![![32, 18, 65, 3, -22]], ![![-8, -48, -15, 10, 0]], ![![-52, -41, -87, -22, 58]], ![![-38, -58, -61, -11, 41]]]
  g := ![![![-1091, -698, -1263, -1184, 1327], ![616, 398, 721, 679, -762], ![960, 618, 1119, 1052, -1180], ![3524, 2279, 4129, 3890, -4366], ![2234, 1447, 2622, 2472, -2775]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 4 2 8 [309, 23, 166, 183, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 182, 329, 357], [312, 245, 368, 333], [268, 33, 225, 232], [0, 1]]
 g := ![![[89, 290, 349, 387], [299, 134, 91], [434, 284, 21, 364], [138, 197, 124, 272], [173, 182, 385], [123, 316, 373], [389, 131, 278, 1], []], ![[202, 99, 358, 337, 234, 393], [104, 188, 405], [47, 97, 378, 334, 351, 84], [330, 48, 100, 67, 58, 21], [351, 322, 296], [0, 66, 81], [184, 125, 168, 397, 54, 62], [296, 71, 255, 54, 258, 437]], ![[379, 89, 90, 306, 111, 131], [4, 206, 397], [121, 389, 34, 410, 125, 313], [195, 51, 154, 290, 424, 241], [157, 424, 61], [428, 83, 439], [31, 106, 88, 455, 366, 286], [34, 270, 448, 67, 144, 398]], ![[233, 174, 159, 54, 266, 94], [381, 355, 348], [314, 247, 376, 6, 450, 138], [36, 231, 28, 88, 331, 205], [119, 318, 109], [88, 0, 120], [20, 29, 353, 273, 58, 270], [341, 261, 165, 46, 152, 61]]]
 h' := ![![[159, 182, 329, 357], [451, 296, 247, 159], [45, 340, 16, 78], [231, 257, 218, 156], [15, 309, 99, 415], [365, 237, 315, 107], [120, 362, 24, 401], [0, 0, 0, 1], [0, 1]], ![[312, 245, 368, 333], [8, 38, 200, 401], [111, 310, 94, 74], [95, 96, 122, 381], [250, 231, 218, 40], [425, 1, 254, 51], [173, 444, 18, 452], [34, 460, 72, 296], [159, 182, 329, 357]], ![[268, 33, 225, 232], [343, 359, 433, 306], [447, 32, 57, 77], [108, 225, 117, 429], [334, 90, 273, 97], [284, 113, 351, 423], [167, 344, 350, 431], [284, 330, 325, 367], [312, 245, 368, 333]], ![[0, 1], [307, 229, 42, 56], [375, 240, 294, 232], [147, 344, 4, 417], [100, 292, 332, 370], [144, 110, 2, 341], [58, 233, 69, 99], [438, 132, 64, 258], [268, 33, 225, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [348, 425], []]
 b := ![[], [], [304, 316, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 4
  hpos := by decide
  P := [309, 23, 166, 183, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284855364683, 334582494189, 453062080480, 2285803230, 315726443979]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-254154841205, -165013485789, -298306711363, -281477836599, 315726443979]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 45165175441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -18, 4, 3, -1]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![1, -18, 4, 3, -1]] 
 ![![461, 0, 0, 0, 0], ![398, 1, 0, 0, 0], ![407, 0, 1, 0, 0], ![169, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![1, -18, 4, 3, -1], ![-32, -18, -65, -3, 22], ![8, 48, 15, -10, 0], ![52, 41, 87, 22, -58], ![22, -37, 51, 9, -15]]]
  hmulB := by decide  
  f := ![![![9307, 644, 2344, 427, -1327]], ![![8034, 558, 2025, 369, -1144]], ![![8209, 570, 2069, 377, -1169]], ![![3411, 249, 869, 159, -477]], ![![833, 67, 217, 40, -112]]]
  g := ![![![11, -18, 4, 3, -1], ![72, -18, -65, -3, 22], ![-51, 48, 15, -10, 0], ![-115, 41, 87, 22, -58], ![-15, -37, 51, 9, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N1 : Nat.card (O ⧸ I461N1) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N1)

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := prime_ideal_of_norm_prime hp461.out _ NI461N1
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![-9307, -644, -2344, -427, 1327]] ![![1, -18, 4, 3, -1]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![-461, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267, -685, -1321, -58, 499]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![-267, -685, -1321, -58, 499]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![417, 71, 362, 127, 1]] where
  M :=![![![-267, -685, -1321, -58, 499], ![-488, 3189, -1152, -706, 534], ![1764, 780, 3853, 404, -1528], ![588, -5296, 2056, 1215, -818], ![-1710, -3742, -3050, 232, 1245]]]
  hmulB := by decide  
  f := ![![![25, -89, 227, -164, 199]], ![![-108, 411, -1040, 754, -914]], ![![140, -528, 1343, -972, 1180]], ![![-608, 2316, -5860, 4249, -5150]], ![![-51, 204, -509, 371, -448]]]
  g := ![![![-450, -78, -393, -137, 499], ![-482, -75, -420, -148, 534], ![1380, 236, 1203, 420, -1528], ![738, 114, 644, 227, -818], ![-1125, -199, -980, -341, 1245]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 4 2 8 [283, 211, 272, 381, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [324, 33, 6, 330], [107, 161, 288, 363], [114, 268, 169, 233], [0, 1]]
 g := ![![[187, 365, 253, 49], [109, 298, 252, 64], [326, 60, 243, 400], [415, 152, 204, 8], [13, 369, 211], [302, 352, 380], [27, 433, 82, 1], []], ![[238, 122, 202, 5, 424, 319], [76, 176, 301, 441, 354, 245], [129, 169, 340, 129, 210, 85], [172, 459, 332, 247, 320, 327], [145, 299, 103], [149, 389, 123], [396, 364, 130, 315, 19, 300], [322, 214, 353, 381, 445, 329]], ![[168, 295, 185, 177, 9, 3], [276, 259, 352, 359, 15, 99], [388, 163, 293, 200, 315, 307], [60, 385, 13, 450, 142, 461], [301, 324, 172], [236, 259, 268], [23, 57, 103, 306, 307, 224], [79, 124, 181, 349, 35, 80]], ![[103, 457, 57, 63, 110, 51], [57, 364, 84, 214, 380, 235], [236, 330, 66, 361, 57, 295], [413, 305, 360, 222, 445, 151], [188, 365, 62], [165, 120, 73], [131, 57, 371, 461, 345, 433], [357, 246, 172, 29, 260, 177]]]
 h' := ![![[324, 33, 6, 330], [174, 371, 302, 456], [342, 462, 35, 8], [157, 185, 131, 443], [285, 368, 126, 57], [307, 56, 148, 423], [230, 15, 319, 197], [0, 0, 0, 1], [0, 1]], ![[107, 161, 288, 363], [295, 418, 196, 167], [112, 185, 455, 201], [112, 260, 235, 98], [234, 180, 66, 111], [353, 452, 414, 154], [127, 322, 359, 405], [329, 336, 407, 112], [324, 33, 6, 330]], ![[114, 268, 169, 233], [332, 51, 191, 421], [124, 324, 282, 107], [405, 54, 191, 204], [346, 17, 44, 437], [356, 205, 316, 239], [460, 131, 455, 113], [275, 353, 216, 387], [107, 161, 288, 363]], ![[0, 1], [313, 86, 237, 345], [228, 418, 154, 147], [341, 427, 369, 181], [49, 361, 227, 321], [406, 213, 48, 110], [324, 458, 256, 211], [310, 237, 303, 426], [114, 268, 169, 233]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 233, 422], []]
 b := ![[], [], [169, 79, 142, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 4
  hpos := by decide
  P := [283, 211, 272, 381, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![368191329320, 463201786028, 535477845518, 46575233110, 362394501832]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-325594634848, -54571939188, -282184301982, -99303512958, 362394501832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 45954068161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 89, -227, 164, -199]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![-25, 89, -227, 164, -199]] 
 ![![463, 0, 0, 0, 0], ![371, 1, 0, 0, 0], ![454, 0, 1, 0, 0], ![460, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-25, 89, -227, 164, -199], ![108, -411, 1040, -754, 914], ![-140, 528, -1343, 972, -1180], ![608, -2316, 5860, -4249, 5150], ![-166, 612, -1568, 1132, -1377]]]
  hmulB := by decide  
  f := ![![![267, 685, 1321, 58, -499]], ![![215, 542, 1061, 48, -401]], ![![258, 670, 1287, 56, -486]], ![![264, 692, 1308, 55, -494]], ![![6, 14, 18, 0, -7]]]
  g := ![![![-10, 89, -227, 164, -199], ![51, -411, 1040, -754, 914], ![-62, 528, -1343, 972, -1180], ![288, -2316, 5860, -4249, 5150], ![-66, 612, -1568, 1132, -1377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N1 : Nat.card (O ⧸ I463N1) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N1)

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := prime_ideal_of_norm_prime hp463.out _ NI463N1
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![-267, -685, -1321, -58, 499]] ![![-25, 89, -227, 164, -199]]
  ![![463, 0, 0, 0, 0]] where
 M := ![![![-463, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0)


lemma PB853I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB853I9 : PrimesBelowBoundCertificateInterval O 419 463 853 where
  m := 9
  g := ![3, 2, 4, 1, 3, 4, 2, 2, 2]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB853I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1, I433N2, I433N3]
    · exact ![I439N0]
    · exact ![I443N0, I443N1, I443N2]
    · exact ![I449N0, I449N1, I449N2, I449N3]
    · exact ![I457N0, I457N1]
    · exact ![I461N0, I461N1]
    · exact ![I463N0, I463N1]
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
    · exact ![177241, 177241, 421]
    · exact ![80062991, 185761]
    · exact ![187489, 433, 433, 433]
    · exact ![16305067506199]
    · exact ![86938307, 443, 443]
    · exact ![201601, 449, 449, 449]
    · exact ![43617904801, 457]
    · exact ![45165175441, 461]
    · exact ![45954068161, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
      exact NI433N2
      exact NI433N3
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
      exact NI443N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
  β := ![I421N2, I433N1, I433N2, I433N3, I443N1, I443N2, I449N1, I449N2, I449N3, I457N1, I461N1, I463N1]
  Il := ![[I421N2], [], [I433N1, I433N2, I433N3], [], [I443N1, I443N2], [I449N1, I449N2, I449N3], [I457N1], [I461N1], [I463N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
