
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-821, -208, 212, -114, 106]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![-821, -208, 212, -114, 106]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![394, 129, 348, 1, 0], ![134, 105, 273, 0, 1]] where
  M :=![![![-821, -208, 212, -114, 106], ![2120, 663, -416, 318, -228], ![-2280, -516, 663, -302, 318], ![2120, 768, -308, 345, -188], ![-1880, -222, 768, -214, 345]]]
  hmulB := by decide  
  f := ![![![-81, -12, 4, -6, 10]], ![![200, 43, -24, -2, -12]], ![![-120, 16, 43, -18, -2]], ![![-114, 15, 32, -21, 4]], ![![-54, 17, 23, -14, -1]]]
  g := ![![![71, 8, 26, -114, 106], ![-220, -39, -116, 318, -228], ![176, 12, 45, -302, 318], ![-258, -57, -164, 345, -188], ![86, -21, -45, -214, 345]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 3 2 8 [273, 253, 262, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [319, 404, 161], [261, 16, 260], [0, 1]]
 g := ![![[5, 85, 372], [86, 366], [34, 359, 5], [245, 247], [353, 247], [173, 204, 64], [349, 21], [1]], ![[411, 318, 70, 326], [377, 199], [284, 416, 401, 95], [74, 44], [54, 38], [243, 102, 90, 203], [410, 149], [175, 46, 76, 329]], ![[390, 318, 154, 304], [295, 142], [134, 166, 118, 95], [54, 113], [365, 234], [358, 162, 187, 249], [35, 234], [331, 316, 46, 92]]]
 h' := ![![[319, 404, 161], [77, 76, 218], [401, 240, 114], [206, 121, 200], [75, 30, 388], [344, 163, 33], [302, 324, 8], [148, 168, 159], [0, 1]], ![[261, 16, 260], [149, 242, 147], [205, 376, 48], [318, 258, 368], [311, 150, 92], [209, 358, 248], [186, 226, 88], [352, 279, 122], [319, 404, 161]], ![[0, 1], [242, 103, 56], [307, 226, 259], [218, 42, 274], [406, 241, 362], [287, 321, 140], [60, 292, 325], [61, 395, 140], [261, 16, 260]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161, 22], []]
 b := ![[], [175, 60, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 3
  hpos := by decide
  P := [273, 253, 262, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19787, 27296, 57594, 95020, 59034]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107763, -43774, -116688, 95020, 59034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 74618461 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3329, -936, 778, -481, 400]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![-3329, -936, 778, -481, 400]] 
 ![![421, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![303, 0, 0, 0, 1]] where
  M :=![![![-3329, -936, 778, -481, 400], ![8000, 2249, -1872, 1156, -962], ![-9620, -2708, 2249, -1391, 1156], ![7560, 2126, -1772, 1093, -910], ![-9100, -2566, 2126, -1317, 1093]]]
  hmulB := by decide  
  f := ![![![611, 122, -398, -157, 174]], ![![46, 13, -24, -12, 10]], ![![113, 24, -73, -30, 32]], ![![221, 32, -162, -56, 72]], ![![453, 82, -304, -114, 133]]]
  g := ![![![-196, -936, 778, -481, 400], ![472, 2249, -1872, 1156, -962], ![-566, -2708, 2249, -1391, 1156], ![447, 2126, -1772, 1093, -910], ![-534, -2566, 2126, -1317, 1093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N1 : Nat.card (O ⧸ I421N1) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N1)

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := prime_ideal_of_norm_prime hp421.out _ NI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 2, -2, 3, -2]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![9, 2, -2, 3, -2]] 
 ![![421, 0, 0, 0, 0], ![120, 1, 0, 0, 0], ![378, 0, 1, 0, 0], ![415, 0, 0, 1, 0], ![360, 0, 0, 0, 1]] where
  M :=![![![9, 2, -2, 3, -2], ![-40, -17, 4, -2, 6], ![60, 18, -17, 1, -2], ![0, 18, 16, -15, -2], ![-20, -4, 18, 17, -15]]]
  hmulB := by decide  
  f := ![![![-4411, -540, 430, -369, 364]], ![![-1240, -153, 120, -104, 102]], ![![-3978, -488, 387, -333, 328]], ![![-4345, -534, 422, -364, 358]], ![![-3780, -466, 366, -317, 311]]]
  g := ![![![0, 2, -2, 3, -2], ![-2, -17, 4, -2, 6], ![11, 18, -17, 1, -2], ![-3, 18, 16, -15, -2], ![-19, -4, 18, 17, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![-821, -208, 212, -114, 106]] ![![-3329, -936, 778, -481, 400]]
  ![![-2796771, -787792, 654790, -404643, 336366]] where
 M := ![![![-2796771, -787792, 654790, -404643, 336366]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![-2796771, -787792, 654790, -404643, 336366]] ![![9, 2, -2, 3, -2]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![38900821, 10956104, -9108756, 5627928, -4678994]]]
 hmul := by decide  
 g := ![![![![92401, 26024, -21636, 13368, -11114]]]]
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

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, 14, -4, 0, 6]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![-121, 14, -4, 0, 6]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![415, 136, 1, 0, 0], ![21, 245, 0, 1, 0], ![41, 93, 0, 0, 1]] where
  M :=![![![-121, 14, -4, 0, 6], ![120, -53, 28, -14, 0], ![0, 74, -53, 28, -14], ![-200, -84, 60, -39, 28], ![280, 98, -84, 46, -39]]]
  hmulB := by decide  
  f := ![![![-71, -46, -4, 16, 2]], ![![40, -51, -92, -10, 32]], ![![-55, -60, -33, 12, 12]], ![![19, -31, -52, -5, 18]], ![![-1, -17, -20, 0, 7]]]
  g := ![![![3, 0, -4, 0, 6], ![-26, -1, 28, -14, 0], ![51, 4, -53, 28, -14], ![-59, -3, 60, -39, 28], ![83, 9, -84, 46, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 2 2 8 [405, 413, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 430], [0, 1]]
 g := ![![[67, 116], [394, 209], [356, 300], [56, 366], [20], [429, 212], [96], [18, 1]], ![[0, 315], [277, 222], [153, 131], [179, 65], [20], [366, 219], [96], [36, 430]]]
 h' := ![![[18, 430], [331, 245], [205, 263], [163, 360], [207, 80], [379, 69], [417, 44], [37, 350], [0, 1]], ![[0, 1], [0, 186], [198, 168], [178, 71], [354, 351], [328, 362], [347, 387], [303, 81], [18, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [425, 288]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 2
  hpos := by decide
  P := [405, 413, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3507, 10668, 57694, -32578, 9818]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54907, -1780, 57694, -32578, 9818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 185761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 18, 8, 5, 2]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![21, 18, 8, 5, 2]] 
 ![![431, 0, 0, 0, 0], ![287, 1, 0, 0, 0], ![407, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![21, 18, 8, 5, 2], ![40, 53, 36, 14, 10], ![100, 98, 53, 31, 14], ![120, 134, 80, 39, 26], ![260, 256, 134, 67, 39]]]
  hmulB := by decide  
  f := ![![![-47589, -4840, 5440, -3749, 4228]], ![![-31493, -3203, 3600, -2481, 2798]], ![![-45113, -4588, 5157, -3554, 4008]], ![![-7452, -758, 852, -587, 662]], ![![-17165, -1746, 1962, -1352, 1525]]]
  g := ![![![-21, 18, 8, 5, 2], ![-75, 53, 36, 14, 10], ![-125, 98, 53, 31, 14], ![-180, 134, 80, 39, 26], ![-321, 256, 134, 67, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1

def I431N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-219, -60, 50, -31, 26]] i)))

def SI431N2: IdealEqSpanCertificate' Table ![![-219, -60, 50, -31, 26]] 
 ![![431, 0, 0, 0, 0], ![310, 1, 0, 0, 0], ![222, 0, 1, 0, 0], ![346, 0, 0, 1, 0], ![245, 0, 0, 0, 1]] where
  M :=![![![-219, -60, 50, -31, 26], ![520, 143, -120, 74, -62], ![-620, -172, 143, -89, 74], ![480, 134, -112, 69, -58], ![-580, -164, 134, -83, 69]]]
  hmulB := by decide  
  f := ![![![-69, 38, 22, -53, -8]], ![![-50, 27, 16, -38, -6]], ![![-38, 18, 11, -27, -4]], ![![-54, 30, 16, -43, -6]], ![![-35, 24, 12, -32, -5]]]
  g := ![![![27, -60, 50, -31, 26], ![-64, 143, -120, 74, -62], ![78, -172, 143, -89, 74], ![-60, 134, -112, 69, -58], ![75, -164, 134, -83, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N2 : Nat.card (O ⧸ I431N2) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N2)

lemma isPrimeI431N2 : Ideal.IsPrime I431N2 := prime_ideal_of_norm_prime hp431.out _ NI431N2

def I431N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249, -70, 58, -36, 30]] i)))

def SI431N3: IdealEqSpanCertificate' Table ![![-249, -70, 58, -36, 30]] 
 ![![431, 0, 0, 0, 0], ![424, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![241, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![-249, -70, 58, -36, 30], ![600, 169, -140, 86, -72], ![-720, -202, 169, -104, 86], ![560, 156, -132, 83, -68], ![-680, -194, 156, -98, 83]]]
  hmulB := by decide  
  f := ![![![-1159, -186, 70, -116, 90]], ![![-1136, -183, 68, -114, 88]], ![![-519, -84, 31, -52, 40]], ![![-649, -106, 38, -65, 50]], ![![-533, -88, 30, -54, 41]]]
  g := ![![![49, -70, 58, -36, 30], ![-118, 169, -140, 86, -72], ![141, -202, 169, -104, 86], ![-109, 156, -132, 83, -68], ![137, -194, 156, -98, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N3 : Nat.card (O ⧸ I431N3) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N3)

lemma isPrimeI431N3 : Ideal.IsPrime I431N3 := prime_ideal_of_norm_prime hp431.out _ NI431N3
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![-121, 14, -4, 0, 6]] ![![21, 18, 8, 5, 2]]
  ![![-821, -292, 128, -131, 76]] where
 M := ![![![-821, -292, 128, -131, 76]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N1 : IdealMulLeCertificate' Table 
  ![![-821, -292, 128, -131, 76]] ![![-219, -60, 50, -31, 26]]
  ![![-158361, -44530, 37150, -22896, 19072]] where
 M := ![![![-158361, -44530, 37150, -22896, 19072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI431N2 : IdealMulLeCertificate' Table 
  ![![-158361, -44530, 37150, -22896, 19072]] ![![-249, -70, 58, -36, 30]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![-39824831, -11216344, 9325116, -5761608, 4790134]]]
 hmul := by decide  
 g := ![![![![-92401, -26024, 21636, -13368, 11114]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1, I431N2, I431N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
    exact isPrimeI431N2
    exact isPrimeI431N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0 ⊙ MulI431N1 ⊙ MulI431N2)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -21, -66, -26, 42]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![21, -21, -66, -26, 42]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![0, 0, 0, 433, 0], ![217, 216, 184, 20, 1]] where
  M :=![![![21, -21, -66, -26, 42], ![840, 459, -42, -174, -52], ![-520, 87, 459, -16, -174], ![-2160, -1304, 108, 633, 10], ![100, -966, -1304, 103, 633]]]
  hmulB := by decide  
  f := ![![![-67, -9, 8, -6, 6]], ![![120, 13, -18, 10, -12]], ![![-120, -21, 13, -12, 10]], ![![40, 0, -12, 3, -6]], ![![-23, -7, 0, -3, 1]]]
  g := ![![![-21, -21, -18, -2, 42], ![28, 27, 22, 2, -52], ![86, 87, 75, 8, -174], ![-10, -8, -4, 1, 10], ![-317, -318, -272, -29, 633]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 4 2 8 [112, 174, 280, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 92, 248, 333], [146, 244, 277, 99], [76, 96, 341, 1], [0, 1]]
 g := ![![[61, 17, 396, 352], [400, 66, 400], [79, 192, 324], [393, 50, 159], [117, 208, 73, 333], [363, 271, 207, 70], [388, 318, 1], []], ![[129, 187, 201, 217, 387, 27], [191, 406, 44], [319, 236, 363], [30, 89, 415], [168, 187, 367, 192, 56, 335], [187, 142, 188, 166, 286, 310], [12, 196, 11], [104, 124, 362, 102, 157, 230]], ![[70, 320, 256, 359, 246, 384], [10, 79, 81], [372, 183, 96], [214, 86, 355], [339, 49, 48, 22, 128, 106], [205, 291, 356, 187, 405, 429], [286, 320, 382], [32, 173, 332, 70, 49, 379]], ![[225, 22, 379, 367, 380, 16], [155, 206, 430], [76, 61, 416], [112, 40, 106], [62, 157, 347, 332, 98, 427], [90, 212, 72, 241, 97, 25], [348, 99, 285], [150, 293, 27, 219, 42, 1]]]
 h' := ![![[96, 92, 248, 333], [273, 185, 146, 312], [333, 413, 264, 20], [156, 149, 403, 415], [319, 30, 237, 67], [46, 102, 62, 58], [277, 359, 23, 396], [0, 0, 0, 1], [0, 1]], ![[146, 244, 277, 99], [24, 309, 355, 184], [64, 323, 338, 386], [252, 317, 291, 305], [183, 389, 241, 207], [355, 172, 4, 29], [8, 405, 81, 77], [160, 232, 114, 240], [96, 92, 248, 333]], ![[76, 96, 341, 1], [58, 393, 177, 374], [237, 384, 296, 424], [58, 305, 29, 410], [53, 155, 414, 211], [155, 110, 31, 291], [303, 116, 408, 388], [45, 327, 170, 41], [146, 244, 277, 99]], ![[0, 1], [181, 412, 188, 429], [124, 179, 401, 36], [323, 95, 143, 169], [297, 292, 407, 381], [47, 49, 336, 55], [428, 419, 354, 5], [1, 307, 149, 151], [76, 96, 341, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 65, 180], []]
 b := ![[], [], [205, 116, 185, 195], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 4
  hpos := by decide
  P := [112, 174, 280, 115, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-856898, -1790464, -1615242, -340844, 302252]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-153454, -154912, -132170, -14748, 302252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 35152125121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -9, 8, -6, 6]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![-67, -9, 8, -6, 6]] 
 ![![433, 0, 0, 0, 0], ![393, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![387, 0, 0, 0, 1]] where
  M :=![![![-67, -9, 8, -6, 6], ![120, 13, -18, 10, -12], ![-120, -21, 13, -12, 10], ![40, 0, -12, 3, -6], ![-60, -22, 0, -9, 3]]]
  hmulB := by decide  
  f := ![![![21, -21, -66, -26, 42]], ![![21, -18, -60, -24, 38]], ![![2, -3, -9, -4, 6]], ![![-3, -5, -6, -1, 4]], ![![19, -21, -62, -23, 39]]]
  g := ![![![2, -9, 8, -6, 6], ![1, 13, -18, 10, -12], ![9, -21, 13, -12, 10], ![7, 0, -12, 3, -6], ![18, -22, 0, -9, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![21, -21, -66, -26, 42]] ![![-67, -9, 8, -6, 6]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 527, 318, 145, 96]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![409, 527, 318, 145, 96]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![265, 242, 28, 1, 0], ![43, 175, 336, 0, 1]] where
  M :=![![![409, 527, 318, 145, 96], ![1920, 1879, 1054, 540, 290], ![2900, 3227, 1879, 909, 540], ![4440, 4690, 2700, 1339, 764], ![7640, 8154, 4690, 2318, 1339]]]
  hmulB := by decide  
  f := ![![![71, 23, -20, 7, -6]], ![![-120, -21, 46, -34, 14]], ![![140, 47, -21, 39, -34]], ![![-15, 5, 12, -12, 2]], ![![67, 30, 0, 17, -21]]]
  g := ![![![-96, -117, -82, 145, 96], ![-350, -409, -254, 540, 290], ![-595, -709, -467, 909, 540], ![-873, -1032, -664, 1339, 764], ![-1513, -1793, -1162, 2318, 1339]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 3 2 8 [316, 366, 273, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [322, 176, 250], [283, 262, 189], [0, 1]]
 g := ![![[74, 396, 203], [261, 423, 360], [268, 342, 130], [326, 61], [153, 240, 364], [127, 77, 25], [7, 338], [1]], ![[298, 201, 306, 267], [34, 55, 79, 324], [47, 127, 196, 276], [330, 355], [3, 343, 93, 146], [436, 377, 435, 345], [403, 65], [136, 225, 85, 112]], ![[344, 277, 154, 263], [406, 253, 434, 374], [236, 167, 387, 389], [163, 392], [403, 84, 429, 403], [71, 85, 436, 378], [161, 81], [158, 181, 307, 327]]]
 h' := ![![[322, 176, 250], [56, 168, 123], [39, 171, 46], [1, 323, 224], [381, 426, 73], [256, 219, 41], [186, 339, 5], [123, 73, 166], [0, 1]], ![[283, 262, 189], [221, 54, 35], [422, 117, 366], [384, 133, 275], [228, 154, 72], [117, 171, 81], [207, 13, 16], [344, 384, 282], [322, 176, 250]], ![[0, 1], [389, 217, 281], [260, 151, 27], [100, 422, 379], [344, 298, 294], [401, 49, 317], [33, 87, 418], [174, 421, 430], [283, 262, 189]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [364, 162], []]
 b := ![[], [364, 102, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 3
  hpos := by decide
  P := [316, 366, 273, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3908476, 5239383, 3936592, 1812441, 721898]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1155877, -1274951, -659156, 1812441, 721898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 84604519 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -23, 20, -7, 6]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![-71, -23, 20, -7, 6]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![207, 411, 1, 0, 0], ![89, 198, 0, 1, 0], ![280, 101, 0, 0, 1]] where
  M :=![![![-71, -23, 20, -7, 6], ![120, 21, -46, 34, -14], ![-140, -47, 21, -39, 34], ![280, 134, -24, -13, -32], ![-320, -64, 134, -8, -13]]]
  hmulB := by decide  
  f := ![![![-409, -527, -318, -145, -96]], ![![-1920, -1879, -1054, -540, -290]], ![![-1997, -2015, -1141, -576, -318]], ![![-959, -965, -546, -276, -152]], ![![-720, -787, -456, -222, -131]]]
  g := ![![![-12, -17, 20, -7, 6], ![24, 31, -46, 34, -14], ![-24, -10, 21, -39, 34], ![35, 36, -24, -13, -32], ![-54, -119, 134, -8, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P1 : CertificateIrreducibleZModOfList' 439 2 2 8 [134, 211, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [228, 438], [0, 1]]
 g := ![![[149, 29], [246, 379], [247, 71], [433], [1, 357], [325, 350], [109], [228, 1]], ![[176, 410], [175, 60], [192, 368], [433], [182, 82], [227, 89], [109], [17, 438]]]
 h' := ![![[228, 438], [400, 111], [266, 348], [322, 70], [305, 260], [350, 75], [396, 235], [178, 48], [0, 1]], ![[0, 1], [246, 328], [151, 91], [39, 369], [320, 179], [329, 364], [418, 204], [147, 391], [228, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [315]]
 b := ![[], [44, 377]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N1 : CertifiedPrimeIdeal' SI439N1 439 where
  n := 2
  hpos := by decide
  P := [134, 211, 1]
  hirr := P439P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4, 493, -962, 746, -868]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![856, 765, -962, 746, -868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N1 B_one_repr
lemma NI439N1 : Nat.card (O ⧸ I439N1) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N1
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![409, 527, 318, 145, 96]] ![![-71, -23, 20, -7, 6]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![-439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6783, 1540, -1332, 845, -748]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![6783, 1540, -1332, 845, -748]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![6, 320, 83, 1, 0], ![388, 286, 76, 0, 1]] where
  M :=![![![6783, 1540, -1332, 845, -748], ![-14960, -3525, 3080, -1916, 1690], ![16900, 4200, -3525, 2235, -1916], ![-11680, -3046, 2660, -1609, 1390], ![13900, 3830, -3046, 1965, -1609]]]
  hmulB := by decide  
  f := ![![![-179, -130, -20, 55, 18]], ![![360, 17, -260, -58, 110]], ![![1100, 710, 17, -315, -58]], ![![462, 144, -183, -100, 68]], ![![256, 14, -182, -41, 77]]]
  g := ![![![659, -124, -33, 845, -748], ![-1488, 285, 76, -1916, 1690], ![1686, -368, -98, 2235, -1916], ![-1222, 258, 69, -1609, 1390], ![1414, -372, -99, 1965, -1609]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [132, 432, 268, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 346, 412], [129, 96, 31], [0, 1]]
 g := ![![[248, 6, 400], [77, 366, 315], [107, 410], [313, 373, 333], [383, 38, 160], [314, 281, 253], [267, 58], [1]], ![[409, 299, 336, 95], [256, 174, 264, 109], [53, 55], [64, 219, 317, 164], [343, 280, 59, 105], [179, 199, 72, 428], [206, 194], [302, 161, 124, 333]], ![[350, 210, 204, 19], [155, 415, 41, 329], [101, 62], [335, 177, 390, 368], [41, 402, 167, 283], [244, 142, 381, 69], [176, 130], [108, 53, 94, 110]]]
 h' := ![![[46, 346, 412], [25, 0, 20], [8, 371, 168], [326, 94, 36], [389, 64, 136], [194, 284, 74], [343, 351, 398], [311, 11, 175], [0, 1]], ![[129, 96, 31], [108, 378, 148], [317, 236, 197], [15, 68, 99], [442, 438, 440], [408, 342, 72], [22, 321, 304], [325, 247, 68], [46, 346, 412]], ![[0, 1], [213, 65, 275], [96, 279, 78], [32, 281, 308], [266, 384, 310], [225, 260, 297], [13, 214, 184], [274, 185, 200], [129, 96, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [255, 374], []]
 b := ![[], [318, 349, 255], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [132, 432, 268, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-932668, 730280, 1366496, -976800, 13528]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-724, 698504, 183776, -976800, 13528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, -17, 20, -14, 16]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![-183, -17, 20, -14, 16]] 
 ![![443, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![246, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-183, -17, 20, -14, 16], ![320, 29, -34, 24, -28], ![-280, -25, 29, -20, 24], ![80, 4, -8, 5, -6], ![-60, 0, 4, -5, 5]]]
  hmulB := by decide  
  f := ![![![-141, -171, -106, -22, -24]], ![![-24, -29, -18, -4, -4]], ![![-22, -27, -17, -4, -4]], ![![-82, -98, -60, -13, -14]], ![![-8, -8, -4, -1, -1]]]
  g := ![![![7, -17, 20, -14, 16], ![-12, 29, -34, 24, -28], ![10, -25, 29, -20, 24], ![-2, 4, -8, 5, -6], ![2, 0, 4, -5, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N1 : Nat.card (O ⧸ I443N1) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N1)

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := prime_ideal_of_norm_prime hp443.out _ NI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -39, -14, -13, -2]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![-67, -39, -14, -13, -2]] 
 ![![443, 0, 0, 0, 0], ![205, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![421, 0, 0, 0, 1]] where
  M :=![![![-67, -39, -14, -13, -2], ![-40, -105, -78, -26, -26], ![-260, -215, -105, -65, -26], ![-240, -286, -176, -79, -52], ![-520, -520, -286, -150, -79]]]
  hmulB := by decide  
  f := ![![![911, 433, -216, -259, 76]], ![![425, 204, -98, -121, 34]], ![![50, 25, -11, -15, 4]], ![![285, 129, -76, -80, 28]], ![![897, 421, -218, -253, 77]]]
  g := ![![![25, -39, -14, -13, -2], ![87, -105, -78, -26, -26], ![152, -215, -105, -65, -26], ![219, -286, -176, -79, -52], ![383, -520, -286, -150, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![6783, 1540, -1332, 845, -748]] ![![-183, -17, 20, -14, 16]]
  ![![-263049, -33971, 34920, -23397, 24630]] where
 M := ![![![-263049, -33971, 34920, -23397, 24630]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![-263049, -33971, 34920, -23397, 24630]] ![![-67, -39, -14, -13, -2]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![2711603, 202008, -260484, 186946, -227702]]]
 hmul := by decide  
 g := ![![![![6121, 456, -588, 422, -514]]]]
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

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![201, 55, -40, 25, -22]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![201, 55, -40, 25, -22]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![193, 85, 122, 1, 0], ![251, 339, 18, 0, 1]] where
  M :=![![![201, 55, -40, 25, -22], ![-440, -103, 110, -58, 50], ![500, 135, -103, 85, -58], ![-360, -98, 80, -45, 60], ![600, 220, -98, 50, -45]]]
  hmulB := by decide  
  f := ![![![49, 5, -6, 5, -4]], ![![-80, -5, 10, -8, 10]], ![![100, 25, -5, 5, -8]], ![![33, 8, -2, 2, -2]], ![![-29, 0, 4, -3, 5]]]
  g := ![![![2, 12, -6, 25, -22], ![-4, -27, 14, -58, 50], ![-3, 28, -21, 85, -58], ![-15, -37, 10, -45, 60], ![5, 25, -12, 50, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 3 2 8 [25, 427, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [448, 123, 367], [322, 325, 82], [0, 1]]
 g := ![![[18, 331, 427], [344, 438], [195, 88], [343, 255], [397, 70], [437, 36], [209, 332, 220], [1]], ![[162, 404, 229, 427], [214, 194], [290, 4], [322, 413], [71, 112], [438, 254], [158, 262, 268, 213], [80, 189, 368, 4]], ![[275, 13, 285, 256], [361, 359], [420, 388], [270, 9], [40, 400], [448, 181], [313, 65, 299, 242], [253, 407, 114, 445]]]
 h' := ![![[448, 123, 367], [194, 11, 234], [266, 333, 82], [287, 320, 375], [55, 29, 50], [378, 147, 238], [163, 66, 443], [424, 22, 321], [0, 1]], ![[322, 325, 82], [93, 396, 165], [385, 87, 242], [30, 24, 447], [214, 208, 402], [174, 368, 191], [272, 26, 271], [244, 98, 149], [448, 123, 367]], ![[0, 1], [48, 42, 50], [274, 29, 125], [214, 105, 76], [404, 212, 446], [147, 383, 20], [349, 357, 184], [365, 329, 428], [322, 325, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 370], []]
 b := ![[], [0, 323, 344], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 3
  hpos := by decide
  P := [25, 427, 128, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43265, 14895, -14422, -5493, 17172]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7142, -11892, 772, -5493, 17172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 90518849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-461, -76, 72, -47, 46]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![-461, -76, 72, -47, 46]] 
 ![![449, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![438, 0, 1, 0, 0], ![185, 0, 0, 1, 0], ![394, 0, 0, 0, 1]] where
  M :=![![![-461, -76, 72, -47, 46], ![920, 163, -152, 98, -94], ![-940, -180, 163, -105, 98], ![520, 118, -104, 65, -58], ![-580, -140, 118, -75, 65]]]
  hmulB := by decide  
  f := ![![![771, 434, -72, -227, -12]], ![![63, 37, -4, -19, -2]], ![![742, 418, -69, -219, -12]], ![![315, 172, -36, -92, -2]], ![![706, 394, -70, -207, -9]]]
  g := ![![![-86, -76, 72, -47, 46], ![179, 163, -152, 98, -94], ![-189, -180, 163, -105, 98], ![117, 118, -104, 65, -58], ![-131, -140, 118, -75, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N1 : Nat.card (O ⧸ I449N1) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N1)

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := prime_ideal_of_norm_prime hp449.out _ NI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 1, 10, 2, -4]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![-11, 1, 10, 2, -4]] 
 ![![449, 0, 0, 0, 0], ![168, 1, 0, 0, 0], ![256, 0, 1, 0, 0], ![413, 0, 0, 1, 0], ![330, 0, 0, 0, 1]] where
  M :=![![![-11, 1, 10, 2, -4], ![-80, -49, 2, 24, 4], ![40, -15, -49, 0, 24], ![280, 164, -16, -73, -2], ![-20, 120, 164, -15, -73]]]
  hmulB := by decide  
  f := ![![![-21299, -6919, 5604, -3418, 2724]], ![![-7848, -2551, 2066, -1260, 1004]], ![![-12296, -3991, 3233, -1972, 1572]], ![![-19463, -6327, 5124, -3125, 2490]], ![![-15810, -5130, 4156, -2535, 2021]]]
  g := ![![![-5, 1, 10, 2, -4], ![-8, -49, 2, 24, 4], ![16, -15, -49, 0, 24], ![17, 164, -16, -73, -2], ![-71, 120, 164, -15, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![201, 55, -40, 25, -22]] ![![-461, -76, 72, -47, 46]]
  ![![21299, 6919, -5604, 3418, -2724]] where
 M := ![![![21299, 6919, -5604, 3418, -2724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![21299, 6919, -5604, 3418, -2724]] ![![-11, 1, 10, 2, -4]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![-449, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1, I449N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
    exact isPrimeI449N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0 ⊙ MulI449N1)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 153, 110, 46, 32]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![107, 153, 110, 46, 32]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![0, 0, 457, 0, 0], ![423, 49, 49, 1, 0], ![295, 120, 390, 0, 1]] where
  M :=![![![107, 153, 110, 46, 32], ![640, 601, 306, 188, 92], ![920, 1025, 601, 260, 188], ![1560, 1588, 872, 413, 214], ![2140, 2500, 1588, 765, 413]]]
  hmulB := by decide  
  f := ![![![-3509, -359, 404, -278, 312]], ![![6240, 639, -718, 496, -556]], ![![-5560, -575, 639, -440, 496]], ![![-3171, -325, 365, -251, 282]], ![![-5375, -555, 618, -425, 479]]]
  g := ![![![-63, -13, -32, 46, 32], ![-232, -43, -98, 188, 92], ![-360, -75, -187, 260, 188], ![-517, -97, -225, 413, 214], ![-970, -185, -431, 765, 413]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 3 2 8 [194, 35, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 448, 38], [251, 8, 419], [0, 1]]
 g := ![![[282, 328, 321], [262, 233], [121, 408], [284, 339, 262], [279, 84], [200, 116], [222, 288, 449], [1]], ![[134, 127, 395, 171], [366, 197], [99, 171], [246, 5, 33, 12], [456, 151], [29, 359], [40, 119, 38, 330], [263, 277, 231, 32]], ![[300, 261, 3, 34], [217, 262], [74, 49], [323, 429, 87, 219], [431, 238], [218, 228], [265, 258, 357, 67], [186, 290, 7, 425]]]
 h' := ![![[132, 448, 38], [223, 36, 271], [18, 445, 337], [201, 229, 151], [419, 3, 165], [263, 338, 86], [347, 43, 49], [263, 422, 383], [0, 1]], ![[251, 8, 419], [141, 346, 337], [416, 98, 412], [157, 427, 313], [32, 101, 63], [333, 88, 279], [240, 36, 198], [49, 385, 363], [132, 448, 38]], ![[0, 1], [267, 75, 306], [271, 371, 165], [312, 258, 450], [53, 353, 229], [6, 31, 92], [305, 378, 210], [156, 107, 168], [251, 8, 419]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [452, 27], []]
 b := ![[], [177, 117, 324], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 3
  hpos := by decide
  P := [194, 35, 74, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25968, 3838, 15614, -34004, 14214]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22242, -78, -8450, -34004, 14214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 95443993 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3509, -359, 404, -278, 312]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![-3509, -359, 404, -278, 312]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![135, 408, 1, 0, 0], ![217, 409, 0, 1, 0], ![82, 270, 0, 0, 1]] where
  M :=![![![-3509, -359, 404, -278, 312], ![6240, 639, -718, 496, -556], ![-5560, -575, 639, -440, 496], ![1840, 196, -216, 143, -162], ![-1620, -160, 196, -135, 143]]]
  hmulB := by decide  
  f := ![![![107, 153, 110, 46, 32]], ![![640, 601, 306, 188, 92]], ![![605, 584, 307, 182, 92]], ![![627, 614, 328, 191, 98]], ![![402, 388, 204, 121, 61]]]
  g := ![![![-51, -297, 404, -278, 312], ![90, 527, -718, 496, -556], ![-81, -471, 639, -440, 496], ![29, 161, -216, 143, -162], ![-23, -139, 196, -135, 143]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P1 : CertificateIrreducibleZModOfList' 457 2 2 8 [56, 449, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 456], [0, 1]]
 g := ![![[261, 253], [403], [266], [97, 266], [18], [34], [199, 64], [8, 1]], ![[0, 204], [403], [266], [397, 191], [18], [34], [254, 393], [16, 456]]]
 h' := ![![[8, 456], [412, 177], [147, 100], [52, 209], [263, 209], [281, 240], [281, 374], [9, 8], [0, 1]], ![[0, 1], [0, 280], [33, 357], [353, 248], [107, 248], [373, 217], [74, 83], [73, 449], [8, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [297, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N1 : CertifiedPrimeIdeal' SI457N1 457 where
  n := 2
  hpos := by decide
  P := [56, 449, 1]
  hirr := P457P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292, -1845, 3796, -4550, 3822]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![354, -1579, 3796, -4550, 3822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N1 B_one_repr
lemma NI457N1 : Nat.card (O ⧸ I457N1) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N1
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![107, 153, 110, 46, 32]] ![![-3509, -359, 404, -278, 312]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![457, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 3, -2, -1, 0]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![11, 3, -2, -1, 0]] 
 ![![461, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![433, 0, 1, 0, 0], ![453, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![11, 3, -2, -1, 0], ![0, 9, 6, -4, -2], ![-20, -9, 9, 7, -4], ![-40, -34, -12, 13, 8], ![80, 22, -34, -16, 13]]]
  hmulB := by decide  
  f := ![![![-1329, -379, 392, -201, 186]], ![![-384, -109, 114, -58, 54]], ![![-1257, -358, 371, -190, 176]], ![![-1297, -369, 384, -196, 182]], ![![-247, -69, 74, -37, 35]]]
  g := ![![![2, 3, -2, -1, 0], ![-4, 9, 6, -4, -2], ![-12, -9, 9, 7, -4], ![7, -34, -12, 13, 8], ![39, 22, -34, -16, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N0 : Nat.card (O ⧸ I461N0) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N0)

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := prime_ideal_of_norm_prime hp461.out _ NI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -5, 4, -3, 2]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![-11, -5, 4, -3, 2]] 
 ![![461, 0, 0, 0, 0], ![180, 1, 0, 0, 0], ![396, 0, 1, 0, 0], ![228, 0, 0, 1, 0], ![225, 0, 0, 0, 1]] where
  M :=![![![-11, -5, 4, -3, 2], ![40, 17, -10, 6, -6], ![-60, -21, 17, -7, 6], ![40, 6, -16, 11, -4], ![-40, -12, 6, -14, 11]]]
  hmulB := by decide  
  f := ![![![-751, -907, -538, -251, -156]], ![![-300, -361, -214, -100, -62]], ![![-656, -791, -469, -219, -136]], ![![-388, -466, -276, -129, -80]], ![![-395, -473, -280, -131, -81]]]
  g := ![![![-1, -5, 4, -3, 2], ![2, 17, -10, 6, -6], ![-6, -21, 17, -7, 6], ![8, 6, -16, 11, -4], ![1, -12, 6, -14, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N1 : Nat.card (O ⧸ I461N1) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N1)

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := prime_ideal_of_norm_prime hp461.out _ NI461N1

def I461N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -4, 2, -1, 0]] i)))

def SI461N2: IdealEqSpanCertificate' Table ![![9, -4, 2, -1, 0]] 
 ![![461, 0, 0, 0, 0], ![324, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![9, -4, 2, -1, 0], ![0, 11, -8, 4, -2], ![-20, -16, 11, -7, 4], ![40, 14, -12, 7, -6], ![-60, -22, 14, -9, 7]]]
  hmulB := by decide  
  f := ![![![109, 50, -6, -37, -14]], ![![76, 35, -4, -26, -10]], ![![14, 6, -1, -5, -2]], ![![50, 22, -4, -17, -6]], ![![26, 12, -2, -9, -3]]]
  g := ![![![3, -4, 2, -1, 0], ![-8, 11, -8, 4, -2], ![12, -16, 11, -7, 4], ![-10, 14, -12, 7, -6], ![16, -22, 14, -9, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N2 : Nat.card (O ⧸ I461N2) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N2)

lemma isPrimeI461N2 : Ideal.IsPrime I461N2 := prime_ideal_of_norm_prime hp461.out _ NI461N2

def I461N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -2, 2, -2, 2]] i)))

def SI461N3: IdealEqSpanCertificate' Table ![![-21, -2, 2, -2, 2]] 
 ![![461, 0, 0, 0, 0], ![366, 1, 0, 0, 0], ![328, 0, 1, 0, 0], ![184, 0, 0, 1, 0], ![442, 0, 0, 0, 1]] where
  M :=![![![-21, -2, 2, -2, 2], ![40, 5, -4, 2, -4], ![-40, -6, 5, -2, 2], ![0, -8, -4, 3, 0], ![0, -2, -8, -4, 3]]]
  hmulB := by decide  
  f := ![![![1159, 326, -294, 170, -142]], ![![914, 257, -232, 134, -112]], ![![832, 234, -211, 122, -102]], ![![456, 128, -116, 67, -56]], ![![1118, 314, -284, 164, -137]]]
  g := ![![![-1, -2, 2, -2, 2], ![2, 5, -4, 2, -4], ![0, -6, 5, -2, 2], ![8, -8, -4, 3, 0], ![6, -2, -8, -4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N3 : Nat.card (O ⧸ I461N3) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N3)

lemma isPrimeI461N3 : Ideal.IsPrime I461N3 := prime_ideal_of_norm_prime hp461.out _ NI461N3

def I461N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -11, 12, -9, 10]] i)))

def SI461N4: IdealEqSpanCertificate' Table ![![-109, -11, 12, -9, 10]] 
 ![![461, 0, 0, 0, 0], ![377, 1, 0, 0, 0], ![160, 0, 1, 0, 0], ![308, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-109, -11, 12, -9, 10], ![200, 23, -22, 14, -18], ![-180, -19, 23, -13, 14], ![40, -6, -8, 9, -4], ![-40, -8, -6, -6, 9]]]
  hmulB := by decide  
  f := ![![![-6169, -1757, 1418, -897, 736]], ![![-5013, -1428, 1152, -729, 598]], ![![-2180, -621, 501, -317, 260]], ![![-4092, -1166, 940, -595, 488]], ![![-412, -118, 94, -60, 49]]]
  g := ![![![10, -11, 12, -9, 10], ![-19, 23, -22, 14, -18], ![15, -19, 23, -13, 14], ![2, -6, -8, 9, -4], ![12, -8, -6, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N4 : Nat.card (O ⧸ I461N4) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N4)

lemma isPrimeI461N4 : Ideal.IsPrime I461N4 := prime_ideal_of_norm_prime hp461.out _ NI461N4
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![11, 3, -2, -1, 0]] ![![-11, -5, 4, -3, 2]]
  ![![79, 32, -4, -12, -4]] where
 M := ![![![79, 32, -4, -12, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N1 : IdealMulLeCertificate' Table 
  ![![79, 32, -4, -12, -4]] ![![9, -4, 2, -1, 0]]
  ![![551, 20, -54, 29, -36]] where
 M := ![![![551, 20, -54, 29, -36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N2 : IdealMulLeCertificate' Table 
  ![![551, 20, -54, 29, -36]] ![![-21, -2, 2, -2, 2]]
  ![![-8611, -838, 924, -723, 806]] where
 M := ![![![-8611, -838, 924, -723, 806]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N3 : IdealMulLeCertificate' Table 
  ![![-8611, -838, 924, -723, 806]] ![![-109, -11, 12, -9, 10]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![543519, 55781, -62696, 42412, -47944]]]
 hmul := by decide  
 g := ![![![![1179, 121, -136, 92, -104]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1, I461N2, I461N3, I461N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
    exact isPrimeI461N2
    exact isPrimeI461N3
    exact isPrimeI461N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0 ⊙ MulI461N1 ⊙ MulI461N2 ⊙ MulI461N3)
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


def P463P0 : CertificateIrreducibleZModOfList' 463 5 2 8 [340, 248, 216, 109, 208, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 280, 300, 217, 63], [253, 123, 4, 213, 447], [296, 333, 6, 213, 172], [59, 189, 153, 283, 244], [0, 1]]
 g := ![![[95, 199, 25, 231, 293], [162, 206, 131, 43, 206], [124, 416, 173, 455, 249], [256, 353, 436, 8, 98], [424, 101, 398, 415], [232, 442, 92, 297], [96, 255, 1], []], ![[139, 20, 186, 453, 43, 356, 52, 166], [197, 26, 45, 127, 189, 344, 89, 396], [402, 345, 419, 408, 19, 365, 252, 165], [328, 336, 320, 298, 120, 184, 239, 257], [271, 137, 318, 240], [190, 146, 89, 407], [28, 273, 320, 448, 2, 420, 300, 454], [110, 22, 339, 117, 310, 210, 219, 27]], ![[407, 385, 28, 171, 111, 189, 132, 459], [444, 342, 207, 44, 26, 129, 161, 234], [389, 251, 230, 167, 343, 210, 98, 424], [230, 196, 230, 17, 206, 398, 69, 430], [143, 67, 367, 81], [290, 280, 49, 34], [159, 302, 254, 200, 214, 140, 190, 48], [128, 395, 453, 42, 355, 340, 193, 71]], ![[194, 52, 450, 279, 396, 3, 47, 375], [285, 100, 236, 363, 439, 47, 209, 206], [22, 85, 287, 131, 372, 401, 384, 410], [355, 432, 364, 429, 235, 287, 289, 58], [460, 362, 167, 259], [445, 310, 243, 2], [294, 288, 165, 334, 295, 353, 86, 316], [323, 366, 264, 156, 196, 439, 330, 78]], ![[448, 60, 295, 101, 187, 113, 48, 222], [103, 385, 333, 96, 29, 427, 279, 435], [314, 17, 310, 303, 294, 347, 4, 25], [224, 435, 385, 44, 108, 93, 429, 357], [221, 414, 363, 336], [347, 319, 368, 32], [279, 112, 6, 341, 196, 426, 389, 32], [130, 248, 194, 127, 424, 359, 155, 159]]]
 h' := ![![[110, 280, 300, 217, 63], [17, 244, 410, 219, 331], [436, 60, 37, 113, 241], [4, 46, 158, 176, 326], [222, 170, 382, 318, 431], [411, 55, 38, 149, 291], [233, 149, 413, 417, 173], [0, 0, 0, 1], [0, 1]], ![[253, 123, 4, 213, 447], [391, 88, 242, 387, 217], [262, 366, 58, 77, 107], [307, 78, 84, 302, 128], [128, 171, 148, 348, 150], [69, 138, 42, 359, 404], [198, 233, 290, 385, 83], [441, 189, 243, 400, 23], [110, 280, 300, 217, 63]], ![[296, 333, 6, 213, 172], [220, 418, 95, 199, 232], [438, 246, 197, 212, 254], [183, 100, 127, 9, 255], [151, 255, 424, 110, 53], [275, 87, 424, 159, 9], [447, 461, 316, 142, 118], [391, 12, 63, 23, 420], [253, 123, 4, 213, 447]], ![[59, 189, 153, 283, 244], [101, 461, 249, 201, 87], [382, 121, 376, 375, 400], [49, 27, 431, 27, 420], [163, 165, 366, 376, 163], [75, 116, 157, 182, 310], [433, 353, 98, 224, 203], [228, 188, 278, 266, 392], [296, 333, 6, 213, 172]], ![[0, 1], [281, 178, 393, 383, 59], [7, 133, 258, 149, 387], [48, 212, 126, 412, 260], [72, 165, 69, 237, 129], [241, 67, 265, 77, 375], [275, 193, 272, 221, 349], [55, 74, 342, 236, 91], [59, 189, 153, 283, 244]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [304, 411, 89, 311], [], [], []]
 b := ![[], [462, 366, 441, 43, 120], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 5
  hpos := by decide
  P := [340, 248, 216, 109, 208, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-151172278, -5406914, 173105514, 604384458, 393194416]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-326506, -11678, 373878, 1305366, 849232]
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



lemma PB547I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB547I9 : PrimesBelowBoundCertificateInterval O 419 463 547 where
  m := 9
  g := ![3, 4, 2, 2, 3, 3, 2, 5, 1]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB547I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1, I431N2, I431N3]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1]
    · exact ![I443N0, I443N1, I443N2]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1]
    · exact ![I461N0, I461N1, I461N2, I461N3, I461N4]
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
    · exact ![74618461, 421, 421]
    · exact ![185761, 431, 431, 431]
    · exact ![35152125121, 433]
    · exact ![84604519, 192721]
    · exact ![86938307, 443, 443]
    · exact ![90518849, 449, 449]
    · exact ![95443993, 208849]
    · exact ![461, 461, 461, 461, 461]
    · exact ![21276733558543]
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
      exact NI431N2
      exact NI431N3
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
      exact NI461N2
      exact NI461N3
      exact NI461N4
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
  β := ![I421N1, I421N2, I431N1, I431N2, I431N3, I433N1, I443N1, I443N2, I449N1, I449N2, I461N0, I461N1, I461N2, I461N3, I461N4]
  Il := ![[I421N1, I421N2], [I431N1, I431N2, I431N3], [I433N1], [], [I443N1, I443N2], [I449N1, I449N2], [], [I461N0, I461N1, I461N2, I461N3, I461N4], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
