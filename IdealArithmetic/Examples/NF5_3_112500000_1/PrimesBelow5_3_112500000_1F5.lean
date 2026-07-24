
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 19, 14, 10, 10]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-7, 19, 14, 10, 10]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![46, 145, 176, 1, 0], ![13, 36, 104, 0, 1]] where
  M :=![![![-7, 19, 14, 10, 10], ![268, 79, 86, 104, 20], ![326, 233, 185, 194, 104], ![416, 141, 122, 139, 30], ![764, 453, 372, 374, 159]]]
  hmulB := by decide  
  f := ![![![-109, -3, -4, -22, 14]], ![![328, -1, 14, 76, -44]], ![![-514, -3, -31, -122, 76]], ![![-238, -4, -18, -57, 38]], ![![-219, -2, -14, -52, 33]]]
  g := ![![![-3, -9, -14, 10, 10], ![-24, -79, -102, 104, 20], ![-50, -159, -225, 194, 104], ![-32, -106, -138, 139, 30], ![-93, -299, -412, 374, 159]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [168, 69, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 21, 98], [140, 177, 101], [0, 1]]
 g := ![![[20, 94, 50], [187, 15, 90], [154, 159, 70], [105, 33], [67, 86], [102, 102], [1]], ![[73, 92, 79, 33], [55, 28, 27, 25], [87, 198, 156, 126], [98, 16], [53, 43], [], [147, 195, 114, 121]], ![[138, 108, 17, 142], [132, 129, 181, 30], [91, 2, 95, 127], [112, 140], [59, 58], [39, 102], [47, 98, 128, 78]]]
 h' := ![![[23, 21, 98], [26, 103, 100], [197, 74, 182], [0, 34, 95], [39, 70, 113], [143, 5, 177], [31, 130, 163], [0, 1]], ![[140, 177, 101], [129, 62, 133], [139, 154, 64], [82, 121, 48], [167, 65, 195], [64, 14, 178], [8, 175], [23, 21, 98]], ![[0, 1], [177, 34, 165], [193, 170, 152], [50, 44, 56], [89, 64, 90], [38, 180, 43], [53, 93, 36], [140, 177, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 120], []]
 b := ![[], [12, 178, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [168, 69, 36, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13427303, -6904605, -6091752, -6495040, -2478405]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1595798, 5146225, 7008992, -6495040, -2478405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -3, -4, -22, 14]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-109, -3, -4, -22, 14]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![168, 70, 1, 0, 0], ![137, 129, 0, 1, 0], ![156, 123, 0, 0, 1]] where
  M :=![![![-109, -3, -4, -22, 14], ![328, -1, 14, 76, -44], ![-514, -3, -31, -122, 76], ![556, 15, 28, 121, -78], ![-516, -11, -14, -110, 65]]]
  hmulB := by decide  
  f := ![![![-7, 19, 14, 10, 10]], ![![268, 79, 86, 104, 20]], ![![90, 45, 43, 46, 16]], ![![171, 65, 66, 75, 20]], ![![164, 66, 66, 74, 21]]]
  g := ![![![7, 7, -4, -22, 14], ![-28, -27, 14, 76, -44], ![48, 43, -31, -122, 76], ![-43, -40, 28, 121, -78], ![34, 36, -14, -110, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [29, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [151, 198], [0, 1]]
 g := ![![[84, 151], [127, 98], [180, 116], [115], [31], [33], [151, 1]], ![[0, 48], [0, 101], [184, 83], [115], [31], [33], [103, 198]]]
 h' := ![![[151, 198], [98, 143], [153, 140], [76, 64], [25, 48], [39, 35], [198, 86], [0, 1]], ![[0, 1], [0, 56], [0, 59], [188, 135], [109, 151], [150, 164], [50, 113], [151, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [48, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [29, 48, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![746944, 426459, 405461, 432964, 199842]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-793276, -544667, 405461, 432964, 199842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-7, 19, 14, 10, 10]] ![![-109, -3, -4, -22, 14]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -28, -22, 0, 16]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-35, -28, -22, 0, 16]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![206, 26, 1, 1, 0], ![11, 51, 25, 0, 1]] where
  M :=![![![-35, -28, -22, 0, 16], ![340, 131, -68, -68, 0], ![-68, 170, 63, -136, -68], ![-160, -172, 30, 97, -28], ![-636, -410, -106, 68, 69]]]
  hmulB := by decide  
  f := ![![![5607, -152, 342, 816, -632]], ![![-14484, 393, -884, -2108, 1632]], ![![18700, -510, 1141, 2720, -2108]], ![![3690, -100, 225, 537, -416]], ![![-933, 25, -57, -136, 105]]]
  g := ![![![-1, -4, -2, 0, 16], ![68, 9, 0, -68, 0], ![136, 34, 9, -136, -68], ![-94, -6, 3, 97, -28], ![-73, -27, -9, 68, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [17, 6, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [139, 128, 63], [125, 82, 148], [0, 1]]
 g := ![![[178, 25, 49], [111, 132, 150], [25, 188], [23, 81], [29, 22, 139], [119, 66], [1]], ![[138, 62, 39, 18], [28, 194, 57, 160], [147, 170], [103, 47], [193, 23, 184, 102], [48, 204], [26, 185, 46, 12]], ![[102, 62, 19, 69], [179, 3, 160, 73], [158, 53], [32, 134], [124, 166, 73, 44], [73, 144], [32, 194, 74, 199]]]
 h' := ![![[139, 128, 63], [12, 178, 7], [61, 83, 19], [8, 122, 140], [140, 91, 9], [165, 56, 136], [194, 205, 53], [0, 1]], ![[125, 82, 148], [11, 154, 183], [52, 111, 35], [21, 208, 176], [57, 5, 141], [109, 170, 121], [202, 157, 170], [139, 128, 63]], ![[0, 1], [119, 90, 21], [9, 17, 157], [95, 92, 106], [46, 115, 61], [194, 196, 165], [198, 60, 199], [125, 82, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 23], []]
 b := ![[], [74, 24, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [17, 6, 158, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-755147, -382469, -290318, -292672, -101515]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![287450, 58788, 12039, -292672, -101515]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 3, -2, -2, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![4, 3, -2, -2, 1]] 
 ![![211, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![164, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![4, 3, -2, -2, 1], ![20, 13, 4, -4, -4], ![-44, -12, 13, 8, -4], ![5, -9, -4, 5, 3], ![27, 5, -16, -4, 10]]]
  hmulB := by decide  
  f := ![![![2062, 65, 88, 500, -295]], ![![280, 9, 12, 68, -40]], ![![1238, 39, 53, 300, -177]], ![![1545, 49, 66, 375, -221]], ![![603, 19, 26, 146, -86]]]
  g := ![![![2, 3, -2, -2, 1], ![0, 13, 4, -4, -4], ![-11, -12, 13, 8, -4], ![-1, -9, -4, 5, 3], ![9, 5, -16, -4, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3546, -101, 218, 508, -397]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![3546, -101, 218, 508, -397]] 
 ![![211, 0, 0, 0, 0], ![175, 1, 0, 0, 0], ![196, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![3546, -101, 218, 508, -397], ![-9092, 263, -560, -1296, 1016], ![11632, -342, 719, 1648, -1296], ![-11519, 341, -712, -1629, 1283], ![7711, -235, 480, 1078, -854]]]
  hmulB := by decide  
  f := ![![![-700, 125, 584, 58, -325]], ![![-612, 84, 488, 58, -269]], ![![-640, 106, 527, 56, -292]], ![![-139, 49, 138, 5, -79]], ![![-393, 103, 358, 24, -202]]]
  g := ![![![11, -101, 218, 508, -397], ![-31, 263, -560, -1296, 1016], ![42, -342, 719, 1648, -1296], ![-44, 341, -712, -1629, 1283], ![32, -235, 480, 1078, -854]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-35, -28, -22, 0, 16]] ![![4, 3, -2, -2, 1]]
  ![![700, -125, -584, -58, 325]] where
 M := ![![![700, -125, -584, -58, 325]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![700, -125, -584, -58, 325]] ![![3546, -101, 218, 508, -397]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2159, 3, -98, -542, 308]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-2159, 3, -98, -542, 308]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![153, 63, 172, 214, 1]] where
  M :=![![![-2159, 3, -98, -542, 308], ![7196, 169, 426, 1728, -1084], ![-12582, -629, -489, -2618, 1728], ![12862, 377, 470, 2877, -1732], ![-11050, 133, -628, -2918, 1687]]]
  hmulB := by decide  
  f := ![![![-921, 25, -56, -134, 104]], ![![2384, -63, 146, 348, -268]], ![![-3070, 87, -185, -446, 348]], ![![3058, -81, 188, 447, -344]], ![![599, -11, 40, 90, -65]]]
  g := ![![![-221, -87, -238, -298, 308], ![776, 307, 838, 1048, -1084], ![-1242, -491, -1335, -1670, 1728], ![1246, 491, 1338, 1675, -1732], ![-1207, -476, -1304, -1632, 1687]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [115, 103, 103, 176, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 191, 81, 28], [28, 37, 99, 218], [150, 217, 43, 200], [0, 1]]
 g := ![![[133, 210, 61, 177], [198, 177, 200, 203], [148, 143, 204, 69], [30, 113, 178, 82], [33, 38, 191, 164], [99, 47, 1], []], ![[213, 136, 118, 67, 1, 89], [137, 28, 145, 162, 189, 202], [21, 41, 65, 69, 86, 76], [15, 144, 37, 56, 207, 110], [60, 136, 51, 81, 68, 146], [189, 65, 82], [103, 31, 70, 36, 216, 98]], ![[51, 57, 94, 125, 17, 31], [97, 7, 197, 8, 117, 171], [109, 179, 25, 199, 141, 115], [38, 112, 62, 14, 25, 136], [142, 52, 111, 123, 161, 183], [44, 33, 101], [28, 72, 181, 134, 212, 98]], ![[24, 139, 53, 59, 154, 106], [56, 11, 38, 113, 159, 14], [118, 97, 149, 15, 6, 212], [96, 177, 107, 201, 107, 166], [140, 211, 88, 1, 125, 136], [38, 51, 94], [78, 48, 219, 73, 149, 98]]]
 h' := ![![[92, 191, 81, 28], [199, 115, 50, 20], [151, 75, 141, 42], [118, 210, 156, 31], [219, 180, 189, 159], [211, 8, 11, 155], [0, 0, 0, 1], [0, 1]], ![[28, 37, 99, 218], [46, 82, 169, 97], [89, 181, 145, 151], [206, 144, 167, 135], [155, 201, 201, 158], [136, 176, 147, 161], [169, 166, 108, 159], [92, 191, 81, 28]], ![[150, 217, 43, 200], [93, 138, 169, 23], [195, 129, 144, 72], [179, 20, 185, 150], [126, 147, 35, 109], [69, 147, 117, 30], [0, 40, 69, 205], [28, 37, 99, 218]], ![[0, 1], [145, 111, 58, 83], [150, 61, 16, 181], [60, 72, 161, 130], [48, 141, 21, 20], [31, 115, 171, 100], [68, 17, 46, 81], [150, 217, 43, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [62, 87, 190], []]
 b := ![[], [], [56, 147, 188, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [115, 103, 103, 176, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1538610755895, 790587252134, 678230486526, 722393626999, 280929131224]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-185845499199, -75820394686, -213639372574, -266351750919, 280929131224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-921, 25, -56, -134, 104]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-921, 25, -56, -134, 104]] 
 ![![223, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-921, 25, -56, -134, 104], ![2384, -63, 146, 348, -268], ![-3070, 87, -185, -446, 348], ![3058, -81, 188, 447, -344], ![-2074, 61, -122, -298, 237]]]
  hmulB := by decide  
  f := ![![![-2159, 3, -98, -542, 308]], ![![-142, 1, -6, -36, 20]], ![![-647, -2, -29, -160, 92]], ![![-165, 2, -8, -43, 24]], ![![-340, 1, -16, -86, 49]]]
  g := ![![![9, 25, -56, -134, 104], ![-24, -63, 146, 348, -268], ![29, 87, -185, -446, 348], ![-31, -81, 188, 447, -344], ![18, 61, -122, -298, 237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-2159, 3, -98, -542, 308]] ![![-921, 25, -56, -134, 104]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0, 0, 0]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]] where
  M :=![![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 5 2 7 [12, 134, 111, 130, 123, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 36, 178, 106, 89], [55, 71, 11, 56, 218], [79, 83, 116, 151, 211], [146, 36, 149, 141, 163], [0, 1]]
 g := ![![[166, 97, 202, 197, 69], [161, 43, 166, 132, 92], [152, 190, 205, 219], [137, 134, 164, 78], [80, 8, 30, 76], [17, 104, 1], []], ![[205, 14, 204, 203, 174, 154, 204, 190], [149, 93, 209, 85, 114, 194, 179, 75], [0, 4, 126, 173], [196, 26, 41, 177], [55, 190, 191, 65], [37, 67, 74, 43, 118, 188, 15, 77], [103, 154, 194, 91, 151, 202, 175, 134]], ![[127, 165, 25, 178, 116, 152, 64, 32], [67, 128, 173, 79, 63, 191, 146, 111], [186, 13, 37, 21], [161, 54, 66, 133], [114, 111, 16, 186], [100, 160, 158, 82, 80, 46, 51, 32], [45, 221, 96, 208, 195, 154, 217, 179]], ![[221, 129, 88, 225, 187, 47, 192, 137], [121, 140, 218, 150, 95, 214, 47, 198], [198, 151, 17, 209], [26, 190, 225, 44], [130, 144, 169, 76], [220, 191, 187, 111, 61, 37, 0, 118], [29, 31, 200, 14, 71, 15, 66, 217]], ![[197, 18, 34, 67, 210, 145, 57, 179], [83, 79, 219, 180, 90, 135, 61, 52], [145, 101, 190, 1], [194, 11, 108, 4], [13, 94, 95, 116], [52, 6, 225, 17, 204, 29, 187, 128], [162, 184, 69, 209, 1, 20, 95, 41]]]
 h' := ![![[51, 36, 178, 106, 89], [111, 141, 89, 89, 110], [165, 221, 142, 123, 41], [20, 78, 120, 100, 197], [23, 189, 49, 137, 140], [23, 106, 55, 186, 168], [0, 0, 0, 1], [0, 1]], ![[55, 71, 11, 56, 218], [21, 225, 32, 226, 170], [214, 13, 13, 187, 179], [21, 169, 223, 223, 20], [28, 206, 107, 212, 75], [190, 57, 42, 195, 92], [209, 122, 145, 159, 188], [51, 36, 178, 106, 89]], ![[79, 83, 116, 151, 211], [197, 172, 170, 152, 20], [91, 103, 167, 120, 65], [196, 154, 169, 95, 193], [53, 134, 8, 134, 157], [115, 57, 139, 123, 58], [125, 43, 87, 77, 20], [55, 71, 11, 56, 218]], ![[146, 36, 149, 141, 163], [106, 4, 190, 28, 179], [60, 107, 146, 18, 4], [47, 194, 149, 79, 45], [86, 32, 21, 48, 80], [113, 115, 150, 29, 168], [101, 22, 29, 24, 34], [79, 83, 116, 151, 211]], ![[0, 1], [194, 139, 200, 186, 202], [61, 10, 213, 6, 165], [62, 86, 20, 184, 226], [183, 120, 42, 150, 2], [148, 119, 68, 148, 195], [65, 40, 193, 193, 212], [146, 36, 149, 141, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 168, 225, 131], [], [], []]
 b := ![[], [41, 22, 205, 118, 98], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 5
  hpos := by decide
  P := [12, 134, 111, 130, 123, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17123829049247, -8784117361431, -7489940186259, -7985048361954, -3113332142844]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-75435370261, -38696552253, -32995331217, -35176424502, -13715119572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 602738989907 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53827, 1454, -3282, -7844, 6070]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-53827, 1454, -3282, -7844, 6070]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![5, 31, 58, 1, 0], ![109, 107, 131, 0, 1]] where
  M :=![![![-53827, 1454, -3282, -7844, 6070], ![139116, -3759, 8484, 20276, -15688], ![-179772, 4858, -10963, -26200, 20276], ![178502, -4818, 10886, 26015, -20130], ![-121730, 3292, -7418, -17740, 13729]]]
  hmulB := by decide  
  f := ![![![-43, -2, 6, -4, 2]], ![![60, -35, 12, 52, -8]], ![![-84, 14, -31, -32, 52]], ![![-13, -1, -6, -1, 12]], ![![-41, -9, -9, 4, 27]]]
  g := ![![![-2953, -1768, -1500, -7844, 6070], ![7632, 4569, 3876, 20276, -15688], ![-9864, -5906, -5011, -26200, 20276], ![9793, 5863, 4974, 26015, -20130], ![-6679, -3999, -3393, -17740, 13729]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [164, 193, 142, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [160, 134, 61], [156, 94, 168], [0, 1]]
 g := ![![[161, 192, 85], [213, 225], [26, 33, 220], [196, 16], [151, 121], [77, 209, 12], [1]], ![[130, 187, 220, 209], [38, 224], [219, 176, 22, 168], [97, 62], [15, 36], [37, 225, 212, 49], [94, 164, 4, 42]], ![[76, 86, 160, 149], [188, 26], [16, 164, 226, 60], [227, 204], [129, 25], [97, 67, 12, 111], [119, 73, 54, 187]]]
 h' := ![![[160, 134, 61], [117, 82, 139], [87, 179, 15], [103, 104, 92], [141, 35, 225], [196, 201, 218], [65, 36, 87], [0, 1]], ![[156, 94, 168], [48, 225, 206], [201, 170, 192], [221, 196, 107], [127, 110, 156], [86, 141, 6], [33, 15, 69], [160, 134, 61]], ![[0, 1], [218, 151, 113], [89, 109, 22], [44, 158, 30], [116, 84, 77], [152, 116, 5], [3, 178, 73], [156, 94, 168]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181, 103], []]
 b := ![[], [168, 139, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [164, 193, 142, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20095416, 1380618, -257806, -6573318, 2703186]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1230900, -367194, 117368, -6573318, 2703186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -2, 6, -4, 2]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-43, -2, 6, -4, 2]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![126, 56, 1, 0, 0], ![49, 140, 0, 1, 0], ![42, 111, 0, 0, 1]] where
  M :=![![![-43, -2, 6, -4, 2], ![60, -35, 12, 52, -8], ![-84, 14, -31, -32, 52], ![250, 54, 22, 35, -30], ![-118, 68, 62, -20, 9]]]
  hmulB := by decide  
  f := ![![![-53827, 1454, -3282, -7844, 6070]], ![![139116, -3759, 8484, 20276, -15688]], ![![3618, -98, 221, 528, -408]], ![![74311, -2008, 4532, 10831, -8380]], ![![57028, -1541, 3478, 8312, -6431]]]
  g := ![![![-3, 0, 6, -4, 2], ![-16, -31, 12, 52, -8], ![14, 2, -31, -32, 52], ![-13, -12, 22, 35, -30], ![-32, -7, 62, -20, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [22, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [205, 228], [0, 1]]
 g := ![![[126, 55], [94], [46, 104], [118], [146], [188, 56], [205, 1]], ![[180, 174], [94], [69, 125], [118], [146], [218, 173], [181, 228]]]
 h' := ![![[205, 228], [49, 183], [133, 134], [70, 185], [190, 205], [215, 72], [70, 96], [0, 1]], ![[0, 1], [8, 46], [123, 95], [210, 44], [79, 24], [90, 157], [56, 133], [205, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [45, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [22, 24, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![157841, 79370, 86171, 97841, 37605]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74556, -98769, 86171, 97841, 37605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-53827, 1454, -3282, -7844, 6070]] ![![-43, -2, 6, -4, 2]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77608, 2039, -4714, -11406, 8783]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-77608, 2039, -4714, -11406, 8783]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![180, 187, 1, 0, 0], ![215, 0, 0, 1, 0], ![215, 108, 0, 0, 1]] where
  M :=![![![-77608, 2039, -4714, -11406, 8783], ![201364, -5253, 12216, 29660, -22812], ![-261528, 6750, -15849, -38636, 29660], ![259963, -6701, 15744, 38427, -29495], ![-178915, 4521, -10816, -26588, 20338]]]
  hmulB := by decide  
  f := ![![![-1934, -2717, -1132, 1036, 941]], ![![20320, 8703, -5816, -5100, 2072]], ![![14896, 4971, -5521, -3328, 2368]], ![![-1875, -2554, -1026, 981, 864]], ![![7467, 1400, -3742, -1350, 1845]]]
  g := ![![![5729, -279, -4714, -11406, 8783], ![-14892, 747, 12216, 29660, -22812], ![19404, -999, -15849, -38636, 29660], ![-19289, 1007, 15744, 38427, -29495], ![13355, -727, -10816, -26588, 20338]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [182, 214, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 232], [0, 1]]
 g := ![![[142, 201], [46], [195], [42, 187], [71], [148, 120], [19, 1]], ![[0, 32], [46], [195], [100, 46], [71], [98, 113], [38, 232]]]
 h' := ![![[19, 232], [129, 30], [87, 38], [45, 112], [202, 113], [92, 49], [37, 179], [0, 1]], ![[0, 1], [0, 203], [110, 195], [76, 121], [19, 120], [91, 184], [176, 54], [19, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [172, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [182, 214, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![767, 855, 10, -1109, -141]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1149, 61, 10, -1109, -141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -5, -4, 0, 4]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-17, -5, -4, 0, 4]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![131, 216, 1, 0, 0], ![0, 164, 0, 1, 0], ![185, 40, 0, 0, 1]] where
  M :=![![![-17, -5, -4, 0, 4], ![88, 23, -10, -8, 0], ![-10, 45, 13, -22, -8], ![-4, -29, 12, 21, -6], ![-108, -65, -6, 28, 15]]]
  hmulB := by decide  
  f := ![![![203, 11, 10, 52, -28]], ![![-652, -7, -14, -156, 104]], ![![-485, 0, -7, -114, 80]], ![![-464, -5, -10, -111, 74]], ![![55, 8, 6, 16, -5]]]
  g := ![![![-1, 3, -4, 0, 4], ![6, 15, -10, -8, 0], ![-1, 5, 13, -22, -8], ![-2, -25, 12, 21, -6], ![-9, -17, -6, 28, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [227, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 232], [0, 1]]
 g := ![![[], [], [231], [], [56], [0, 36], [0, 1]], ![[], [], [231], [], [56], [0, 197], [0, 232]]]
 h' := ![![[0, 232], [144], [221], [0, 124], [103], [0, 216], [0, 6], [0, 1]], ![[0, 1], [144], [221], [0, 109], [103], [0, 17], [0, 227], [0, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [0, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [227, 0, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51992, 35334, 32498, 33360, 20748]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34522, -57018, 32498, 33360, 20748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15408, -417, 940, 2244, -1737]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![15408, -417, 940, 2244, -1737]] 
 ![![233, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![217, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![15408, -417, 940, 2244, -1737], ![-39808, 1079, -2428, -5796, 4488], ![51428, -1392, 3139, 7488, -5796], ![-51051, 1385, -3114, -7431, 5755], ![34799, -941, 2126, 5066, -3920]]]
  hmulB := by decide  
  f := ![![![1742, 1719, 358, -726, -399]], ![![904, 917, 208, -384, -222]], ![![1562, 1551, 329, -654, -363]], ![![433, 403, 68, -173, -85]], ![![1655, 1601, 312, -680, -360]]]
  g := ![![![466, -417, 940, 2244, -1737], ![-1206, 1079, -2428, -5796, 4488], ![1553, -1392, 3139, 7488, -5796], ![-1547, 1385, -3114, -7431, 5755], ![1047, -941, 2126, 5066, -3920]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-77608, 2039, -4714, -11406, 8783]] ![![-17, -5, -4, 0, 4]]
  ![![642968, -17314, 39190, 93794, -72539]] where
 M := ![![![642968, -17314, 39190, 93794, -72539]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![642968, -17314, 39190, 93794, -72539]] ![![15408, -417, 940, 2244, -1737]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![5298987821, -143188053, 323153292, 772161068, -597548538]]]
 hmul := by decide  
 g := ![![![![22742437, -614541, 1386924, 3313996, -2564586]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-488, -84, -78, -146, 21]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-488, -84, -78, -146, 21]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![160, 217, 61, 1, 0], ![99, 230, 170, 0, 1]] where
  M :=![![![-488, -84, -78, -146, 21], ![348, -367, -282, -92, -292], ![-3786, -1045, -941, -1338, -92], ![801, -520, -400, -77, -471], ![-5425, -1894, -1650, -2096, -402]]]
  hmulB := by decide  
  f := ![![![2354, -64, 146, 344, -267]], ![![-6116, 149, -370, -880, 688]], ![![7886, -217, 467, 1146, -880]], ![![-1997, 38, -121, -281, 225]], ![![721, -38, 38, 114, -77]]]
  g := ![![![87, 112, 22, -146, 21], ![184, 363, 230, -92, -292], ![918, 1299, 403, -1338, -92], ![250, 521, 353, -77, -471], ![1547, 2282, 814, -2096, -402]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [24, 124, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 126, 81], [72, 112, 158], [0, 1]]
 g := ![![[185, 24, 155], [212, 106, 120], [128, 166, 15], [225, 216, 80], [40, 90], [177, 137, 54], [1]], ![[177, 83, 90, 85], [73, 3, 75, 29], [236, 61, 166, 133], [78, 132, 7, 226], [55, 1], [202, 118, 214, 2], [141, 210, 11, 144]], ![[213, 224, 22, 114], [24, 121, 209, 105], [90, 159, 30, 57], [164, 181, 88, 21], [68, 102], [53, 118, 216, 189], [38, 212, 143, 95]]]
 h' := ![![[101, 126, 81], [170, 117, 148], [35, 69, 169], [97, 161, 60], [44, 186, 115], [54, 196, 125], [215, 115, 173], [0, 1]], ![[72, 112, 158], [68, 78, 2], [152, 43, 139], [209, 182, 163], [7, 40, 222], [128, 180, 1], [173, 133, 11], [101, 126, 81]], ![[0, 1], [166, 44, 89], [101, 127, 170], [185, 135, 16], [150, 13, 141], [78, 102, 113], [213, 230, 55], [72, 112, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 220], []]
 b := ![[], [154, 113, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [24, 124, 66, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11161958, 6637846, 5584812, 5819311, 3054202]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5114200, -8195059, -3634341, 5819311, 3054202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2354, 64, -146, -344, 267]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-2354, 64, -146, -344, 267]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![171, 57, 1, 0, 0], ![120, 201, 0, 1, 0], ![165, 157, 0, 0, 1]] where
  M :=![![![-2354, 64, -146, -344, 267], ![6116, -149, 370, 880, -688], ![-7886, 217, -467, -1146, 880], ![7797, -226, 476, 1145, -879], ![-5333, 126, -338, -770, 610]]]
  hmulB := by decide  
  f := ![![![488, 84, 78, 146, -21]], ![![-348, 367, 282, 92, 292]], ![![282, 152, 127, 132, 55]], ![![-51, 353, 278, 151, 237]], ![![131, 307, 246, 170, 179]]]
  g := ![![![83, 149, -146, -344, 267], ![-206, -377, 370, 880, -688], ![269, 498, -467, -1146, 880], ![-276, -500, 476, 1145, -879], ![185, 328, -338, -770, 610]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [180, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 238], [0, 1]]
 g := ![![[93, 81], [119, 133], [188, 54], [53, 157], [61], [47, 186], [229, 1]], ![[0, 158], [223, 106], [126, 185], [156, 82], [61], [99, 53], [219, 238]]]
 h' := ![![[229, 238], [90, 9], [98, 33], [20, 66], [196, 184], [144, 104], [127, 159], [0, 1]], ![[0, 1], [0, 230], [7, 206], [77, 173], [29, 55], [60, 135], [210, 80], [229, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [202]]
 b := ![[], [27, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [180, 10, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21764, 10879, 11698, 13527, 5563]
  a := ![12, 6, 8, 15, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18911, -17775, 11698, 13527, 5563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-488, -84, -78, -146, 21]] ![![-2354, 64, -146, -344, 267]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [41, 215, 130, 68, 118, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [148, 138, 144, 145, 86], [97, 215, 164, 22, 240], [36, 51, 163, 205, 192], [83, 77, 11, 110, 205], [0, 1]]
 g := ![![[208, 107, 112, 153, 182], [64, 93, 140, 180], [147, 17, 92, 24], [209, 222, 89, 20], [159, 134, 131, 127, 187], [119, 123, 1], []], ![[150, 230, 224, 95, 152, 58, 106, 14], [184, 48, 204, 141], [223, 214, 110, 154], [132, 180, 168, 58], [141, 45, 118, 29, 58, 79, 89, 84], [158, 238, 190, 20, 158, 48, 65, 149], [25, 210, 4, 140, 92, 208, 173, 57]], ![[148, 192, 211, 152, 121, 69, 83, 194], [115, 85, 159, 25], [43, 191, 100, 29], [23, 194, 62, 1], [99, 181, 118, 239, 31, 133, 21, 161], [100, 169, 107, 111, 239, 115, 154, 41], [220, 187, 126, 167, 42, 50, 184, 240]], ![[153, 99, 65, 181, 112, 240, 159, 183], [239, 134, 97, 209], [219, 36, 25, 29], [209, 16, 184, 98], [86, 205, 240, 162, 217, 159, 227, 32], [71, 188, 228, 10, 100, 134, 203, 64], [129, 157, 172, 169, 150, 17, 26, 200]], ![[134, 52, 197, 115, 17, 148, 204, 193], [91, 117, 2, 123], [226, 178, 56, 160], [211, 4, 22, 6], [104, 29, 56, 70, 74, 65, 63, 60], [226, 121, 173, 213, 227, 1, 117, 61], [125, 64, 229, 106, 66, 231, 150, 98]]]
 h' := ![![[148, 138, 144, 145, 86], [232, 103, 108, 148, 69], [98, 41, 119, 231, 136], [10, 135, 48, 36, 54], [229, 193, 165, 237, 206], [182, 220, 219, 44, 118], [0, 0, 0, 1], [0, 1]], ![[97, 215, 164, 22, 240], [107, 198, 152, 232, 68], [105, 100, 195, 55, 83], [191, 56, 220, 102, 40], [209, 73, 150, 152, 96], [167, 1, 72, 200, 149], [40, 142, 73, 174, 18], [148, 138, 144, 145, 86]], ![[36, 51, 163, 205, 192], [137, 102, 103, 136, 23], [153, 113, 183, 94, 5], [179, 81, 25, 214, 149], [188, 114, 20, 151, 240], [3, 64, 103, 116, 70], [144, 165, 176, 181, 21], [97, 215, 164, 22, 240]], ![[83, 77, 11, 110, 205], [169, 36, 29, 151, 124], [150, 17, 118, 89, 89], [104, 120, 137, 41, 92], [210, 114, 109, 107, 154], [42, 142, 68, 39, 125], [156, 236, 79, 3, 99], [36, 51, 163, 205, 192]], ![[0, 1], [109, 43, 90, 56, 198], [15, 211, 108, 13, 169], [72, 90, 52, 89, 147], [218, 229, 38, 76, 27], [160, 55, 20, 83, 20], [71, 180, 154, 123, 103], [83, 77, 11, 110, 205]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [217, 120, 221, 153], [], [], []]
 b := ![[], [233, 237, 209, 46, 214], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [41, 215, 130, 68, 118, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-620291847153925, -316777526779459, -269772338241046, -287761768749234, -111277552789308]
  a := ![-25, -6, -33, -52, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2573825091925, -1314429571699, -1119387295606, -1194032235474, -461732584188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2352, 55, 102, 544, -333]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![2352, 55, 102, 544, -333]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![101, 56, 226, 1, 0], ![121, 178, 139, 0, 1]] where
  M :=![![![2352, 55, 102, 544, -333], ![-7788, -203, -352, -1808, 1088], ![12704, 274, 533, 2928, -1808], ![-13371, -339, -604, -3107, 1871], ![12371, 245, 500, 2834, -1780]]]
  hmulB := by decide  
  f := ![![![-94, -7, 0, -6, 7]], ![![168, -37, 0, 40, -12]], ![![-144, 50, -49, -64, 40]], ![![-129, 34, -44, -51, 36]], ![![-7, -2, -27, -10, 17]]]
  g := ![![![-49, 115, -305, 544, -333], ![172, -369, 1024, -1808, 1088], ![-256, 630, -1633, 2928, -1808], ![295, -635, 1759, -3107, 1871], ![-233, 631, -1564, 2834, -1780]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [247, 92, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 30, 64], [8, 220, 187], [0, 1]]
 g := ![![[28, 78, 118], [83, 38, 86], [143, 149], [8, 44, 194], [65, 147, 36], [186, 124, 93], [1]], ![[55, 58, 207, 204], [56, 109, 245, 119], [113, 28], [22, 233, 30, 49], [28, 38, 248, 21], [49, 5, 48, 101], [48, 42, 124, 100]], ![[181, 55, 78, 206], [122, 33, 82, 71], [54, 80], [229, 86, 161, 34], [133, 25, 63, 224], [159, 247, 123, 138], [26, 43, 138, 151]]]
 h' := ![![[112, 30, 64], [81, 114, 143], [90, 207, 191], [32, 23, 231], [9, 211, 52], [242, 217, 6], [4, 159, 120], [0, 1]], ![[8, 220, 187], [246, 175, 102], [41, 196, 48], [51, 24, 84], [119, 130, 95], [188, 234, 148], [22, 232, 181], [112, 30, 64]], ![[0, 1], [81, 213, 6], [68, 99, 12], [75, 204, 187], [156, 161, 104], [188, 51, 97], [114, 111, 201], [8, 220, 187]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 134], []]
 b := ![[], [230, 99, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [247, 92, 131, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10940846, -5663585, -4662850, -4847890, -1855395]
  a := ![-10, -3, -10, -18, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2801589, 2374815, 5373945, -4847890, -1855395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1151, 31, -70, -168, 130]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-1151, 31, -70, -168, 130]] 
 ![![251, 0, 0, 0, 0], ![191, 1, 0, 0, 0], ![208, 0, 1, 0, 0], ![244, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-1151, 31, -70, -168, 130], ![2980, -79, 182, 436, -336], ![-3850, 105, -233, -562, 436], ![3830, -101, 234, 561, -432], ![-2610, 73, -156, -380, 297]]]
  hmulB := by decide  
  f := ![![![59, 209, 100, -92, -70]], ![![39, 156, 78, -68, -54]], ![![42, 167, 81, -74, -56]], ![![66, 207, 96, -91, -68]], ![![26, 63, 26, -28, -19]]]
  g := ![![![160, 31, -70, -168, 130], ![-417, -79, 182, 436, -336], ![533, 105, -233, -562, 436], ![-537, -101, 234, 561, -432], ![357, 73, -156, -380, 297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, 12, 40, 2, -23]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-44, 12, 40, 2, -23]] 
 ![![251, 0, 0, 0, 0], ![212, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-44, 12, 40, 2, -23], ![-472, -289, 58, 144, 4], ![106, -175, -227, 38, 144], ![401, 284, -14, -133, -27], ![299, 448, 200, -168, -162]]]
  hmulB := by decide  
  f := ![![![-16698, -24, -848, -3244, 2157]], ![![-13904, -19, -706, -2700, 1796]], ![![-8150, -13, -413, -1586, 1054]], ![![-5943, -6, -302, -1151, 767]], ![![-4521, -8, -228, -882, 586]]]
  g := ![![![-24, 12, 40, 2, -23], ![160, -289, 58, 144, 4], ![204, -175, -227, 38, 144], ![-175, 284, -14, -133, -27], ![-367, 448, 200, -168, -162]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![2352, 55, 102, 544, -333]] ![![-1151, 31, -70, -168, 130]]
  ![![16698, 24, 848, 3244, -2157]] where
 M := ![![![16698, 24, 848, 3244, -2157]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![16698, 24, 848, 3244, -2157]] ![![-44, 12, 40, 2, -23]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB519I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB519I5 : PrimesBelowBoundCertificateInterval O 197 251 519 where
  m := 9
  g := ![2, 3, 2, 1, 2, 3, 2, 1, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB519I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7880599, 39601]
    · exact ![9393931, 211, 211]
    · exact ![2472973441, 223]
    · exact ![602738989907]
    · exact ![12008989, 52441]
    · exact ![54289, 54289, 233]
    · exact ![13651919, 57121]
    · exact ![812990017201]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I211N1, I211N2, I223N1, I233N2, I251N1, I251N2]
  Il := ![[], [I211N1, I211N2], [I223N1], [], [], [I233N2], [], [], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
