
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1266, -2068, 2922, -1633, -298]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-1266, -2068, 2922, -1633, -298]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![104, 170, 1, 0, 0], ![179, 64, 0, 1, 0], ![184, 4, 0, 0, 1]] where
  M :=![![![-1266, -2068, 2922, -1633, -298], ![-4005, -2349, 304, 1243, -8904], ![30441, 26740, -31547, 13241, 34170], ![-29391, -30772, 51232, -29392, -7080], ![16322, 18992, -36616, 22866, -6321]]]
  hmulB := by decide  
  f := ![![![-111756, 319844, 1342584, 3165803, 3266512]], ![![-302127, 928701, 3787774, 8916065, 9195282]], ![![-205215, 623122, 2553803, 6013193, 6202012]], ![![-129783, 385768, 1594558, 3756491, 3875002]], ![![-70138, 201692, 844972, 1992206, 2055515]]]
  g := ![![![135, -1264, 2922, -1633, -298], ![4438, -315, 304, 1243, -8904], ![-17190, 14166, -31547, 13241, 34170], ![3879, -21964, 51232, -29392, -7080], ![2876, 15452, -36616, 22866, -6321]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 2 2 8 [215, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [191, 310], [0, 1]]
 g := ![![[232, 14], [197, 135], [13, 75], [223], [274, 20], [92, 282], [94], [1]], ![[107, 297], [169, 176], [32, 236], [223], [51, 291], [151, 29], [94], [1]]]
 h' := ![![[191, 310], [252, 221], [4, 67], [5, 186], [180, 277], [124, 234], [202, 201], [96, 191], [0, 1]], ![[0, 1], [167, 90], [50, 244], [77, 125], [217, 34], [34, 77], [29, 110], [190, 120], [191, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216]]
 b := ![[], [260, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 2
  hpos := by decide
  P := [215, 120, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-404, -802, 645, -476, -404]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![296, -252, 645, -476, -404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1199, 2752, 878, 576, 168]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![1199, 2752, 878, 576, 168]] 
 ![![311, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![124, 0, 1, 0, 0], ![196, 0, 0, 1, 0], ![171, 0, 0, 0, 1]] where
  M :=![![![1199, 2752, 878, 576, 168], ![1224, 3301, 2104, 3316, 2952], ![1092, 4420, 5525, 11204, 11040], ![-366, 1904, 6514, 15153, 15576], ![-876, -1692, 148, 1364, 1697]]]
  hmulB := by decide  
  f := ![![![7345, 5400, -4326, 664, 11928]], ![![4048, 2957, -2320, 316, 6648]], ![![3056, 2300, -2011, 444, 4704]], ![![5030, 3720, -2974, 457, 8184]], ![![3609, 2612, -2034, 260, 5945]]]
  g := ![![![-2359, 2752, 878, 576, 168], ![-6416, 3301, 2104, 3316, 2952], ![-17832, 4420, 5525, 11204, 11040], ![-21790, 1904, 6514, 15153, 15576], ![-897, -1692, 148, 1364, 1697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -217, 13, 160, 202]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![-111, -217, 13, 160, 202]] 
 ![![311, 0, 0, 0, 0], ![280, 1, 0, 0, 0], ![283, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![127, 0, 0, 0, 1]] where
  M :=![![![-111, -217, 13, 160, 202], ![-126, -224, 69, 304, 354], ![-150, -207, 230, 696, 762], ![-36, 53, 309, 741, 768], ![73, 157, 27, -25, -51]]]
  hmulB := by decide  
  f := ![![![2001, -1567, -27, 250, 410]], ![![1800, -1406, -27, 226, 370]], ![![1821, -1430, -19, 224, 376]], ![![300, -251, 3, 37, 48]], ![![826, -630, -20, 105, 181]]]
  g := ![![![76, -217, 13, 160, 202], ![-53, -224, 69, 304, 354], ![-442, -207, 230, 696, 762], ![-757, 53, 309, 741, 768], ![-141, 157, 27, -25, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2

def I311N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 5, -3, 1, 0]] i)))

def SI311N3: IdealEqSpanCertificate' Table ![![-2, 5, -3, 1, 0]] 
 ![![311, 0, 0, 0, 0], ![307, 1, 0, 0, 0], ![295, 0, 1, 0, 0], ![281, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-2, 5, -3, 1, 0], ![3, -2, 3, -3, 6], ![-27, -21, 22, -9, -36], ![39, 39, -57, 28, 24], ![-27, -29, 45, -25, -11]]]
  hmulB := by decide  
  f := ![![![-5650, -11581, -969, 4387, 6426]], ![![-5597, -11473, -960, 4346, 6366]], ![![-5381, -11030, -923, 4178, 6120]], ![![-5107, -10468, -876, 3965, 5808]], ![![-787, -1613, -135, 611, 895]]]
  g := ![![![-3, 5, -3, 1, 0], ![1, -2, 3, -3, 6], ![13, -21, 22, -9, -36], ![-13, 39, -57, 28, 24], ![10, -29, 45, -25, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N3 : Nat.card (O ⧸ I311N3) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N3)

lemma isPrimeI311N3 : Ideal.IsPrime I311N3 := prime_ideal_of_norm_prime hp311.out _ NI311N3
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-1266, -2068, 2922, -1633, -298]] ![![1199, 2752, 878, 576, 168]]
  ![![384, -276, -36, 63, 142]] where
 M := ![![![384, -276, -36, 63, 142]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![384, -276, -36, 63, 142]] ![![-111, -217, 13, 160, 202]]
  ![![5650, 11581, 969, -4387, -6426]] where
 M := ![![![5650, 11581, 969, -4387, -6426]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N2 : IdealMulLeCertificate' Table 
  ![![5650, 11581, 969, -4387, -6426]] ![![-2, 5, -3, 1, 0]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2, I311N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
    exact isPrimeI311N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1 ⊙ MulI311N2)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15179, 145019, 433323, 997216, 1021932]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![-15179, 145019, 433323, 997216, 1021932]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![36, 209, 14, 265, 1]] where
  M :=![![![-15179, 145019, 433323, 997216, 1021932], ![-74148, 343996, 1216383, 2836362, 2917500], ![-243414, 898821, 3423772, 8024352, 8265672], ![-324906, 1056201, 4215375, 9909283, 10215798], ![-27279, 22153, 189555, 460487, 478993]]]
  hmulB := by decide  
  f := ![![![1111, -845, 21, 98, 324]], ![![-678, 454, -69, 12, -384]], ![![1188, 441, -722, 282, 1224]], ![![-1074, -1407, 1809, -917, -798]], ![![-1179, -962, 1451, -742, -839]]]
  g := ![![![-117587, -681913, -44325, -862028, 1021932], ![-335796, -1947008, -126609, -2461026, 2917500], ![-951462, -5516379, -358772, -6972456, 8265672], ![-1176018, -6818037, -443469, -8617499, 10215798], ![-55179, -319768, -20819, -404066, 478993]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 4 2 8 [141, 280, 118, 104, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 199, 214, 91], [40, 235, 98, 246], [25, 191, 1, 289], [0, 1]]
 g := ![![[292, 99, 88, 144], [303, 267, 228], [219, 6, 12], [152, 122, 293, 198], [19, 309, 126, 192], [37, 154, 188, 174], [1], []], ![[117, 38, 177, 305, 91, 145], [207, 143, 247], [56, 47, 295], [222, 52, 7, 3, 44, 252], [228, 0, 28, 11, 120, 193], [52, 186, 33, 172, 57, 211], [312, 206, 247], [132, 288, 143]], ![[247, 220, 212, 290, 110, 130], [272, 202, 210], [302, 282, 3], [56, 241, 105, 143, 228, 279], [186, 254, 116, 203, 147, 178], [3, 173, 148, 287, 258, 283], [157, 14, 286], [178, 154, 107]], ![[212, 255, 229, 166, 113, 72], [120, 42, 213], [44, 73, 162], [252, 237, 221, 158, 195, 213], [91, 275, 235, 89, 213, 72], [71, 66, 283, 0, 248, 194], [27, 37, 288], [224, 144, 263]]]
 h' := ![![[144, 199, 214, 91], [233, 92, 207, 301], [102, 271, 236, 139], [165, 285, 66, 166], [138, 113, 300, 220], [104, 14, 271, 275], [172, 33, 195, 209], [0, 0, 1], [0, 1]], ![[40, 235, 98, 246], [279, 311, 37, 289], [277, 67, 113, 160], [273, 182, 209, 236], [149, 117, 253, 211], [108, 154, 249, 3], [248, 311, 114, 260], [246, 89, 191, 153], [144, 199, 214, 91]], ![[25, 191, 1, 289], [98, 167, 4, 152], [138, 52, 235, 264], [195, 160, 79, 83], [238, 89, 12, 33], [35, 251, 160, 232], [302, 72, 212, 110], [290, 143, 130, 35], [40, 235, 98, 246]], ![[0, 1], [301, 56, 65, 197], [56, 236, 42, 63], [0, 312, 272, 141], [165, 307, 61, 162], [148, 207, 259, 116], [107, 210, 105, 47], [28, 81, 304, 125], [25, 191, 1, 289]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [294, 78, 64], []]
 b := ![[], [], [67, 186, 98, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 4
  hpos := by decide
  P := [141, 280, 118, 104, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20086570365, 27719457034, -45463602012, 54893837664, 2813086815]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-259375575, -1789826477, -271076094, -2206307247, 2813086815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 9597924961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1111, 845, -21, -98, -324]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-1111, 845, -21, -98, -324]] 
 ![![313, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-1111, 845, -21, -98, -324], ![678, -454, 69, -12, 384], ![-1188, -441, 722, -282, -1224], ![1074, 1407, -1809, 917, 798], ![-657, -1109, 1449, -775, -319]]]
  hmulB := by decide  
  f := ![![![15179, -145019, -433323, -997216, -1021932]], ![![14349, -135925, -406752, -936186, -959424]], ![![7664, -68663, -207526, -478048, -490032]], ![![1426, -7081, -24543, -57147, -58758]], ![![1639, -14897, -44907, -103423, -106009]]]
  g := ![![![-744, 845, -21, -98, -324], ![354, -454, 69, -12, 384], ![211, -441, 722, -282, -1224], ![-589, 1407, -1809, 917, 798], ![424, -1109, 1449, -775, -319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![-15179, 145019, 433323, 997216, 1021932]] ![![-1111, 845, -21, -98, -324]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1118, -359, 1357, -885, 30]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-1118, -359, 1357, -885, 30]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![214, 11, 4, 1, 0], ![295, 228, 47, 0, 1]] where
  M :=![![![-1118, -359, 1357, -885, 30], ![-2745, -2506, 1501, 29, -5400], ![16287, 15043, -18764, 8489, 16374], ![-10455, -11813, 22843, -14232, 3606], ![3669, 5499, -14527, 10271, -9695]]]
  hmulB := by decide  
  f := ![![![3794, 8949, 3357, 3127, 1860]], ![![3801, 10952, 8275, 14235, 13182]], ![![3159, 15235, 22028, 46073, 45864]], ![![2728, 6637, 2914, 3379, 2490]], ![![6724, 18447, 12344, 19995, 18031]]]
  g := ![![![566, 8, 11, -885, 30], ![4997, 3875, 805, 29, -5400], ![-20917, -12024, -2594, 8489, 16374], ![6219, -2137, -283, -14232, 3606], ![2100, 6634, 1262, 10271, -9695]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [209, 48, 242, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [293, 15, 70], [99, 301, 247], [0, 1]]
 g := ![![[35, 309, 230], [64, 169], [293, 32, 148], [17, 286, 302], [123, 299, 167], [306, 68, 157], [75, 1], []], ![[1, 67, 278, 148], [52, 286], [217, 160, 314, 24], [40, 70, 10, 234], [17, 101, 236, 264], [24, 220, 138, 212], [263, 256], [295, 145]], ![[125, 184, 220, 6], [42, 194], [229, 198, 301, 221], [144, 170, 119, 54], [66, 13, 239, 218], [199, 274], [132, 225], [118, 145]]]
 h' := ![![[293, 15, 70], [221, 252, 123], [261, 88, 13], [251, 223, 214], [287, 137, 122], [80, 140, 22], [175, 312, 188], [0, 0, 1], [0, 1]], ![[99, 301, 247], [62, 182, 139], [109, 48, 246], [243, 36, 140], [250, 213, 30], [232, 240, 255], [134, 111, 129], [102, 146, 301], [293, 15, 70]], ![[0, 1], [45, 200, 55], [274, 181, 58], [28, 58, 280], [100, 284, 165], [194, 254, 40], [167, 211], [38, 171, 15], [99, 301, 247]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 284], []]
 b := ![[], [122, 230, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [209, 48, 242, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32895, 40852, -28862, 85453, 71451]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-124076, -54227, -11763, 85453, 71451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3794, 8949, 3357, 3127, 1860]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![3794, 8949, 3357, 3127, 1860]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![43, 309, 1, 0, 0], ![172, 307, 0, 1, 0], ![159, 71, 0, 0, 1]] where
  M :=![![![3794, 8949, 3357, 3127, 1860], ![3801, 10952, 8275, 14235, 13182], ![3159, 15235, 22028, 46073, 45864], ![-1587, 7431, 26203, 61088, 62832], ![-2823, -5357, 717, 4939, 6023]]]
  hmulB := by decide  
  f := ![![![-1118, -359, 1357, -885, 30]], ![![-2745, -2506, 1501, 29, -5400]], ![![-2776, -2444, 1588, -65, -5208]], ![![-3298, -2659, 2262, -497, -5202]], ![![-1164, -724, 971, -405, -1225]]]
  g := ![![![-3073, -6689, 3357, 3127, 1860], ![-15446, -24770, 8275, 14235, 13182], ![-50981, -76316, 22028, 46073, 45864], ![-68220, -98752, 26203, 61088, 62832], ![-5807, -6848, 717, 4939, 6023]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [109, 263, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 316], [0, 1]]
 g := ![![[174, 281], [165], [311, 228], [213, 222], [8, 24], [255, 217], [63], [1]], ![[132, 36], [165], [260, 89], [155, 95], [36, 293], [244, 100], [63], [1]]]
 h' := ![![[54, 316], [167, 50], [20, 254], [241, 202], [79, 92], [101, 138], [259, 189], [208, 54], [0, 1]], ![[0, 1], [14, 267], [105, 63], [54, 115], [292, 225], [262, 179], [4, 128], [271, 263], [54, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [33, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [109, 263, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5526, 11022, -2148, 15447, 13608]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14898, -15879, -2148, 15447, 13608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-1118, -359, 1357, -885, 30]] ![![3794, 8949, 3357, 3127, 1860]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-322, -947, -71, 371, 546]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![-322, -947, -71, 371, 546]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![271, 245, 32, 285, 1]] where
  M :=![![![-322, -947, -71, 371, 546], ![-525, -918, -51, 425, 588], ![-489, -1065, -4, 585, 786], ![-39, -89, 87, 268, 282], ![273, 623, 53, -221, -319]]]
  hmulB := by decide  
  f := ![![![2, -1, -1, 1, 0]], ![![3, 4, -3, 1, 6]], ![![-15, -15, 20, -9, -12]], ![![3, 5, -15, 12, -12]], ![![5, 5, -14, 11, -7]]]
  g := ![![![-448, -407, -53, -469, 546], ![-483, -438, -57, -505, 588], ![-645, -585, -76, -675, 786], ![-231, -209, -27, -242, 282], ![262, 238, 31, 274, -319]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [131, 173, 109, 157, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [189, 89, 93, 209], [321, 23, 200, 306], [326, 218, 38, 147], [0, 1]]
 g := ![![[135, 128, 77, 324], [104, 317, 22, 120], [245, 134, 105], [109, 78, 273, 212], [246, 15, 289], [279, 244, 130], [174, 1], []], ![[164, 190, 29, 148, 125, 148], [93, 136, 167, 263, 222, 170], [183, 166, 80], [81, 279, 128, 190, 27, 41], [90, 187, 259], [220, 232, 110], [191, 119, 280, 300, 265, 162], [89, 219, 320]], ![[54, 141, 194, 307, 14, 7], [295, 31, 275, 60, 122, 301], [239, 96, 113], [231, 124, 284, 156, 42, 108], [313, 156, 258], [169, 218, 197], [263, 169, 149, 254, 97, 147], [143, 112, 294]], ![[129, 88, 288, 49, 73, 129], [138, 184, 180, 200, 43, 12], [4, 102, 225], [319, 261, 100, 304, 291, 286], [306, 325, 49], [195, 7, 196], [307, 48, 284, 192, 83, 18], [315, 55, 94]]]
 h' := ![![[189, 89, 93, 209], [278, 34, 10, 313], [142, 277, 318, 293], [285, 137, 160, 84], [282, 23, 8, 132], [231, 52, 28, 314], [45, 219, 59, 46], [0, 0, 1], [0, 1]], ![[321, 23, 200, 306], [244, 241, 249, 120], [8, 7, 55, 61], [255, 58, 164, 61], [206, 194, 49, 187], [61, 18, 304, 212], [49, 138, 198, 310], [230, 148, 238, 35], [189, 89, 93, 209]], ![[326, 218, 38, 147], [266, 233, 229, 195], [86, 65, 215, 261], [287, 214, 117, 171], [239, 328, 269, 123], [23, 211, 288, 143], [216, 145, 216, 292], [234, 180, 175, 309], [321, 23, 200, 306]], ![[0, 1], [224, 154, 174, 34], [171, 313, 74, 47], [258, 253, 221, 15], [256, 117, 5, 220], [195, 50, 42, 324], [65, 160, 189, 14], [135, 3, 248, 318], [326, 218, 38, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [213, 197, 206], []]
 b := ![[], [], [76, 210, 17, 326], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [131, 173, 109, 157, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76941873, -85932244, 157911236, -98162520, 11269942]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9459505, -8601414, -612468, -10000290, 11269942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, -1, 1, 0]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![2, -1, -1, 1, 0]] 
 ![![331, 0, 0, 0, 0], ![279, 1, 0, 0, 0], ![275, 0, 1, 0, 0], ![225, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![2, -1, -1, 1, 0], ![3, 4, -3, 1, 6], ![-15, -15, 20, -9, -12], ![3, 5, -15, 12, -12], ![3, 1, 7, -7, 17]]]
  hmulB := by decide  
  f := ![![![-322, -947, -71, 371, 546]], ![![-273, -801, -60, 314, 462]], ![![-269, -790, -59, 310, 456]], ![![-219, -644, -48, 253, 372]], ![![-77, -227, -17, 89, 131]]]
  g := ![![![1, -1, -1, 1, 0], ![-3, 4, -3, 1, 6], ![5, -15, 20, -9, -12], ![3, 5, -15, 12, -12], ![-6, 1, 7, -7, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![-322, -947, -71, 371, 546]] ![![2, -1, -1, 1, 0]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, -234, -602, -1368, -1392]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![73, -234, -602, -1368, -1392]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![0, 0, 0, 337, 0], ![6, 327, 29, 123, 1]] where
  M :=![![![73, -234, -602, -1368, -1392], ![72, -457, -1674, -3916, -4032], ![348, -1254, -4721, -11064, -11400], ![468, -1454, -5826, -13659, -14076], ![18, -30, -250, -642, -671]]]
  hmulB := by decide  
  f := ![![![1, -6, 2, 0, 0]], ![![0, 3, -6, 4, 0]], ![![12, 6, -5, 0, 24]], ![![-36, -34, 42, -19, -36]], ![![-12, -9, 9, -3, -11]]]
  g := ![![![25, 1350, 118, 504, -1392], ![72, 3911, 342, 1460, -4032], ![204, 11058, 967, 4128, -11400], ![252, 13654, 1194, 5097, -14076], ![12, 651, 57, 243, -671]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 4 2 8 [292, 140, 60, 44, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [215, 115, 316, 276], [261, 210, 5, 230], [154, 11, 16, 168], [0, 1]]
 g := ![![[192, 2, 218, 255], [25, 14, 253], [9, 206, 273], [297, 47, 193], [214, 154, 98, 255], [102, 246, 85], [293, 1], []], ![[299, 113, 72, 48, 134, 66], [302, 110, 181], [183, 30, 246], [335, 58, 310], [54, 63, 163, 183, 60, 10], [137, 116, 63], [161, 50, 82, 267, 99, 66], [36, 261, 14]], ![[144, 223, 126, 145, 201, 47], [63, 108, 8], [311, 131, 273], [91, 269, 85], [242, 97, 80, 252, 267, 25], [222, 254, 8], [235, 310, 332, 230], [109, 0, 328]], ![[42, 38, 326, 40, 5, 100], [134, 308, 98], [121, 285, 128], [266, 26, 9], [61, 188, 167, 152, 91, 117], [99, 186, 7], [244, 190, 302, 281, 271, 216], [70, 310, 253]]]
 h' := ![![[215, 115, 316, 276], [289, 320, 218, 170], [258, 31, 25, 169], [114, 336, 47, 173], [194, 265, 29, 246], [288, 41, 159, 167], [42, 139, 141, 191], [0, 0, 1], [0, 1]], ![[261, 210, 5, 230], [112, 194, 294, 286], [311, 82, 31, 65], [294, 46, 239, 120], [76, 203, 117, 240], [210, 302, 290, 254], [59, 138, 130, 317], [328, 213, 162, 286], [215, 115, 316, 276]], ![[154, 11, 16, 168], [137, 319, 214, 156], [196, 280, 190, 285], [78, 336, 151, 173], [135, 237, 149, 191], [225, 3, 203, 309], [285, 242, 221, 285], [234, 0, 336], [261, 210, 5, 230]], ![[0, 1], [7, 178, 285, 62], [69, 281, 91, 155], [333, 293, 237, 208], [256, 306, 42, 334], [169, 328, 22, 281], [134, 155, 182, 218], [243, 124, 175, 51], [154, 11, 16, 168]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [258, 155, 336], []]
 b := ![[], [], [233, 164, 291, 274], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 4
  hpos := by decide
  P := [292, 140, 60, 44, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-900308468, -697173872, 519078632, -19166152, -1528299408]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24538540, 1480880512, 133055672, 557749736, -1528299408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 12897917761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -6, 2, 0, 0]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![1, -6, 2, 0, 0]] 
 ![![337, 0, 0, 0, 0], ![276, 1, 0, 0, 0], ![323, 0, 1, 0, 0], ![109, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![1, -6, 2, 0, 0], ![0, 3, -6, 4, 0], ![12, 6, -5, 0, 24], ![-36, -34, 42, -19, -36], ![30, 30, -38, 18, 25]]]
  hmulB := by decide  
  f := ![![![73, -234, -602, -1368, -1392]], ![![60, -193, -498, -1132, -1152]], ![![71, -228, -591, -1344, -1368]], ![![25, -80, -212, -483, -492]], ![![15, -48, -124, -282, -287]]]
  g := ![![![3, -6, 2, 0, 0], ![2, 3, -6, 4, 0], ![-5, 6, -5, 0, 24], ![1, -34, 42, -19, -36], ![1, 30, -38, 18, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![73, -234, -602, -1368, -1392]] ![![1, -6, 2, 0, 0]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6936, -4267, 23747, 61827, 65458]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-6936, -4267, 23747, 61827, 65458]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![191, 310, 109, 1, 0], ![21, 141, 27, 0, 1]] where
  M :=![![![-6936, -4267, 23747, 61827, 65458], ![-10893, 5918, 68453, 167517, 174588], ![-21213, 36347, 194648, 464869, 481338], ![-19257, 59055, 241085, 567524, 585306], ![2581, 9843, 11561, 23095, 22641]]]
  hmulB := by decide  
  f := ![![![-360, -569, 677, -335, -304]], ![![-93, 224, -811, 653, -1098]], ![![5253, 4349, -4376, 1435, 7212]], ![![1344, 1229, -1692, 832, 1100]], ![![367, 413, -657, 372, 105]]]
  g := ![![![-38013, -81845, -24446, 61827, 65458], ![-102804, -220580, -66008, 167517, 174588], ![-285070, -610783, -182917, 464869, 481338], ![-347861, -744673, -223119, 567524, 585306], ![-14075, -29804, -8983, 23095, 22641]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [93, 122, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [285, 56, 258], [1, 290, 89], [0, 1]]
 g := ![![[232, 252, 113], [69, 116, 94], [44, 243], [344, 83, 172], [251, 301, 34], [243, 87], [129, 286, 1], []], ![[110, 92, 131, 23], [153, 78, 166, 188], [327, 90], [254, 141, 6, 309], [81, 140, 108, 191], [145, 229], [335, 207, 232, 237], [285, 287]], ![[297, 142, 52, 116], [40, 63, 183, 212], [71, 339], [257, 336, 24, 213], [273, 120, 325, 243], [78, 292], [234, 44, 305, 116], [107, 287]]]
 h' := ![![[285, 56, 258], [176, 98, 279], [185, 59, 326], [279, 95, 186], [253, 29, 296], [346, 188, 46], [148, 345, 174], [0, 0, 1], [0, 1]], ![[1, 290, 89], [267, 288, 12], [141, 106, 110], [4, 234, 28], [44, 153, 326], [123, 84, 78], [219, 212, 323], [241, 301, 290], [285, 56, 258]], ![[0, 1], [224, 308, 56], [300, 182, 258], [225, 18, 133], [71, 165, 72], [180, 75, 223], [29, 137, 197], [113, 46, 56], [1, 290, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 80], []]
 b := ![[], [276, 245, 344], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [93, 122, 61, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92366, -39536, 142624, 188163, 37374]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106099, -183400, -61603, 188163, 37374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![360, 569, -677, 335, 304]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![360, 569, -677, 335, 304]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![60, 129, 1, 0, 0], ![294, 38, 0, 1, 0], ![14, 124, 0, 0, 1]] where
  M :=![![![360, 569, -677, 335, 304], ![93, -224, 811, -653, 1098], ![-5253, -4349, 4376, -1435, -7212], ![8619, 8339, -11963, 6156, 5964], ![-6191, -6253, 9693, -5301, -2913]]]
  hmulB := by decide  
  f := ![![![6936, 4267, -23747, -61827, -65458]], ![![10893, -5918, -68453, -167517, -174588]], ![![5310, -1567, -30115, -74306, -77610]], ![![7125, 2797, -28311, -72364, -76266]], ![![4165, -1971, -25453, -62423, -65095]]]
  g := ![![![-178, 108, -677, 335, 304], ![369, -623, 811, -653, 1098], ![735, 1095, 4376, -1435, -7212], ![-3363, 1666, -11963, 6156, 5964], ![2915, -2000, 9693, -5301, -2913]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [263, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [324, 346], [0, 1]]
 g := ![![[103, 95], [127, 289], [116], [333, 4], [291, 39], [144], [278, 182], [1]], ![[0, 252], [73, 58], [116], [241, 343], [88, 308], [144], [256, 165], [1]]]
 h' := ![![[324, 346], [258, 147], [209, 330], [212, 84], [154, 345], [150, 115], [103, 335], [84, 324], [0, 1]], ![[0, 1], [0, 200], [253, 17], [15, 263], [200, 2], [281, 232], [32, 12], [266, 23], [324, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [148, 209]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [263, 23, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-106, -326, 162, 91, -630]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80, 154, 162, 91, -630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-6936, -4267, 23747, 61827, 65458]] ![![360, 569, -677, 335, 304]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![-347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, -54, -246, 136, 384]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![601, -54, -246, 136, 384]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![0, 0, 0, 349, 0], ![77, 158, 332, 313, 1]] where
  M :=![![![601, -54, -246, 136, 384], ![-744, -389, 826, -468, -336], ![-396, -314, -461, 584, -1800], ![3948, 3342, -3854, 1549, 4620], ![-3570, -3074, 3834, -1694, -3695]]]
  hmulB := by decide  
  f := ![![![-131, -274, -26, 96, 144]], ![![-144, -301, -34, 92, 144]], ![![-156, -334, -53, 64, 120]], ![![-12, -38, -34, -63, -60]], ![![-253, -548, -102, 67, 157]]]
  g := ![![![-83, -174, -366, -344, 384], ![72, 151, 322, 300, -336], ![396, 814, 1711, 1616, -1800], ![-1008, -2082, -4406, -4139, 4620], ![805, 1664, 3526, 3309, -3695]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 4 2 8 [65, 164, 119, 78, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [241, 295, 345, 130], [238, 193, 281, 113], [141, 209, 72, 106], [0, 1]]
 g := ![![[152, 17, 231, 106], [222, 253, 124], [53, 281, 28, 80], [187, 129, 63, 60], [303, 306, 49, 333], [337, 73, 326], [271, 1], []], ![[324, 134, 59, 84, 313, 202], [172, 74, 348], [23, 184, 312, 40, 201, 9], [112, 160, 168, 15, 77, 300], [98, 97, 325, 279, 87, 83], [254, 232, 151], [2, 49, 145, 58, 211, 151], [287, 329, 148]], ![[94, 116, 308, 45, 134, 328], [39, 347, 304], [121, 163, 76, 120, 286, 260], [263, 226, 6, 208, 219, 229], [320, 282, 300, 301, 216, 154], [6, 263, 145], [240, 330, 307, 115, 177, 166], [247, 52, 205]], ![[168, 171, 181, 328, 182, 94], [156, 3, 29], [45, 49, 112, 98, 273, 145], [256, 227, 313, 167, 253, 29], [166, 144, 317, 169, 214, 196], [13, 329, 153], [56, 274, 27, 292, 332, 157], [212, 188, 68]]]
 h' := ![![[241, 295, 345, 130], [159, 92, 43, 111], [45, 26, 205, 54], [60, 151, 83, 248], [198, 114, 223, 218], [85, 320, 208, 154], [184, 163, 44, 32], [0, 0, 1], [0, 1]], ![[238, 193, 281, 113], [250, 45, 83, 283], [175, 257, 77, 213], [290, 344, 321, 216], [348, 9, 205, 209], [150, 144, 68, 181], [64, 139, 187, 271], [338, 98, 281, 317], [241, 295, 345, 130]], ![[141, 209, 72, 106], [345, 192, 300, 94], [257, 257, 52, 181], [272, 241, 125, 207], [177, 181, 19, 6], [151, 150, 77, 55], [273, 213, 184, 205], [105, 167, 52, 225], [238, 193, 281, 113]], ![[0, 1], [123, 20, 272, 210], [96, 158, 15, 250], [279, 311, 169, 27], [192, 45, 251, 265], [201, 84, 345, 308], [136, 183, 283, 190], [168, 84, 15, 156], [141, 209, 72, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 66, 201], []]
 b := ![[], [], [169, 86, 31, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 4
  hpos := by decide
  P := [65, 164, 119, 78, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-116320199, -105876676, 135386944, -60248744, -111980678]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24373043, 50392752, 106913960, 100257030, -111980678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 14835483601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -274, -26, 96, 144]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-131, -274, -26, 96, 144]] 
 ![![349, 0, 0, 0, 0], ![219, 1, 0, 0, 0], ![201, 0, 1, 0, 0], ![217, 0, 0, 1, 0], ![305, 0, 0, 0, 1]] where
  M :=![![![-131, -274, -26, 96, 144], ![-144, -301, -34, 92, 144], ![-156, -334, -53, 64, 120], ![-12, -38, -34, -63, -60], ![90, 186, 14, -74, -107]]]
  hmulB := by decide  
  f := ![![![601, -54, -246, 136, 384]], ![![375, -35, -152, 84, 240]], ![![345, -32, -143, 80, 216]], ![![385, -24, -164, 89, 252]], ![![515, -56, -204, 114, 325]]]
  g := ![![![1, -274, -26, 96, 144], ![25, -301, -34, 92, 144], ![95, -334, -53, 64, 120], ![135, -38, -34, -63, -60], ![15, 186, 14, -74, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![601, -54, -246, 136, 384]] ![![-131, -274, -26, 96, 144]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, -9, 1, 5, 8]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![12, -9, 1, 5, 8]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![239, 167, 1, 0, 0], ![341, 119, 0, 1, 0], ![288, 36, 0, 0, 1]] where
  M :=![![![12, -9, 1, 5, 8], ![-9, 4, 5, 9, 6], ![9, 5, 4, 31, 36], ![-3, -3, 23, 28, 36], ![-1, 5, -5, 5, -3]]]
  hmulB := by decide  
  f := ![![![-36, -121, -11, 45, 70]], ![![-75, -122, -1, 43, 60]], ![![-60, -140, -8, 51, 76]], ![![-60, -158, -11, 58, 88]], ![![-37, -111, -9, 41, 63]]]
  g := ![![![-12, -3, 1, 5, 8], ![-17, -6, 5, 9, 6], ![-62, -16, 4, 31, 36], ![-72, -24, 23, 28, 36], ![1, 1, -5, 5, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [240, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 352], [0, 1]]
 g := ![![[192, 328], [311], [91], [317], [281], [259, 337], [269, 94], [1]], ![[0, 25], [311], [91], [317], [281], [122, 16], [59, 259], [1]]]
 h' := ![![[163, 352], [11, 210], [232, 283], [48, 47], [301, 252], [321, 276], [39, 168], [113, 163], [0, 1]], ![[0, 1], [0, 143], [118, 70], [296, 306], [76, 101], [125, 77], [242, 185], [207, 190], [163, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203]]
 b := ![[], [288, 278]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 2
  hpos := by decide
  P := [240, 190, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![745, 572, 323, 754, 1781]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2398, -587, 323, 754, 1781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-150, 740, 2570, 5985, 6154]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-150, 740, 2570, 5985, 6154]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![339, 113, 1, 0, 0], ![85, 316, 0, 1, 0], ![220, 297, 0, 0, 1]] where
  M :=![![![-150, 740, 2570, 5985, 6154], ![-507, 1913, 7232, 16941, 17448], ![-1521, 5204, 20375, 47839, 49302], ![-1941, 6276, 25100, 59012, 60840], ![-122, 216, 1136, 2710, 2805]]]
  hmulB := by decide  
  f := ![![![4860, -3212, -292, 595, 1544]], ![![-2847, 1721, 230, -343, -1062]], ![![3762, -2535, -209, 463, 1146]], ![![-1377, 764, 138, -165, -578]], ![![631, -551, 10, 83, 67]]]
  g := ![![![-7745, -11356, 2570, 5985, 6154], ![-21900, -32155, 7232, 16941, 17448], ![-61817, -90813, 20375, 47839, 49302], ![-76237, -112032, 25100, 59012, 60840], ![-3492, -5149, 1136, 2710, 2805]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [332, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [269, 352], [0, 1]]
 g := ![![[349, 84], [1], [155], [307], [68], [301, 18], [338, 349], [1]], ![[0, 269], [1], [155], [307], [68], [201, 335], [321, 4], [1]]]
 h' := ![![[269, 352], [82, 43], [240, 1], [91, 89], [46, 170], [320, 189], [38, 205], [21, 269], [0, 1]], ![[0, 1], [0, 310], [156, 352], [28, 264], [239, 183], [329, 164], [115, 148], [17, 84], [269, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [300]]
 b := ![[], [299, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [332, 84, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![678, 488, -50, 814, 462]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-434, -1100, -50, 814, 462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1

def I353N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![295, -193, -23, 40, 90]] i)))

def SI353N2: IdealEqSpanCertificate' Table ![![295, -193, -23, 40, 90]] 
 ![![353, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![319, 0, 1, 0, 0], ![322, 0, 0, 1, 0], ![110, 0, 0, 0, 1]] where
  M :=![![![295, -193, -23, 40, 90], ![-150, 122, -3, -16, -30], ![42, -111, 64, -24, -6], ![48, -35, -39, 39, -48], ![-39, 61, 11, -25, 55]]]
  hmulB := by decide  
  f := ![![![-9439, 29975, 120715, 283930, 292758]], ![![-2027, 6439, 25928, 60984, 62880]], ![![-8741, 27766, 111807, 262976, 271152]], ![![-8870, 28179, 113465, 266875, 275172]], ![![-2953, 9379, 37769, 88835, 91597]]]
  g := ![![![-3, -193, -23, 40, 90], ![1, 122, -3, -16, -30], ![-11, -111, 64, -24, -6], ![22, -35, -39, 39, -48], ![-17, 61, 11, -25, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N2 : Nat.card (O ⧸ I353N2) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N2)

lemma isPrimeI353N2 : Ideal.IsPrime I353N2 := prime_ideal_of_norm_prime hp353.out _ NI353N2
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![12, -9, 1, 5, 8]] ![![-150, 740, 2570, 5985, 6154]]
  ![![-9439, 29975, 120715, 283930, 292758]] where
 M := ![![![-9439, 29975, 120715, 283930, 292758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N1 : IdealMulLeCertificate' Table 
  ![![-9439, 29975, 120715, 283930, 292758]] ![![295, -193, -23, 40, 90]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1, I353N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
    exact isPrimeI353N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0 ⊙ MulI353N1)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1569, -3384, -16118, -38274, -39568]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![1569, -3384, -16118, -38274, -39568]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![43, 269, 159, 1, 0], ![213, 242, 154, 0, 1]] where
  M :=![![![1569, -3384, -16118, -38274, -39568], ![3882, -10667, -45540, -107490, -110940], ![10350, -31308, -128507, -302610, -312120], ![12324, -39480, -158454, -372617, -384180], ![344, -2244, -7244, -16776, -17223]]]
  hmulB := by decide  
  f := ![![![-501, 384, 14, -66, -104]], ![![114, -373, 204, -66, -84]], ![![54, 372, -493, 294, -144]], ![![51, -67, -65, 73, -136]], ![![-199, 134, -64, 42, -183]]]
  g := ![![![28065, 55342, 33880, -38274, -39568], ![78708, 155297, 95070, -107490, -110940], ![221460, 437058, 267557, -302610, -312120], ![272605, 538067, 329391, -372617, -384180], ![12229, 24174, 14798, -16776, -17223]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 3 2 8 [263, 266, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [178, 267, 336], [85, 91, 23], [0, 1]]
 g := ![![[129, 95, 302], [312, 33, 243], [61, 164, 94], [219, 138], [99, 292], [143, 170, 182], [334, 263, 1], []], ![[73, 267, 337, 314], [354, 86, 89, 142], [342, 26, 154, 199], [316, 72], [179, 198], [288, 195], [10, 207, 234, 166], [118, 170]], ![[339, 258, 226, 20], [60, 185, 29, 101], [159, 353, 200, 237], [30, 272], [86, 48], [166, 254, 14, 237], [164, 43, 283, 94], [72, 170]]]
 h' := ![![[178, 267, 336], [155, 212, 210], [112, 12, 31], [213, 256, 290], [27, 67, 280], [86, 26, 37], [113, 306, 30], [0, 0, 1], [0, 1]], ![[85, 91, 23], [276, 348, 233], [140, 223, 32], [213, 153, 39], [93, 321, 245], [44, 292, 256], [127, 173], [291, 286, 91], [178, 267, 336]], ![[0, 1], [65, 158, 275], [322, 124, 296], [24, 309, 30], [4, 330, 193], [148, 41, 66], [47, 239, 329], [136, 73, 267], [85, 91, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 166], []]
 b := ![[], [325, 322, 335], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 3
  hpos := by decide
  P := [263, 266, 96, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4136833, -3716600, 4129033, -2222724, -5127261]
  a := ![-16, -14, -1, -14, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3296788, 5111402, 3195377, -2222724, -5127261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 46268279 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![501, -384, -14, 66, 104]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![501, -384, -14, 66, 104]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![67, 41, 1, 0, 0], ![242, 91, 0, 1, 0], ![202, 165, 0, 0, 1]] where
  M :=![![![501, -384, -14, 66, 104], ![-114, 373, -204, 66, 84], ![-54, -372, 493, -294, 144], ![-600, -624, 426, -53, -1140], ![632, 708, -596, 168, 1041]]]
  hmulB := by decide  
  f := ![![![-1569, 3384, 16118, 38274, 39568]], ![![-3882, 10667, 45540, 107490, 110940]], ![![-765, 1937, 8567, 20262, 20924]], ![![-2076, 5095, 22850, 54085, 55864]], ![![-2668, 6813, 30020, 70986, 73301]]]
  g := ![![![-99, -64, -14, 66, 104], ![-54, -31, -204, 66, 84], ![25, -49, 493, -294, 144], ![596, 487, 426, -53, -1140], ![-586, -451, -596, 168, 1041]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [174, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [285, 358], [0, 1]]
 g := ![![[215, 306], [68, 245], [190, 23], [205], [15], [76, 182], [350, 91], [1]], ![[188, 53], [247, 114], [283, 336], [205], [15], [250, 177], [78, 268], [1]]]
 h' := ![![[285, 358], [15, 32], [327, 41], [304, 270], [153, 88], [59, 71], [130, 30], [185, 285], [0, 1]], ![[0, 1], [160, 327], [165, 318], [69, 89], [103, 271], [190, 288], [64, 329], [276, 74], [285, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216]]
 b := ![[], [47, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [174, 74, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1459, -1288, 1360, -440, -1959]
  a := ![-7, -5, 1, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1141, 853, 1360, -440, -1959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![1569, -3384, -16118, -38274, -39568]] ![![501, -384, -14, 66, 104]]
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


lemma PB402I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB402I7 : PrimesBelowBoundCertificateInterval O 307 359 402 where
  m := 9
  g := ![4, 2, 2, 2, 2, 2, 2, 3, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB402I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2, I311N3]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1]
    · exact ![I353N0, I353N1, I353N2]
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
    · exact ![96721, 311, 311, 311]
    · exact ![9597924961, 313]
    · exact ![31855013, 100489]
    · exact ![12003612721, 331]
    · exact ![12897917761, 337]
    · exact ![41781923, 120409]
    · exact ![14835483601, 349]
    · exact ![124609, 124609, 353]
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
      exact NI311N2
      exact NI311N3
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
      exact NI353N2
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I311N2, I311N3, I313N1, I331N1, I337N1, I349N1, I353N2]
  Il := ![[I311N1, I311N2, I311N3], [I313N1], [], [I331N1], [I337N1], [], [I349N1], [I353N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
