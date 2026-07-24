
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, 127, -446, 237, 680]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-131, 127, -446, 237, 680]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![10, 12, 17, 16, 1]] where
  M :=![![![-131, 127, -446, 237, 680], ![-372, -371, 342, -108, 44], ![4416, 230, 5193, -3212, -11344], ![-10062, 2530, -18538, 10575, 33730], ![5862, -900, 9542, -5550, -18171]]]
  hmulB := by decide  
  f := ![![![11, 37, 78, -57, -154]], ![![204, 49, 138, -128, -316]], ![![816, 282, 753, -660, -1664]], ![![1794, 588, 1610, -1423, -3578]], ![![1552, 522, 1411, -1242, -3127]]]
  g := ![![![-239, -277, -414, -367, 680], ![-28, -31, -14, -28, 44], ![4064, 4702, 6829, 6148, -11344], ![-11978, -13870, -20412, -18245, 33730], ![6468, 7488, 10981, 9834, -18171]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [16, 0, 0, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 6, 1, 24], [1, 22, 13, 12], [27, 0, 15, 22], [0, 1]]
 g := ![![[5, 18, 19, 23], [25, 24, 16], [13, 7, 6, 1], []], ![[4, 13, 19, 5, 6, 4], [0, 26, 13], [22, 24, 5, 23, 26, 20], [22, 21, 0, 10, 21, 20]], ![[15, 3, 21, 2, 21, 19], [16, 20, 13], [2, 11, 3, 18, 3, 19], [16, 16, 1, 16, 5, 17]], ![[3, 21, 6, 9], [1, 5, 25], [9, 3, 0, 11, 8, 1], [13, 15, 4, 14, 2, 5]]]
 h' := ![![[7, 6, 1, 24], [2, 11, 24, 9], [24, 4, 20, 4], [0, 0, 0, 1], [0, 1]], ![[1, 22, 13, 12], [28, 13, 28, 18], [12, 7, 9, 10], [20, 24, 4, 24], [7, 6, 1, 24]], ![[27, 0, 15, 22], [21, 27, 0, 2], [4, 18, 0, 10], [6, 13, 25, 2], [1, 22, 13, 12]], ![[0, 1], [18, 7, 6], [11, 0, 0, 5], [16, 21, 0, 2], [27, 0, 15, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 10, 7], []]
 b := ![[], [], [14, 10, 18, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [16, 0, 0, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188548910252, -63531503207, -163403505302, 147983399567, 367130740438]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133098493608, -154106909947, -220849175612, -197452015429, 367130740438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 37, 78, -57, -154]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![11, 37, 78, -57, -154]] 
 ![![29, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![11, 37, 78, -57, -154], ![204, 49, 138, -128, -316], ![816, 282, 753, -660, -1664], ![1794, 588, 1610, -1423, -3578], ![-126, -22, -78, 76, 185]]]
  hmulB := by decide  
  f := ![![![-131, 127, -446, 237, 680]], ![![-58, 31, -142, 78, 236]], ![![80, 78, -67, 20, -16]], ![![-356, 96, -670, 381, 1210]], ![![166, 4, 206, -126, -439]]]
  g := ![![![-9, 37, 78, -57, -154], ![10, 49, 138, -128, -316], ![20, 282, 753, -660, -1664], ![56, 588, 1610, -1423, -3578], ![-10, -22, -78, 76, 185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-131, 127, -446, 237, 680]] ![![11, 37, 78, -57, -154]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15481, -7194, -14663, 8719, 25902]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![15481, -7194, -14663, 8719, 25902]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![1, 9, 19, 1, 0], ![13, 23, 2, 0, 1]] where
  M :=![![![15481, -7194, -14663, 8719, 25902], ![-3060, 9282, 14883, -9338, -26716], ![15576, 3783, 2036, -1890, -4184], ![10446, 3963, 3503, -2615, -6638], ![10134, -2005, -5469, 3082, 9511]]]
  hmulB := by decide  
  f := ![![![205, 358, -525, 223, 372]], ![![-3564, -394, -3725, 2366, 8612]], ![![18168, -3409, 30928, -17858, -57912]], ![![9325, -1752, 15879, -9168, -29730]], ![![-827, -583, 219, 23, 727]]]
  g := ![![![-10644, -21981, -7488, 8719, 25902], ![11406, 22832, 7927, -9338, -26716], ![2318, 3775, 1494, -1890, -4184], ![3205, 5812, 2144, -2615, -6638], ![-3761, -8016, -2679, 3082, 9511]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [22, 0, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 27, 17], [14, 3, 14], [0, 1]]
 g := ![![[14, 1, 14], [18], [11, 4, 8], [1]], ![[18, 17, 21, 12], [4, 12, 21, 22], [28, 0, 10, 15], [2, 6, 27, 15]], ![[24, 23, 12, 25], [17, 22, 28, 9], [20, 21, 4, 25], [15, 10, 5, 16]]]
 h' := ![![[2, 27, 17], [7, 5, 18], [6, 24], [9, 0, 16], [0, 1]], ![[14, 3, 14], [9, 10, 15], [23, 28, 5], [26, 6, 17], [2, 27, 17]], ![[0, 1], [12, 16, 29], [1, 10, 26], [27, 25, 29], [14, 3, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 14], []]
 b := ![[], [25, 17, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [22, 0, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2117851474, -484544441, 4017989880, -2432247973, -7053546492]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3104716253, 5923782472, 2075412721, -2432247973, -7053546492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205, 358, -525, 223, 372]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![205, 358, -525, 223, 372]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![17, 24, 1, 0, 0], ![13, 0, 0, 1, 0], ![28, 25, 0, 0, 1]] where
  M :=![![![205, 358, -525, 223, 372], ![-3564, -394, -3725, 2366, 8612], ![18168, -3409, 30928, -17858, -57912], ![-24246, 13647, -61333, 33577, 100818], ![17334, -6847, 37433, -20888, -64551]]]
  hmulB := by decide  
  f := ![![![15481, -7194, -14663, 8719, 25902]], ![![-3060, 9282, 14883, -9338, -26716]], ![![6623, 3363, 3547, -2509, -6614]], ![![6829, -2889, -6036, 3572, 10648]], ![![11842, 923, -1418, 444, 2157]]]
  g := ![![![-135, 118, -525, 223, 372], ![-6843, -4074, -3725, 2366, 8612], ![43422, 22649, 30928, -17858, -57912], ![-72290, -33381, -61333, 33577, 100818], ![47095, 22856, 37433, -20888, -64551]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [25, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 30], [0, 1]]
 g := ![![[30, 5], [6, 1], [1, 28], [25, 1]], ![[0, 26], [0, 30], [19, 3], [19, 30]]]
 h' := ![![[25, 30], [5, 6], [6, 1], [26, 11], [0, 1]], ![[0, 1], [0, 25], [0, 30], [22, 20], [25, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [25, 6, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16597, -5779, -13701, 12677, 31745]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27011, -15180, -13701, 12677, 31745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![15481, -7194, -14663, 8719, 25902]] ![![205, 358, -525, 223, 372]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4711, -3479, -4185, 2842, 7702]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-4711, -3479, -4185, 2842, 7702]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![7, 33, 29, 1, 0], ![0, 26, 27, 0, 1]] where
  M :=![![![-4711, -3479, -4185, 2842, 7702], ![-9888, -6878, -8137, 5554, 15000], ![-19944, -14133, -16808, 11454, 30968], ![-15420, -10907, -12969, 8839, 23896], ![-6792, -4871, -5811, 3956, 10703]]]
  hmulB := by decide  
  f := ![![![-19, -9, -9, 10, 30]], ![![0, -18, 21, 2, -40]], ![![-552, -23, -748, 506, 1464]], ![![-445, -47, -561, 401, 1114]], ![![-408, -26, -545, 378, 1063]]]
  g := ![![![-665, -8041, -7961, 2842, 7702], ![-1318, -15680, -15519, 5554, 15000], ![-2706, -32359, -32030, 11454, 30968], ![-2089, -24970, -24716, 8839, 23896], ![-932, -11181, -11068, 3956, 10703]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [26, 35, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 16, 25], [21, 20, 12], [0, 1]]
 g := ![![[10, 3, 34], [36, 4], [29, 27, 25], [20, 1], []], ![[22, 32, 35, 33], [2, 21], [17, 21, 9, 27], [30, 30], [17, 33]], ![[26, 20, 31, 1], [20, 10], [8, 22, 36, 21], [26, 34], [30, 33]]]
 h' := ![![[36, 16, 25], [0, 17, 16], [23, 26, 2], [35, 14, 32], [0, 0, 1], [0, 1]], ![[21, 20, 12], [31, 7, 5], [3, 36, 24], [6, 27, 28], [3, 32, 20], [36, 16, 25]], ![[0, 1], [2, 13, 16], [2, 12, 11], [26, 33, 14], [31, 5, 16], [21, 20, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 11], []]
 b := ![[], [34, 22, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [26, 35, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1990778609, -628720377, -1796791614, 1585294662, 3976737016]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-353725439, -4225367747, -4193033412, 1585294662, 3976737016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 42, 50, -34, -92]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![59, 42, 50, -34, -92]] 
 ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![59, 42, 50, -34, -92], ![120, 85, 100, -68, -184], ![240, 172, 201, -136, -368], ![180, 130, 152, -101, -276], ![84, 60, 70, -48, -129]]]
  hmulB := by decide  
  f := ![![![-25, 22, 50, -30, -92]], ![![-2, 1, 0, 0, 0]], ![![-21, 18, 51, -30, -92]], ![![-3, 4, -2, 1, 0]], ![![-24, 20, 54, -32, -97]]]
  g := ![![![47, 42, 50, -34, -92], ![94, 85, 100, -68, -184], ![187, 172, 201, -136, -368], ![139, 130, 152, -101, -276], ![66, 60, 70, -48, -129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 97, 116, -79, -214]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![137, 97, 116, -79, -214]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![137, 97, 116, -79, -214], ![276, 197, 228, -156, -420], ![576, 396, 497, -336, -912], ![438, 318, 348, -241, -654], ![198, 132, 180, -120, -325]]]
  hmulB := by decide  
  f := ![![![-1057, -325, -908, 811, 2032]], ![![-530, -165, -460, 410, 1028]], ![![-1346, -422, -1175, 1046, 2624]], ![![-2271, -717, -1992, 1772, 4446]], ![![-171, -51, -144, 129, 323]]]
  g := ![![![8, 97, 116, -79, -214], ![14, 197, 228, -156, -420], ![38, 396, 497, -336, -912], ![21, 318, 348, -241, -654], ![15, 132, 180, -120, -325]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-4711, -3479, -4185, 2842, 7702]] ![![59, 42, 50, -34, -92]]
  ![![-541301, -381817, -453511, 309168, 835678]] where
 M := ![![![-541301, -381817, -453511, 309168, 835678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-541301, -381817, -453511, 309168, 835678]] ![![137, 97, 116, -79, -214]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-139882237, -98689582, -117227655, 79915079, 216012364]]]
 hmul := by decide  
 g := ![![![![-3780601, -2667286, -3168315, 2159867, 5838172]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617, 44, 415, -431, -1036]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![617, 44, 415, -431, -1036]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![2, 21, 26, 1, 0], ![37, 23, 17, 0, 1]] where
  M :=![![![617, 44, 415, -431, -1036], ![3084, 858, 2863, -2602, -6500], ![15672, 4651, 13948, -12538, -31384], ![35838, 11227, 31927, -28439, -71354], ![-2670, -1015, -2435, 2092, 5301]]]
  hmulB := by decide  
  f := ![![![427, -104, 779, -445, -1422]], ![![-1044, 674, -2831, 1538, 4564]], ![![-600, -2387, 4488, -2086, -4552]], ![![-632, -1139, 1696, -725, -1238]], ![![-559, -744, 919, -359, -413]]]
  g := ![![![971, 803, 713, -431, -1036], ![6068, 5000, 4415, -2602, -6500], ![29316, 24141, 21304, -12538, -31384], ![66654, 54868, 48399, -28439, -71354], ![-4951, -4070, -3584, 2092, 5301]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 19, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 35, 5], [21, 5, 36], [0, 1]]
 g := ![![[1, 37, 39], [17, 21], [29, 20], [14, 19, 1], []], ![[12, 40, 34, 21], [3, 37], [19, 16], [39, 22, 29, 2], [5, 25]], ![[16, 38, 24, 18], [27, 39], [23, 39], [26, 28, 2, 25], [15, 25]]]
 h' := ![![[39, 35, 5], [28, 32, 30], [29, 33, 29], [13, 24, 26], [0, 0, 1], [0, 1]], ![[21, 5, 36], [30, 32, 23], [35, 24, 23], [14, 31, 4], [35, 2, 5], [39, 35, 5]], ![[0, 1], [33, 18, 29], [13, 25, 30], [10, 27, 11], [1, 39, 35], [21, 5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 19], []]
 b := ![[], [16, 7, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 19, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1552498370, 436951722, 1419320924, -1179266178, -3203618510]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2986461356, 2411823590, 2110774542, -1179266178, -3203618510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 5, 11, -6, -18]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-11, 5, 11, -6, -18]] 
 ![![41, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-11, 5, 11, -6, -18], ![0, -6, -13, 10, 24], ![-72, -9, -72, 54, 152], ![-60, -47, 3, 27, 40], ![-24, 13, -39, 20, 67]]]
  hmulB := by decide  
  f := ![![![29093, 20527, 24383, -16622, -44930]], ![![24861, 17541, 20836, -14204, -38394]], ![![15714, 11087, 13170, -8978, -24268]], ![![27107, 19126, 22718, -15487, -41862]], ![![1008, 711, 845, -576, -1557]]]
  g := ![![![-4, 5, 11, -6, -18], ![2, -6, -13, 10, 24], ![-9, -9, -72, 54, 152], ![12, -47, 3, 27, 40], ![-11, 13, -39, 20, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, -63, -98, 75, 196]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-113, -63, -98, 75, 196]] 
 ![![41, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-113, -63, -98, 75, 196], ![-348, -165, -302, 244, 628], ![-1248, -510, -1097, 924, 2352], ![-2346, -838, -2078, 1805, 4558], ![42, -24, 42, -54, -125]]]
  hmulB := by decide  
  f := ![![![-163, 39, -374, 213, 670]], ![![-142, 29, -318, 182, 576]], ![![-112, 54, -325, 180, 544]], ![![-241, 19, -408, 240, 792]], ![![-51, 39, -204, 111, 325]]]
  g := ![![![-50, -63, -98, 75, 196], ![-206, -165, -302, 244, 628], ![-904, -510, -1097, 924, 2352], ![-1937, -838, -2078, 1805, 4558], ![111, -24, 42, -54, -125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![617, 44, 415, -431, -1036]] ![![-11, 5, 11, -6, -18]]
  ![![14057, 5875, 15446, -13209, -33622]] where
 M := ![![![14057, 5875, 15446, -13209, -33622]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![14057, 5875, 15446, -13209, -33622]] ![![-113, -63, -98, 75, 196]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![6666641, 2143644, 5940080, -5266778, -13230208]]]
 hmul := by decide  
 g := ![![![![162601, 52284, 144880, -128458, -322688]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 35, -15, 6, 38]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-7, 35, -15, 6, 38]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![10, 36, 3, 16, 1]] where
  M :=![![![-7, 35, -15, 6, 38], ![240, 4, 373, -218, -664], ![-120, 385, -810, 410, 1192], ![-348, -281, 317, -101, 120], ![120, 303, -437, 192, 399]]]
  hmulB := by decide  
  f := ![![![-157, -49, -137, 122, 306]], ![![-720, -232, -643, 570, 1432]], ![![-3336, -1071, -2970, 2634, 6616]], ![![-7356, -2363, -6551, 5809, 14592]], ![![-3598, -1156, -3205, 2842, 7139]]]
  g := ![![![-9, -31, -3, -14, 38], ![160, 556, 55, 242, -664], ![-280, -989, -102, -434, 1192], ![-36, -107, -1, -47, 120], ![-90, -327, -38, -144, 399]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [20, 36, 40, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 37, 24, 15], [19, 42], [42, 6, 19, 28], [0, 1]]
 g := ![![[42, 22, 16, 16], [14, 12, 36, 35], [20, 18, 10], [38, 1], []], ![[28, 13, 20, 6], [39, 26, 14, 32, 19, 25], [34, 11, 14], [6, 18, 41, 28, 13, 13], [0, 25, 10]], ![[9, 16, 25, 27], [33, 17, 10, 8], [16, 32, 10], [14, 42], []], ![[16, 39, 18, 37], [19, 3, 31, 36, 29, 18], [8, 16, 14], [3, 29, 18, 42, 1, 30], [0, 25, 10]]]
 h' := ![![[20, 37, 24, 15], [21, 22, 31, 39], [11, 3, 35, 11], [14, 31, 35, 28], [0, 0, 1], [0, 1]], ![[19, 42], [1, 20, 40], [29, 19, 2, 39], [35, 8, 11, 33], [13, 34, 25, 27], [20, 37, 24, 15]], ![[42, 6, 19, 28], [18, 36, 18, 4], [2, 41, 17, 32], [8, 6, 40, 15], [17, 5, 1], [19, 42]], ![[0, 1], [29, 8, 40], [35, 23, 32, 4], [25, 41, 0, 10], [1, 4, 16, 16], [42, 6, 19, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3], []]
 b := ![[], [], [15, 14, 11, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [20, 36, 40, 5, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119509165996, 70326597296, -309057861824, 168778992592, 504849444688]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-120186130532, -421029149104, -42409446416, -183925863312, 504849444688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, -49, -137, 122, 306]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-157, -49, -137, 122, 306]] 
 ![![43, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-157, -49, -137, 122, 306], ![-720, -232, -643, 570, 1432], ![-3336, -1071, -2970, 2634, 6616], ![-7356, -2363, -6551, 5809, 14592], ![480, 155, 429, -380, -955]]]
  hmulB := by decide  
  f := ![![![-7, 35, -15, 6, 38]], ![![2, 18, 1, -2, 4]], ![![-8, 35, -30, 14, 56]], ![![-12, 13, -1, 1, 24]], ![![1, 16, -14, 6, 19]]]
  g := ![![![-23, -49, -137, 122, 306], ![-104, -232, -643, 570, 1432], ![-482, -1071, -2970, 2634, 6616], ![-1062, -2363, -6551, 5809, 14592], ![69, 155, 429, -380, -955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-7, 35, -15, 6, 38]] ![![-157, -49, -137, 122, 306]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [17, 24, 33, 21, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 15, 3, 34, 7], [41, 28, 14, 21, 9], [30, 10, 16, 31, 29], [27, 40, 14, 8, 2], [0, 1]]
 g := ![![[21, 31, 16, 17, 16], [18, 34, 35, 13, 27], [38, 16, 3, 15, 12], [1], []], ![[26, 15, 33, 44, 19, 27, 14, 7], [35, 4, 28, 34, 36, 45, 28, 32], [38, 4, 29, 28, 42, 13, 7, 42], [5, 4, 5, 12, 2, 24, 25, 32], [7, 2, 5, 2]], ![[24, 29, 38, 43, 15, 37, 8, 36], [6, 7, 33, 16, 20, 21, 31, 36], [4, 23, 6, 3, 42, 1, 16, 8], [17, 21, 18, 32, 26, 35, 24, 2], [45, 10, 32, 34]], ![[6, 33, 41, 8, 36, 42, 25, 38], [5, 27, 12, 22, 37, 24, 14, 40], [32, 24, 29, 35, 21, 27, 37, 39], [24, 17, 3, 30, 16, 12, 2, 11], [22, 1, 38, 42]], ![[34, 7, 39, 4, 21, 11, 12, 28], [34, 13, 25, 25, 42, 16, 45, 3], [43, 33, 5, 13, 41, 41, 41, 14], [25, 40, 14, 26, 2, 25, 36, 2], [11, 21, 30, 4]]]
 h' := ![![[19, 15, 3, 34, 7], [23, 27, 15, 38, 43], [12, 45, 20, 45, 11], [30, 23, 14, 26, 23], [0, 0, 1], [0, 1]], ![[41, 28, 14, 21, 9], [26, 26, 11, 24, 1], [12, 7, 29, 31, 21], [0, 17, 19, 12, 37], [7, 39, 22, 28, 26], [19, 15, 3, 34, 7]], ![[30, 10, 16, 31, 29], [31, 17, 29, 46, 45], [39, 43, 28, 31, 45], [15, 19, 40, 3, 36], [23, 12, 39, 26, 29], [41, 28, 14, 21, 9]], ![[27, 40, 14, 8, 2], [44, 29, 2, 16, 27], [3, 41, 10, 17, 12], [1, 35, 1, 28, 15], [9, 8, 40, 12, 40], [30, 10, 16, 31, 29]], ![[0, 1], [2, 42, 37, 17, 25], [21, 5, 7, 17, 5], [0, 0, 20, 25, 30], [25, 35, 39, 28, 46], [27, 40, 14, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 28, 24, 46], [], [], []]
 b := ![[], [35, 34, 28, 30, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [17, 24, 33, 21, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6517393247586752, -2091739383179392, -5808955854575688, 5148419793691160, 12934930699721868]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-138667941438016, -44505093259136, -123594805416504, 109540846674280, 275211291483444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [18, 28, 52, 35, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 40, 39, 13, 45], [45, 52, 22, 0, 27], [46, 40, 1, 48, 31], [22, 26, 44, 45, 3], [0, 1]]
 g := ![![[36, 3, 45, 32, 38], [34, 12, 27, 17], [3, 44, 6, 8, 47], [48, 1], []], ![[37, 17, 44, 4, 9, 18, 3, 14], [40, 4, 9, 25], [52, 13, 18, 35, 1, 18, 46, 51], [21, 42, 22, 46], [22, 14, 51, 33, 12, 47, 21, 18]], ![[4, 20, 36, 2, 37, 49, 49, 45], [48, 20, 8, 46], [30, 5, 13, 30, 29, 12, 49, 27], [13, 25, 36, 36], [12, 31, 8, 0, 51, 2, 6, 20]], ![[6, 10, 31, 36, 44, 6, 25, 34], [20, 45, 25, 38], [32, 37, 50, 20, 49, 43, 2, 33], [44, 37, 23, 13], [15, 13, 39, 38, 40, 12, 29, 5]], ![[9, 26, 6, 44, 7, 51], [12, 20, 1, 1], [28, 48, 6, 0, 16, 10, 20, 35], [29, 14, 18, 13], [41, 13, 48, 25, 27, 30, 20, 27]]]
 h' := ![![[41, 40, 39, 13, 45], [25, 19, 39, 49, 12], [52, 16, 6, 38, 21], [37, 16, 20, 17, 43], [0, 0, 0, 1], [0, 1]], ![[45, 52, 22, 0, 27], [22, 27, 25, 29, 41], [0, 43, 50, 29, 48], [9, 19, 27, 19, 26], [49, 35, 42, 45, 24], [41, 40, 39, 13, 45]], ![[46, 40, 1, 48, 31], [48, 14, 32, 41, 39], [45, 45, 14, 16, 24], [15, 48, 7, 28, 52], [14, 27, 20, 18, 6], [45, 52, 22, 0, 27]], ![[22, 26, 44, 45, 3], [28, 42, 6, 19, 14], [32, 32, 37, 20, 12], [2, 51, 49, 10, 48], [23, 32, 52, 43, 38], [46, 40, 1, 48, 31]], ![[0, 1], [32, 4, 4, 21], [6, 23, 52, 3, 1], [9, 25, 3, 32, 43], [52, 12, 45, 52, 38], [22, 26, 44, 45, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 50, 46, 50], [], [], []]
 b := ![[], [42, 10, 12, 19, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [18, 28, 52, 35, 5, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![514821711547, -100337166770, 884670686803, -510077769368, -1650715134528]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9713617199, -1893154090, 16691899751, -9624108856, -31145568576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [18, 43, 5, 49, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 6, 19, 47, 2], [46, 10, 41, 0, 2], [6, 1, 35, 36, 2], [25, 41, 23, 35, 53], [0, 1]]
 g := ![![[31, 0, 6, 8, 9], [53, 56, 30, 48, 19], [53, 54, 10, 15], [32, 50, 1], []], ![[32, 36, 41, 1, 31, 43, 19, 33], [34, 4, 25, 31, 47, 7, 28, 56], [2, 49, 6, 21], [36, 23, 58, 5, 8, 33, 7, 6], [10, 57, 17, 45, 56, 48, 20, 8]], ![[32, 51, 54, 3, 27, 45, 49, 24], [11, 56, 50, 18, 26, 54, 31, 13], [34, 39, 25, 22], [4, 51, 30, 6, 12, 37, 9, 30], [56, 20, 27, 53, 3, 40, 46, 8]], ![[30, 25, 41, 10, 1, 42, 42, 31], [30, 43, 17, 49, 30, 46, 0, 32], [15, 6, 18, 12], [2, 46, 31, 53, 51, 47, 48, 54], [38, 58, 11, 16, 23, 21, 6, 8]], ![[11, 28, 23, 29, 32, 34, 53, 9], [54, 33, 24, 0, 35, 55, 27, 26], [47, 53, 35, 17], [18, 35, 48, 21, 35, 33, 48, 1], [20, 15, 48, 57, 32, 36, 1, 20]]]
 h' := ![![[32, 6, 19, 47, 2], [49, 39, 16, 54, 56], [9, 45, 52, 28, 45], [14, 25, 32, 27, 30], [0, 0, 0, 1], [0, 1]], ![[46, 10, 41, 0, 2], [1, 28, 58, 57, 39], [27, 22, 15, 29, 38], [57, 18, 52, 39, 32], [20, 43, 17, 34, 48], [32, 6, 19, 47, 2]], ![[6, 1, 35, 36, 2], [39, 37, 35, 58, 37], [56, 41, 51, 16, 6], [14, 5, 5, 4, 50], [40, 1, 39, 51, 30], [46, 10, 41, 0, 2]], ![[25, 41, 23, 35, 53], [35, 12, 26, 51, 24], [26, 6, 47, 41, 4], [1, 55, 49, 32, 37], [4, 26, 31, 53, 33], [6, 1, 35, 36, 2]], ![[0, 1], [29, 2, 42, 16, 21], [40, 4, 12, 4, 25], [58, 15, 39, 16, 28], [43, 48, 31, 38, 7], [25, 41, 23, 35, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 31, 32, 46], [], [], []]
 b := ![[], [34, 29, 11, 52, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [18, 43, 5, 49, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367962045293733, -116852803379733, -329580592431021, 290726049155325, 733094936490934]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6236644835487, -1980555989487, -5586111736119, 4927560155175, 12425337906626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 15, 28, -17, -50]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-19, 15, 28, -17, -50]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![33, 50, 1, 0, 0], ![29, 48, 0, 1, 0], ![9, 37, 0, 0, 1]] where
  M :=![![![-19, 15, 28, -17, -50], ![12, -7, -20, 12, 36], ![0, 4, 29, -16, -48], ![-6, 10, -12, 7, 14], ![-6, 4, 28, -16, -45]]]
  hmulB := by decide  
  f := ![![![11, 9, 12, -7, -20]], ![![12, 17, 4, 0, -4]], ![![15, 19, 9, -3, -12]], ![![13, 17, 8, -2, -10]], ![![9, 12, 4, -1, -5]]]
  g := ![![![0, 21, 28, -17, -50], ![0, -15, -20, 12, 36], ![-1, 18, 29, -16, -48], ![1, -4, -12, 7, 14], ![-1, 17, 28, -16, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 60], [0, 1]]
 g := ![![[5, 46], [47], [5, 3], [48, 14], [28, 1]], ![[12, 15], [47], [28, 58], [13, 47], [56, 60]]]
 h' := ![![[28, 60], [59, 31], [28, 13], [37, 8], [47, 21], [0, 1]], ![[0, 1], [12, 30], [26, 48], [17, 53], [25, 40], [28, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [3, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 33, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-152233, -81527, -89841, 116858, 226496]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42866, -157033, -89841, 116858, 226496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1415, -1084, -1195, 779, 2136]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1415, -1084, -1195, 779, 2136]] 
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-1415, -1084, -1195, 779, 2136], ![-2412, -2032, -1963, 1178, 3316], ![-2616, -3415, -1986, 610, 2264], ![3810, -763, 3661, -4135, -9822], ![-2874, -1809, -2449, 1776, 4713]]]
  hmulB := by decide  
  f := ![![![-9641, 3192, -19467, 10961, 34318]], ![![-666, 40, -947, 564, 1904]], ![![-3101, 2115, -8661, 4691, 13854]], ![![-11938, 2219, -20281, 11715, 38006]], ![![-355, 1267, -3252, 1635, 4239]]]
  g := ![![![-584, -1084, -1195, 779, 2136], ![-809, -2032, -1963, 1178, 3316], ![36, -3415, -1986, 610, 2264], ![4357, -763, 3661, -4135, -9822], ![-1460, -1809, -2449, 1776, 4713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -13, 7, 20]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-1, 2, -13, 7, 20]] 
 ![![61, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-1, 2, -13, 7, 20], ![-12, -8, 7, -2, 4], ![120, 3, 146, -90, -312], ![-246, 71, -473, 267, 850], ![150, -27, 249, -144, -469]]]
  hmulB := by decide  
  f := ![![![10865, 7654, 9091, -6199, -16754]], ![![5706, 4020, 4775, -3256, -8800]], ![![3411, 2403, 2855, -1947, -5262]], ![![1286, 905, 1077, -735, -1986]], ![![8802, 6201, 7365, -5022, -13573]]]
  g := ![![![-14, 2, -13, 7, 20], ![-1, -8, 7, -2, 4], ![216, 3, 146, -90, -312], ![-609, 71, -473, 267, 850], ![333, -27, 249, -144, -469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2

def I61N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-559, 388, 726, -440, -1290]] i)))

def SI61N3: IdealEqSpanCertificate' Table ![![-559, 388, 726, -440, -1290]] 
 ![![61, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-559, 388, 726, -440, -1290], ![360, -243, -452, 272, 800], ![-192, 164, 317, -200, -576], ![-36, 96, 200, -139, -384], ![-288, 194, 362, -218, -641]]]
  hmulB := by decide  
  f := ![![![-67, -72, 14, 4, 30]], ![![-36, -43, 12, 0, 8]], ![![-82, -52, -39, 32, 116]], ![![28, -32, 96, -51, -152]], ![![-43, -6, -56, 34, 109]]]
  g := ![![![-453, 388, 726, -440, -1290], ![284, -243, -452, 272, 800], ![-190, 164, 317, -200, -576], ![-108, 96, 200, -139, -384], ![-227, 194, 362, -218, -641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N3 : Nat.card (O ⧸ I61N3) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N3)

lemma isPrimeI61N3 : Ideal.IsPrime I61N3 := prime_ideal_of_norm_prime hp61.out _ NI61N3
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-19, 15, 28, -17, -50]] ![![-1415, -1084, -1195, 779, 2136]]
  ![![-3613, -2083, -2135, 1444, 3872]] where
 M := ![![![-3613, -2083, -2135, 1444, 3872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-3613, -2083, -2135, 1444, 3872]] ![![-1, 2, -13, 7, 20]]
  ![![-2015, 1013, 1794, -995, -3040]] where
 M := ![![![-2015, 1013, 1794, -995, -3040]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N2 : IdealMulLeCertificate' Table 
  ![![-2015, 1013, 1794, -995, -3040]] ![![-559, 388, 726, -440, -1290]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![2057957, -1419043, -2651548, 1604361, 4707126]]]
 hmul := by decide  
 g := ![![![![33737, -23263, -43468, 26301, 77166]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2, I61N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
    exact isPrimeI61N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1 ⊙ MulI61N2)


lemma PB696I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB696I1 : PrimesBelowBoundCertificateInterval O 23 61 696 where
  m := 9
  g := ![2, 2, 3, 3, 2, 1, 1, 1, 4]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB696I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2, I61N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![68921, 41, 41]
    · exact ![3418801, 43]
    · exact ![229345007]
    · exact ![418195493]
    · exact ![714924299]
    · exact ![3721, 61, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
      exact NI61N3
  β := ![I29N1, I37N1, I37N2, I41N1, I41N2, I43N1, I61N1, I61N2, I61N3]
  Il := ![[I29N1], [], [I37N1, I37N2], [I41N1, I41N2], [I43N1], [], [], [], [I61N1, I61N2, I61N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
