
import IdealArithmetic.Examples.NF5_1_121500000_1.RI5_1_121500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![490, -2697, 2660, -848, 2116]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![490, -2697, 2660, -848, 2116]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![490, -2697, 2660, -848, 2116], ![12696, -12510, -1429, -1456, -11436], ![-68616, 89863, -25402, 15646, 25572], ![70368, -122433, 66255, -26777, 14298], ![-11566, 49951, -51141, 14954, -43431]]]
  hmulB := by decide  
  f := ![![![1119093, -785528, 51593, 245478, 372556]], ![![1117668, -595864, -83747, 47254, 177600]], ![![1065600, -162025, -371010, -380932, -249276]], ![![-1306662, 1327227, -354243, -716759, -857682]], ![![-568229, 67053, 211712, 223426, 152869]]]
  g := ![![![245, -2697, 2660, -848, 2116], ![6348, -12510, -1429, -1456, -11436], ![-34308, 89863, -25402, 15646, 25572], ![35184, -122433, 66255, -26777, 14298], ![-5783, 49951, -51141, 14954, -43431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -14, -4, -1, 3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![31, -14, -4, -1, 3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![31, -14, -4, -1, 3], ![18, 5, -12, -17, -15], ![-90, 94, -27, -45, -57], ![-180, 116, 2, -29, -42], ![60, -60, 13, 25, 25]]]
  hmulB := by decide  
  f := ![![![170564, -46154, 16905, 29776, 40407]], ![![206503, -55879, 20467, 36050, 48921]], ![![257587, -69702, 25530, 44968, 61023]], ![![61848, -16736, 6130, 10797, 14652]], ![![20089, -5436, 1991, 3507, 4759]]]
  g := ![![![23, -14, -4, -1, 3], ![20, 5, -12, -17, -15], ![-50, 94, -27, -45, -57], ![-128, 116, 2, -29, -42], ![41, -60, 13, 25, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![209, -643, 230, -189, -193]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![209, -643, 230, -189, -193]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![209, -643, 230, -189, -193], ![-1158, 1601, -1025, 279, -555], ![-3330, 1981, 1325, -103, 3339], ![10596, -13541, 3121, -2308, -5040], ![-9590, 13955, -5092, 2691, 2268]]]
  hmulB := by decide  
  f := ![![![-49218, 54511, -16583, -31738, -36964]], ![![-135501, 107860, -15387, -43095, -58250]], ![![-263217, 160418, 5319, -32202, -62534]], ![![-101319, 20470, 31645, 30907, 18481]], ![![108959, -46436, -16520, -7618, 5301]]]
  g := ![![![502, -643, 230, -189, -193], ![-729, 1601, -1025, 279, -555], ![-4936, 1981, 1325, -103, 3339], ![14182, -13541, 3121, -2308, -5040], ![-11706, 13955, -5092, 2691, 2268]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![490, -2697, 2660, -848, 2116]] ![![31, -14, -4, -1, 3]]
  ![![6844, 4367, -15604, 3151, -21179]] where
 M := ![![![6844, 4367, -15604, 3151, -21179]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![6844, 4367, -15604, 3151, -21179]] ![![31, -14, -4, -1, 3]]
  ![![-142790, 95499, 72503, 243, 182638]] where
 M := ![![![-142790, 95499, 72503, 243, 182638]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-142790, 95499, 72503, 243, 182638]] ![![209, -643, 230, -189, -193]]
  ![![-2130789534, 2933759139, -963895993, 537081736, 629642306]] where
 M := ![![![-2130789534, 2933759139, -963895993, 537081736, 629642306]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-2130789534, 2933759139, -963895993, 537081736, 629642306]] ![![209, -643, 230, -189, -193]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-980206078762, 5671602682822, -6304253425116, 1775302107744, -5714305862142]]]
 hmul := by decide  
 g := ![![![![-490103039381, 2835801341411, -3152126712558, 887651053872, -2857152931071]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![346579, -93782, 34350, 60504, 82106]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![346579, -93782, 34350, 60504, 82106]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![346579, -93782, 34350, 60504, 82106], ![492636, -133309, 48828, 86000, 116706], ![700236, -189478, 69397, 122244, 165882], ![251328, -67994, 24910, 43881, 59556], ![-264920, 71666, -26252, -46256, -62773]]]
  hmulB := by decide  
  f := ![![![2353, -3478, 1418, 2432, 2666]], ![![5332, -4153, 540, 1600, 2198]], ![![13188, -7914, -355, 1484, 3006]], ![![6352, -1286, -1982, -1935, -1156]], ![![-5850, 2090, 1176, 832, 131]]]
  g := ![![![60789, -93782, 34350, 60504, 82106], ![86408, -133309, 48828, 86000, 116706], ![122824, -189478, 69397, 122244, 165882], ![44072, -67994, 24910, 43881, 59556], ![-46458, 71666, -26252, -46256, -62773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-699, 713, 22, 88, 553]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-699, 713, 22, 88, 553]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-699, 713, 22, 88, 553], ![3318, -4460, 1354, -798, -1131], ![-6786, 11791, -6389, 2576, -1395], ![-5844, 1813, 5809, -731, 10386], ![13886, -14373, -154, -1822, -10696]]]
  hmulB := by decide  
  f := ![![![-103845, 28067, -10306, -18136, -24603]], ![![-83821, 22667, -8326, -14650, -19870]], ![![-139244, 37693, -13833, -24348, -33023]], ![![-25260, 6901, -2503, -4425, -6006]], ![![-42736, 11521, -4232, -7446, -10106]]]
  g := ![![![-854, 713, 22, 88, 553], ![2444, -4460, 1354, -798, -1131], ![-1003, 11791, -6389, 2576, -1395], ![-13349, 1813, 5809, -731, 10386], ![16653, -14373, -154, -1822, -10696]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![346579, -93782, 34350, 60504, 82106]] ![![346579, -93782, 34350, 60504, 82106]]
  ![![91424548281, -24739156820, 9061296032, 15960326104, 21658676268]] where
 M := ![![![91424548281, -24739156820, 9061296032, 15960326104, 21658676268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![91424548281, -24739156820, 9061296032, 15960326104, 21658676268]] ![![-699, 713, 22, 88, 553]]
  ![![-3544659, 1081453, -427682, -572800, -848211]] where
 M := ![![![-3544659, 1081453, -427682, -572800, -848211]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-3544659, 1081453, -427682, -572800, -848211]] ![![-699, 713, 22, 88, 553]]
  ![![537413001, -1240570406, 921994456, -312481076, 536660676]] where
 M := ![![![537413001, -1240570406, 921994456, -312481076, 536660676]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![537413001, -1240570406, 921994456, -312481076, 536660676]] ![![-699, 713, 22, 88, 553]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-1470309118143, 8507404024233, -9456380137674, 2662953161616, -8571458793213]]]
 hmul := by decide  
 g := ![![![![-490103039381, 2835801341411, -3152126712558, 887651053872, -2857152931071]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34435, 37650, -2340, 5228, 23736]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-34435, 37650, -2340, 5228, 23736]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-34435, 37650, -2340, 5228, 23736], ![142416, -197699, 66614, -36468, -39840], ![-239040, 451442, -274007, 103504, -99288], ![-369072, 241586, 194522, -1229, 479364], ![680004, -751638, 57258, -106120, -457405]]]
  hmulB := by decide  
  f := ![![![-9239, -60338, 47512, 68100, 65832]], ![![73455, -107093, 43226, 74392, 81720]], ![![251477, -180364, 14365, 59212, 87696]], ![![180394, -97654, -12442, 9195, 30204]], ![![-150952, 46270, 35854, 29520, 11291]]]
  g := ![![![-50089, 37650, -2340, 5228, 23736], ![180239, -197699, 66614, -36468, -39840], ![-225843, 451442, -274007, 103504, -99288], ![-640670, 241586, 194522, -1229, 479364], ![983904, -751638, 57258, -106120, -457405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-34435, 37650, -2340, 5228, 23736]] ![![-34435, 37650, -2340, 5228, 23736]]
  ![![21318151753, -26374087340, 5605808284, -4320535272, -10435841328]] where
 M := ![![![21318151753, -26374087340, 5605808284, -4320535272, -10435841328]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![21318151753, -26374087340, 5605808284, -4320535272, -10435841328]] ![![-34435, 37650, -2340, 5228, 23736]]
  ![![-11332020242933083, 15347650479750510, -4780773204581376, 2766246514683588, 3702458729239848]] where
 M := ![![![-11332020242933083, 15347650479750510, -4780773204581376, 2766246514683588, 3702458729239848]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-11332020242933083, 15347650479750510, -4780773204581376, 2766246514683588, 3702458729239848]] ![![-34435, 37650, -2340, 5228, 23736]]
  ![![5215507746663393873361, -7733729775197283776088, 3108941826342389102712, -1510075706606065297520, -773237958446213512608]] where
 M := ![![![5215507746663393873361, -7733729775197283776088, 3108941826342389102712, -1510075706606065297520, -773237958446213512608]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5215507746663393873361, -7733729775197283776088, 3108941826342389102712, -1510075706606065297520, -773237958446213512608]] ![![-34435, 37650, -2340, 5228, 23736]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-1992642566596480267338000115, 3345203308410727547110359050, -1717267792007921541099892060, 715000141928924441812024380, -246966552573640620158541480]]]
 hmul := by decide  
 g := ![![![![-398528513319296053467600023, 669040661682145509422071810, -343453558401584308219978412, 143000028385784888362404876, -49393310514728124031708296]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, 282, -510, 120, -592]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![87, 282, -510, 120, -592]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![1, 3, 5, 5, 1]] where
  M :=![![![87, 282, -510, 120, -592], ![-3552, 3841, -190, 524, 2496], ![14976, -20690, 6861, -3800, -4344], ![-11256, 22302, -14322, 5243, -6132], ![-2408, -4578, 9618, -2184, 11683]]]
  hmulB := by decide  
  f := ![![![-1007, -54, 498, 576, 448]], ![![2688, -3069, 970, 1828, 2112]], ![![12672, -9298, 871, 3200, 4632]], ![![12552, -6306, -1218, 125, 1596]], ![![17991, -11717, 173, 2987, 5047]]]
  g := ![![![97, 294, 350, 440, -592], ![-864, -521, -1810, -1708, 2496], ![2760, -1094, 4083, 2560, -4344], ![-732, 5814, 2334, 5129, -6132], ![-2013, -5661, -6971, -8657, 11683]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 3, 3, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 1, 5], [0, 5, 4, 5], [5, 0, 5, 2], [0, 1]]
 g := ![![[6, 6, 3, 1], []], ![[1, 3, 0, 0, 5], [0, 2, 6]], ![[6, 2, 4, 3, 1, 6], [0, 5, 5, 4, 3, 6]], ![[1, 5, 5, 2], [0, 1, 0, 0, 0, 1]]]
 h' := ![![[5, 1, 5], [0, 0, 0, 1], [0, 1]], ![[0, 5, 4, 5], [6, 2, 4, 1], [5, 1, 5]], ![[5, 0, 5, 2], [0, 3, 2, 5], [0, 5, 4, 5]], ![[0, 1], [6, 2, 1], [5, 0, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 1, 3], []]
 b := ![[], [], [0, 2, 6, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 3, 3, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1581054289, -2336779016, 944493124, -454178780, -211518227]
  a := ![0, -8, -10, -22, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![256081788, -243174905, 286012037, 86201765, -211518227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1007, -54, 498, 576, 448]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1007, -54, 498, 576, 448]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1007, -54, 498, 576, 448], ![2688, -3069, 970, 1828, 2112], ![12672, -9298, 871, 3200, 4632], ![12552, -6306, -1218, 125, 1596], ![-7240, 5262, -462, -1776, -2595]]]
  hmulB := by decide  
  f := ![![![87, 282, -510, 120, -592]], ![![-495, 589, -100, 92, 272]], ![![2214, -2714, 543, -440, -1128]], ![![-1608, 3186, -2046, 749, -876]], ![![-344, -654, 1374, -312, 1669]]]
  g := ![![![-563, -54, 498, 576, 448], ![-9, -3069, 970, 1828, 2112], ![2392, -9298, 871, 3200, 4632], ![3738, -6306, -1218, 125, 1596], ![-1390, 5262, -462, -1776, -2595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![87, 282, -510, 120, -592]] ![![-1007, -54, 498, 576, 448]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-493307, 439136, -92985, -209742, -263475]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-493307, 439136, -92985, -209742, -263475]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![4, 2, 8, 9, 1]] where
  M :=![![![-493307, 439136, -92985, -209742, -263475], ![-1580850, 1048291, -34081, -288246, -468027], ![-2808162, 1373012, 292018, 3154, -325395], ![-185760, -641758, 542426, 766267, 731568], ![1555950, -749012, -171523, -15532, 166936]]]
  hmulB := by decide  
  f := ![![![214499, -108568, -156227, 11972, -322827]], ![![-1936962, 2330033, -419423, 369116, 1040313]], ![![6241878, -9269460, 3739462, -1812124, -906243]], ![![-1750248, 6091442, -5784202, 1742961, -4597164]], ![![2429758, -1145268, -1884325, 165509, -3774302]]]
  g := ![![![50963, 87826, 183165, 196503, -263475], ![26478, 180395, 337285, 356727, -468027], ![-136962, 183982, 263198, 266519, -325395], ![-282912, -191354, -482738, -528895, 731568], ![80746, -98444, -137001, -137996, 166936]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [5, 2, 2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 9, 6], [6, 6, 4, 3], [6, 1, 9, 2], [0, 1]]
 g := ![![[10, 6, 0, 1], [6, 1], []], ![[5, 3, 3, 7, 4, 2], [8, 3, 6, 5, 2, 2], [9, 5, 3]], ![[1, 6, 10, 2, 5, 5], [10, 9, 8, 7, 9, 4], [7, 1, 9]], ![[8, 0, 6, 1, 1, 10], [5, 8, 6, 2, 2, 6], [8, 5, 4]]]
 h' := ![![[5, 3, 9, 6], [3, 5, 8, 1], [0, 0, 1], [0, 1]], ![[6, 6, 4, 3], [2, 7, 0, 9], [2, 9, 1, 9], [5, 3, 9, 6]], ![[6, 1, 9, 2], [0, 5, 4, 8], [1, 9, 1, 7], [6, 6, 4, 3]], ![[0, 1], [5, 5, 10, 4], [7, 4, 8, 6], [6, 1, 9, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 5, 8], []]
 b := ![[], [], [10, 5, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [5, 2, 2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3721512818461, -10075128233314, 8905689248078, -2442674770084, 7340811532092]
  a := ![3, -126, -123, -313, -430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2331066664537, -2250613754318, -4529163909878, -6228179868992, 7340811532092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-214499, 108568, 156227, -11972, 322827]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-214499, 108568, 156227, -11972, 322827]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-214499, 108568, 156227, -11972, 322827], ![1936962, -2330033, 419423, -369116, -1040313], ![-6241878, 9269460, -3739462, 1812124, 906243], ![1750248, -6091442, 5784202, -1742961, 4597164], ![4439526, -2508960, -2878301, 155178, -6317780]]]
  hmulB := by decide  
  f := ![![![493307, -439136, 92985, 209742, 263475]], ![![323098, -254985, 36911, 102474, 138357]], ![![524364, -364348, 24172, 114118, 173295]], ![![375656, -261030, 18314, 82879, 125112]], ![![-141450, 68092, 15593, 1412, -15176]]]
  g := ![![![-135487, 108568, 156227, -11972, 322827], ![1063044, -2330033, 419423, -369116, -1040313], ![-3216358, 9269460, -3739462, 1812124, 906243], ![486772, -6091442, 5784202, -1742961, 4597164], ![2773068, -2508960, -2878301, 155178, -6317780]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-493307, 439136, -92985, -209742, -263475]] ![![-214499, 108568, 156227, -11972, 322827]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8214335, 6507500, -908852, -2578014, -3497564]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-8214335, 6507500, -908852, -2578014, -3497564]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![5, 8, 7, 2, 1]] where
  M :=![![![-8214335, 6507500, -908852, -2578014, -3497564], ![-20985384, 12781747, 431922, -2556618, -4975392], ![-29852352, 11717664, 5249737, 3144774, -413532], ![9252096, -15672432, 7008492, 11658739, 12542316], ![16389224, -6226500, -3029752, -1942634, 14577]]]
  hmulB := by decide  
  f := ![![![1361421, -3104580, 2283956, -778118, 1306532]], ![![7839192, -6278465, -2576166, -379506, -8588304]], ![![-51529824, 65001648, -15246275, 10885758, 23487876]], ![![66544032, -107013504, 50975724, -22215761, 1719612]], ![![-14028515, 17910096, -4440853, 3039216, 6097073]]]
  g := ![![![713345, 2652924, 1813392, 339778, -3497564], ![299352, 4044991, 2712282, 568782, -4975392], ![-2137284, 1155840, 626497, 305526, -413532], ![-4112268, -8923920, -6214440, -1032761, 12542316], ![1255103, -487932, -240907, -151676, 14577]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [1, 3, 9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 5, 7, 11], [10, 4, 10, 12], [1, 3, 9, 3], [0, 1]]
 g := ![![[1, 5, 8, 4], [0, 10, 1], []], ![[4, 9, 4, 3, 8, 2], [4], [9, 6, 5, 8, 4, 5]], ![[2, 11, 12, 12, 9, 1], [9], [1, 6, 5, 12, 7, 12]], ![[4, 10, 6, 9, 9, 3], [1, 12, 1], [9, 11, 6, 3, 6, 1]]]
 h' := ![![[12, 5, 7, 11], [0, 3, 8, 11], [0, 0, 0, 1], [0, 1]], ![[10, 4, 10, 12], [5, 10, 3, 8], [3, 8, 11], [12, 5, 7, 11]], ![[1, 3, 9, 3], [8, 6, 10, 8], [11, 8, 3], [10, 4, 10, 12]], ![[0, 1], [11, 7, 5, 12], [5, 10, 12, 12], [1, 3, 9, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 2, 9], []]
 b := ![[], [], [12, 2, 2, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [1, 3, 9, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![286522235, -577718166, 394424247, -131806028, 217771689]
  a := ![1, -9, -9, -23, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-61718170, -178453206, -86921352, -43642262, 217771689]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1361421, 3104580, -2283956, 778118, -1306532]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1361421, 3104580, -2283956, 778118, -1306532]] 
 ![![13, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-1361421, 3104580, -2283956, 778118, -1306532], ![-7839192, 6278465, 2576166, 379506, 8588304], ![51529824, -65001648, 15246275, -10885758, -23487876], ![-66544032, 107013504, -50975724, 22215761, -1719612], ![24270632, -57597340, 43769064, -14667662, 26418635]]]
  hmulB := by decide  
  f := ![![![8214335, -6507500, 908852, 2578014, 3497564]], ![![4141748, -2985519, 246422, 989898, 1458896]], ![![8615054, -5907128, 295291, 1741182, 2722244]], ![![1815788, -796736, -259468, -103591, 111380]], ![![2530522, -2524500, 652528, 1339286, 1613139]]]
  g := ![![![1060503, 3104580, -2283956, 778118, -1306532], ![-8597120, 6278465, 2576166, 379506, 8588304], ![26426458, -65001648, 15246275, -10885758, -23487876], ![-4875860, 107013504, -50975724, 22215761, -1719612], ![-21759370, -57597340, 43769064, -14667662, 26418635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-8214335, 6507500, -908852, -2578014, -3497564]] ![![-1361421, 3104580, -2283956, 778118, -1306532]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -4, -4, -4, -2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![15, -4, -4, -4, -2]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![2, 2, 3, 1, 0], ![14, 15, 13, 0, 1]] where
  M :=![![![15, -4, -4, -4, -2], ![-12, 21, -10, -16, -18], ![-108, 88, -13, -32, -42], ![-120, 60, 12, -11, -24], ![56, -40, 2, 20, 23]]]
  hmulB := by decide  
  f := ![![![-161, 44, -16, -28, -38]], ![![-228, 61, -22, -40, -54]], ![![-324, 88, -33, -56, -78]], ![![-110, 30, -11, -19, -26]], ![![-574, 155, -57, -100, -137]]]
  g := ![![![3, 2, 2, -4, -2], ![16, 19, 16, -16, -18], ![32, 46, 37, -32, -42], ![14, 26, 21, -11, -24], ![-18, -25, -21, 20, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 1, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 12], [15, 2, 5], [0, 1]]
 g := ![![[9, 2, 13], [1, 4], [4, 1], []], ![[5, 2, 16, 5], [1, 15], [8, 4], [11, 8]], ![[12, 1, 9, 6], [14, 8], [7, 9], [1, 8]]]
 h' := ![![[6, 14, 12], [4, 16, 8], [14, 8, 15], [0, 0, 1], [0, 1]], ![[15, 2, 5], [16, 4, 4], [15, 14, 7], [15, 15, 2], [6, 14, 12]], ![[0, 1], [15, 14, 5], [0, 12, 12], [16, 2, 14], [15, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 13], []]
 b := ![[], [8, 4, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 1, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-406664368, 556413004, -200474932, 101605608, 67142216]
  a := ![1, 44, 49, 114, 175]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-91168624, -38466556, -81067092, 101605608, 67142216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161, 44, -16, -28, -38]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-161, 44, -16, -28, -38]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![16, 11, 1, 0, 0], ![14, 16, 0, 1, 0], ![10, 3, 0, 0, 1]] where
  M :=![![![-161, 44, -16, -28, -38], ![-228, 61, -22, -40, -54], ![-324, 88, -33, -56, -78], ![-120, 36, -12, -19, -24], ![128, -40, 14, 20, 27]]]
  hmulB := by decide  
  f := ![![![15, -4, -4, -4, -2]], ![![-12, 21, -10, -16, -18]], ![![0, 15, -11, -16, -16]], ![![-6, 20, -12, -19, -20]], ![![10, -1, -4, -4, -3]]]
  g := ![![![51, 46, -16, -28, -38], ![72, 65, -22, -40, -54], ![104, 93, -33, -56, -78], ![34, 32, -12, -19, -24], ![-38, -35, 14, 20, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[2, 2], [1], [9], [1]], ![[13, 15], [1], [9], [1]]]
 h' := ![![[14, 16], [5, 11], [10, 16], [7, 14], [0, 1]], ![[0, 1], [6, 6], [13, 1], [16, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [16, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29312, -31527, 1233, -5698, -22596]
  a := ![-1, -7, -13, -23, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18548, 6698, 1233, -5698, -22596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![15, -4, -4, -4, -2]] ![![-161, 44, -16, -28, -38]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [12, 11, 17, 4, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 9, 5, 1], [9, 7, 12, 1, 11], [3, 15, 5, 14, 10], [13, 6, 16, 3, 17], [0, 1]]
 g := ![![[2, 9, 3, 7, 7], [17, 14, 16, 1, 1], [], []], ![[15, 8, 6, 2, 4, 12, 7], [8, 17, 4, 10, 14, 1, 17], [9, 6, 11, 11], [11, 1]], ![[17, 13, 6, 17, 9, 8, 12, 5], [17, 12, 16, 0, 2, 2, 16, 1], [8, 6, 10, 6], [0, 0, 10, 7]], ![[8, 0, 2, 17, 16, 14, 3, 8], [8, 13, 15, 12, 18, 0, 2, 13], [13, 13, 17, 16], [4, 10, 0, 5]], ![[9, 5, 12, 10, 3, 3, 16, 7], [8, 4, 0, 2, 8, 16, 6, 7], [8, 0, 3, 9], [14, 16, 11, 4]]]
 h' := ![![[14, 9, 5, 1], [5, 6, 11, 0, 8], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 7, 12, 1, 11], [17, 4, 4, 10, 8], [17, 13, 15, 10, 13], [7, 5, 4, 0, 12], [14, 9, 5, 1]], ![[3, 15, 5, 14, 10], [2, 6, 6, 4, 4], [5, 17, 18, 6, 11], [5, 12, 12, 11, 14], [9, 7, 12, 1, 11]], ![[13, 6, 16, 3, 17], [7, 6, 16, 14, 4], [16, 1, 4, 3, 8], [18, 2, 1, 7, 15], [3, 15, 5, 14, 10]], ![[0, 1], [18, 16, 1, 10, 14], [0, 7, 1, 0, 5], [1, 0, 1, 1, 16], [13, 6, 16, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 2, 2], [], [], []]
 b := ![[], [11, 1, 6, 10, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [12, 11, 17, 4, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5604619500300, -13065549555708, 9788910121834, -3304029890266, 5774946388212]
  a := ![0, -4, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![294979973700, -687660502932, 515205795886, -173896310014, 303944546748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53119, -14376, 5265, 9274, 12585]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![53119, -14376, 5265, 9274, 12585]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![15, 1, 1, 0, 0], ![4, 19, 0, 1, 0], ![17, 11, 0, 0, 1]] where
  M :=![![![53119, -14376, 5265, 9274, 12585], ![75510, -20437, 7483, 13182, 17889], ![107334, -29048, 10634, 18734, 25425], ![38520, -10418, 3814, 6719, 9120], ![-40614, 10992, -4023, -7088, -9620]]]
  hmulB := by decide  
  f := ![![![5, -40, 47, -12, 45]], ![![270, -275, -7, -32, -207]], ![![-39, 35, 8, 4, 39]], ![![274, -325, 55, -49, -147]], ![![131, -131, -7, -14, -104]]]
  g := ![![![-12039, -14534, 5265, 9274, 12585], ![-17112, -20659, 7483, 13182, 17889], ![-24319, -29361, 10634, 18734, 25425], ![-8722, -10531, 3814, 6719, 9120], ![9201, 11109, -4023, -7088, -9620]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [11, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[6, 13], [6, 9], [7, 9], [1]], ![[22, 10], [10, 14], [11, 14], [1]]]
 h' := ![![[3, 22], [3, 6], [15, 20], [12, 3], [0, 1]], ![[0, 1], [21, 17], [6, 3], [21, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [17, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [11, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24508, -26850, 2261, -6224, -17750]
  a := ![13, -8, -12, -24, -49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13793, 12365, 2261, -6224, -17750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, 1, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![3, -2, 1, 0, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![19, 7, 1, 0, 0], ![14, 20, 0, 1, 0], ![7, 14, 0, 0, 1]] where
  M :=![![![3, -2, 1, 0, 1], ![6, -3, -1, 0, -3], ![-18, 26, -6, 4, 9], ![24, -40, 20, -9, 0], ![-10, 22, -17, 6, -10]]]
  hmulB := by decide  
  f := ![![![1, 6, 3, 2, 1]], ![![6, -1, 9, 10, 9]], ![![5, 3, 6, 6, 5]], ![![10, 0, 10, 11, 10]], ![![3, 2, 6, 6, 5]]]
  g := ![![![-1, -1, 1, 0, 1], ![2, 2, -1, 0, -3], ![-1, -6, -6, 4, 9], ![-10, 0, 20, -9, 0], ![13, 7, -17, 6, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[4, 16], [16, 18], [9, 13], [1]], ![[0, 7], [0, 5], [0, 10], [1]]]
 h' := ![![[17, 22], [22, 19], [21, 15], [10, 17], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [9, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [13, 6, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![224, 684, -540, 338, 342]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![146, -308, -540, 338, 342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, 0, 0, 2]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-7, 6, 0, 0, 2]] 
 ![![23, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-7, 6, 0, 0, 2], ![12, -21, 8, -4, -6], ![-36, 58, -31, 16, -6], ![-24, 6, 30, 1, 60], ![76, -78, 0, -12, -57]]]
  hmulB := by decide  
  f := ![![![-75057, 20310, -7440, -13104, -17782]], ![![-53589, 14501, -5312, -9356, -12696]], ![![-22911, 6200, -2271, -4000, -5428]], ![![-5631, 1524, -558, -983, -1334]], ![![-26875, 7272, -2664, -4692, -6367]]]
  g := ![![![-5, 6, 0, 0, 2], ![15, -21, 8, -4, -6], ![-31, 58, -31, 16, -6], ![-35, 6, 30, 1, 60], ![77, -78, 0, -12, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![53119, -14376, 5265, 9274, 12585]] ![![3, -2, 1, 0, 1]]
  ![![75057, -20310, 7440, 13104, 17782]] where
 M := ![![![75057, -20310, 7440, 13104, 17782]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![75057, -20310, 7440, 13104, 17782]] ![![-7, 6, 0, 0, 2]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB687I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB687I0 : PrimesBelowBoundCertificateInterval O 1 23 687 where
  m := 9
  g := ![5, 5, 5, 2, 2, 2, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB687I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![2476099]
    · exact ![529, 529, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I17N1, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1], [I17N1], [], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
