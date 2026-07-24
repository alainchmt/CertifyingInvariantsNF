
import IdealArithmetic.Examples.NF5_3_1125000000_2.RI5_3_1125000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-272622, 81904, 193224, -23479, -30401]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-272622, 81904, 193224, -23479, -30401]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![94, 31, 42, 1, 0], ![12, 10, 75, 0, 1]] where
  M :=![![![-272622, 81904, 193224, -23479, -30401], ![-304010, 86451, 210766, -25322, -33114], ![-165570, 43955, 111773, -13240, -17530], ![64355, -22009, -48188, 6014, 7607], ![56060, -16507, -39414, 4768, 6199]]]
  hmulB := by decide  
  f := ![![![-3106, 5278, -4362, -103, 753]], ![![7530, -12945, 10762, 106, -1918]], ![![-9590, 15965, -13051, -640, 2130]], ![![-4247, 7032, -5732, -320, 919]], ![![-6536, 10846, -8851, -470, 1431]]]
  g := ![![![21488, 10409, 32331, -23479, -30401], ![23118, 11239, 35120, -25322, -33114], ![12050, 5885, 18529, -13240, -17530], ![-5535, -2659, -8143, 6014, 7607], ![-4360, -2115, -6585, 4768, 6199]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [69, 92, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 84, 48], [92, 22, 59], [0, 1]]
 g := ![![[64, 75, 44], [47, 91, 36], [88, 35], [63, 68, 1], [59, 10], [1]], ![[26, 7, 85, 89], [74, 93, 75, 90], [26, 81], [17, 78, 102, 57], [57, 86], [49, 15, 17, 61]], ![[90, 32, 87, 71], [21, 93, 42, 15], [89, 85], [81, 103, 100, 66], [76, 92], [23, 45, 26, 46]]]
 h' := ![![[78, 84, 48], [74, 46, 30], [22, 95, 6], [40, 55, 79], [48, 51, 106], [38, 15, 63], [0, 1]], ![[92, 22, 59], [84, 83, 86], [61, 12, 91], [101, 74, 98], [65, 48, 72], [50, 93, 73], [78, 84, 48]], ![[0, 1], [96, 85, 98], [2, 0, 10], [77, 85, 37], [101, 8, 36], [67, 106, 78], [92, 22, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 41], []]
 b := ![[], [17, 57, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [69, 92, 44, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16030156, -8513460, 20507778, -32159511, -26636436]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31089730, 11727063, 31485420, -32159511, -26636436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10557, 17995, -14896, -296, 2592]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-10557, 17995, -14896, -296, 2592]] 
 ![![107, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-10557, 17995, -14896, -296, 2592], ![25920, -44189, 36582, 720, -6368], ![-31840, 54259, -44909, -906, 7808], ![26080, -44514, 36874, 673, -6436], ![-58010, 98819, -81776, -1684, 14197]]]
  hmulB := by decide  
  f := ![![![-155111, 93633, 155254, -21644, -24880]], ![![-90753, 54604, 90664, -12632, -14528]], ![![-19116, 11327, 18929, -2630, -3032]], ![![-123265, 74311, 123284, -17183, -19756]], ![![-1103, 678, 1116, -156, -179]]]
  g := ![![![-8476, 17995, -14896, -296, 2592], ![20819, -44189, 36582, 720, -6368], ![-25547, 54259, -44909, -906, 7808], ![21011, -44514, 36874, 673, -6436], ![-46502, 98819, -81776, -1684, 14197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -3, -6, 1, 1]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![8, -3, -6, 1, 1]] 
 ![![107, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![8, -3, -6, 1, 1], ![10, -3, -8, 2, 2], ![10, -4, -5, 6, 2], ![5, 3, -6, 12, 9], ![20, -12, 0, 26, 3]]]
  hmulB := by decide  
  f := ![![![-336, 57, 354, -35, -57]], ![![-222, 40, 230, -23, -37]], ![![-86, 13, 93, -9, -15]], ![![-327, 57, 342, -34, -55]], ![![-182, 27, 198, -19, -32]]]
  g := ![![![2, -3, -6, 1, 1], ![1, -3, -8, 2, 2], ![-3, -4, -5, 6, 2], ![-17, 3, -6, 12, 9], ![-19, -12, 0, 26, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-272622, 81904, 193224, -23479, -30401]] ![![-10557, 17995, -14896, -296, 2592]]
  ![![-336, 57, 354, -35, -57]] where
 M := ![![![-336, 57, 354, -35, -57]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-336, 57, 354, -35, -57]] ![![8, -3, -6, 1, 1]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [95, 10, 35, 67, 71, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 15, 43, 76, 14], [5, 87, 6, 98, 40], [34, 84, 31, 56, 28], [25, 31, 29, 97, 27], [0, 1]]
 g := ![![[76, 73, 74, 27, 60], [53, 5, 47, 16], [36, 64, 75, 76, 22], [101, 106, 46, 12, 74], [38, 1], []], ![[62, 93, 24, 73, 88, 50, 8, 62], [9, 28, 56, 104], [40, 47, 79, 19, 107, 23, 92, 52], [66, 58, 26, 83, 52, 8, 68, 11], [46, 4, 82, 75], [4, 51, 12, 69, 57, 99, 66, 19]], ![[24, 32, 11, 108, 20, 32, 87, 69], [100, 65, 88, 100], [2, 103, 53, 48, 8, 18, 37, 68], [30, 47, 13, 66, 62, 57, 49, 30], [67, 24, 76, 102], [11, 77, 6, 101, 64, 93, 57, 17]], ![[66, 54, 12, 25, 85, 108, 43, 64], [79, 76, 75, 28], [4, 94, 43, 39, 24, 41, 92, 31], [12, 26, 90, 82, 12, 67, 41, 45], [82, 77, 40, 83], [17, 55, 50, 70, 68, 89, 39, 43]], ![[69, 56, 15, 12, 108, 82, 10, 25], [54, 104, 26, 82], [35, 79, 80, 55, 71, 69, 101, 84], [93, 87, 61, 34, 63, 54, 4, 88], [6, 62, 3, 20], [89, 53, 107, 40, 62, 51, 21, 63]]]
 h' := ![![[83, 15, 43, 76, 14], [25, 85, 39, 7, 96], [68, 0, 88, 107, 4], [106, 98, 6, 86, 26], [96, 70, 77, 35, 69], [0, 0, 0, 1], [0, 1]], ![[5, 87, 6, 98, 40], [62, 25, 84, 26, 42], [63, 35, 50, 22, 70], [55, 102, 89, 50, 34], [68, 79, 25, 47, 50], [29, 29, 66, 86, 27], [83, 15, 43, 76, 14]], ![[34, 84, 31, 56, 28], [88, 80, 34, 97, 76], [66, 69, 73, 76, 10], [89, 8, 57, 58, 80], [81, 65, 5, 99, 30], [61, 81, 99, 38, 59], [5, 87, 6, 98, 40]], ![[25, 31, 29, 97, 27], [43, 89, 99, 25, 7], [71, 1, 2, 51, 79], [95, 16, 19, 97, 88], [29, 85, 8, 16, 13], [84, 10, 10, 23, 65], [34, 84, 31, 56, 28]], ![[0, 1], [75, 48, 71, 63, 106], [55, 4, 5, 71, 55], [22, 103, 47, 36, 99], [6, 28, 103, 21, 56], [85, 98, 43, 70, 67], [25, 31, 29, 97, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 19, 106, 82], [], [], []]
 b := ![[], [38, 16, 88, 11, 72], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [95, 10, 35, 67, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-877419374807164317, 142431678946784152, 456430075424167946, -1325808315375088216, -624501657476173912]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8049719034928113, 1306712650887928, 4187431884625394, -12163379040138424, -5729373004368568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 15386239549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-142103, 40860, 98934, -11914, -15548]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-142103, 40860, 98934, -11914, -15548]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![78, 97, 90, 1, 0], ![67, 36, 21, 0, 1]] where
  M :=![![![-142103, 40860, 98934, -11914, -15548], ![-155480, 41839, 105548, -12536, -16560], ![-82800, 20458, 54375, -6348, -8512], ![35180, -11688, -25968, 3223, 4096], ![28990, -8100, -20058, 2398, 3151]]]
  hmulB := by decide  
  f := ![![![489, -120, -210, 710, 292]], ![![2920, -345, -1660, 4504, 2256]], ![![11280, -2762, -4849, 16380, 6752]], ![![12114, -2613, -5594, 17843, 7736]], ![![3761, -822, -1725, 5532, 2387]]]
  g := ![![![16185, 15542, 13254, -11914, -15548], ![17096, 16407, 13996, -12536, -16560], ![8696, 8342, 7119, -6348, -8512], ![-4342, -4175, -3558, 3223, 4096], ![-3267, -3134, -2673, 2398, 3151]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [68, 71, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 102, 45], [110, 10, 68], [0, 1]]
 g := ![![[91, 14, 51], [107, 16], [18, 60], [29, 106], [7, 20, 11], [1]], ![[76, 35, 64, 68], [30, 95], [96, 87], [27, 44], [46, 104, 107, 10], [52, 26, 69, 47]], ![[100, 98, 104, 59], [65, 57], [0, 72], [43, 61], [5, 39, 75, 55], [91, 97, 71, 66]]]
 h' := ![![[27, 102, 45], [82, 81, 86], [37, 36, 4], [73, 71, 25], [89, 55, 85], [45, 42, 24], [0, 1]], ![[110, 10, 68], [7, 57, 98], [76, 16, 78], [29, 99, 55], [82, 14, 48], [101, 89, 96], [27, 102, 45]], ![[0, 1], [101, 88, 42], [112, 61, 31], [15, 56, 33], [112, 44, 93], [0, 95, 106], [110, 10, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 64], []]
 b := ![[], [14, 81, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [68, 71, 89, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8848491, 210909, 5945825, -14242923, -7976267]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14482384, 14769204, 12878854, -14242923, -7976267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![489, -120, -210, 710, 292]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![489, -120, -210, 710, 292]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![49, 23, 1, 0, 0], ![3, 61, 0, 1, 0], ![54, 100, 0, 0, 1]] where
  M :=![![![489, -120, -210, 710, 292], ![2920, -345, -1660, 4504, 2256], ![11280, -2762, -4849, 16380, 6752], ![32300, -3864, -18312, 49791, 24880], ![50230, -14424, -19266, 71422, 27159]]]
  hmulB := by decide  
  f := ![![![-142103, 40860, 98934, -11914, -15548]], ![![-155480, 41839, 105548, -12536, -16560]], ![![-93999, 26415, 64865, -7774, -10188]], ![![-87393, 23567, 59374, -7055, -9316]], ![![-205244, 56480, 140506, -16766, -22057]]]
  g := ![![![-63, -600, -210, 710, 292], ![-452, -4093, -1660, 4504, 2256], ![-1459, -13855, -4849, 16380, 6752], ![-4985, -45203, -18312, 49791, 24880], ![-6076, -58796, -19266, 71422, 27159]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [75, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 112], [0, 1]]
 g := ![![[68, 9], [91], [56], [82], [0, 13], [98, 1]], ![[46, 104], [91], [56], [82], [31, 100], [83, 112]]]
 h' := ![![[98, 112], [15, 3], [25, 59], [65, 13], [0, 67], [108, 37], [0, 1]], ![[0, 1], [83, 110], [44, 54], [96, 100], [12, 46], [5, 76], [98, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [68, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [75, 15, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66676, 77660, -130450, 164481, 168975]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27959, -211087, -130450, 164481, 168975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-142103, 40860, 98934, -11914, -15548]] ![![489, -120, -210, 710, 292]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-707, 1209, -1004, -16, 172]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-707, 1209, -1004, -16, 172]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![60, 8, 26, 1, 0], ![79, 41, 97, 0, 1]] where
  M :=![![![-707, 1209, -1004, -16, 172], ![1720, -2947, 2450, 24, -408], ![-2040, 3537, -2971, 26, 456], ![1420, -2602, 2286, -221, -200], ![-3090, 5709, -5044, 544, 411]]]
  hmulB := by decide  
  f := ![![![-1541, 415, 1046, -124, -164]], ![![-1640, 405, 1078, -124, -168]], ![![-840, 183, 529, -54, -80]], ![![-1000, 258, 668, -77, -104]], ![![-2127, 528, 1401, -158, -217]]]
  g := ![![![-105, -45, -136, -16, 172], ![256, 107, 326, 24, -408], ![-312, -121, -377, 26, 456], ![240, 58, 216, -221, -200], ![-537, -122, -465, 544, 411]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [47, 118, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 25, 50], [20, 101, 77], [0, 1]]
 g := ![![[73, 15, 31], [2, 18, 98], [29, 124, 15], [12, 120, 26], [99, 60, 70], [1]], ![[15, 103, 111, 71], [47, 49, 30, 73], [41, 65, 54, 15], [74, 45, 72, 32], [9, 60, 64, 71], [60, 100, 116, 32]], ![[109, 7, 36, 109], [34, 36, 62, 28], [85, 125, 45, 10], [3, 6, 93, 24], [43, 24], [83, 124, 4, 95]]]
 h' := ![![[125, 25, 50], [33, 74, 83], [34, 109, 112], [71, 13, 53], [46, 26, 91], [80, 9, 18], [0, 1]], ![[20, 101, 77], [35, 81, 18], [23, 12, 125], [101, 115, 34], [59, 57, 77], [93, 77, 109], [125, 25, 50]], ![[0, 1], [31, 99, 26], [52, 6, 17], [113, 126, 40], [0, 44, 86], [35, 41], [20, 101, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 87], []]
 b := ![[], [56, 63, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [47, 118, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![57929417, -117789198, 88519206, 10122438, -107231508]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![62376947, 33052938, 80525922, 10122438, -107231508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -4, -2, 7, 3]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![8, -4, -2, 7, 3]] 
 ![![127, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![8, -4, -2, 7, 3], ![30, -1, -22, 46, 22], ![110, -27, -47, 156, 70], ![335, -57, -172, 506, 231], ![450, -95, -208, 662, 299]]]
  hmulB := by decide  
  f := ![![![-1496, 482, 1120, -129, -183]], ![![-250, 81, 186, -22, -30]], ![![-642, 205, 483, -54, -80]], ![![-1005, 329, 744, -91, -118]], ![![-1408, 441, 1074, -111, -184]]]
  g := ![![![-6, -4, -2, 7, 3], ![-42, -1, -22, 46, 22], ![-146, -27, -47, 156, 70], ![-474, -57, -172, 506, 231], ![-621, -95, -208, 662, 299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3618, 1481, 2944, -381, -467]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-3618, 1481, 2944, -381, -467]] 
 ![![127, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-3618, 1481, 2944, -381, -467], ![-4670, 1833, 3724, -478, -590], ![-2950, 1114, 2311, -294, -366], ![505, -249, -454, 60, 73], ![790, -320, -634, 84, 99]]]
  hmulB := by decide  
  f := ![![![7786, -13299, 11020, 191, -1929]], ![![3220, -5502, 4560, 77, -799]], ![![4780, -8169, 6771, 113, -1187]], ![![4067, -6964, 5778, 83, -1018]], ![![998, -1725, 1438, 5, -260]]]
  g := ![![![-2161, 1481, 2944, -381, -467], ![-2719, 1833, 3724, -478, -590], ![-1679, 1114, 2311, -294, -366], ![341, -249, -454, 60, 73], ![465, -320, -634, 84, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-707, 1209, -1004, -16, 172]] ![![8, -4, -2, 7, 3]]
  ![![-7786, 13299, -11020, -191, 1929]] where
 M := ![![![-7786, 13299, -11020, -191, 1929]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-7786, 13299, -11020, -191, 1929]] ![![-3618, 1481, 2944, -381, -467]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4088999, -987544, -2665998, 309716, 417136]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![4088999, -987544, -2665998, 309716, 417136]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![2, 54, 1, 0, 0], ![23, 33, 0, 1, 0], ![22, 10, 0, 0, 1]] where
  M :=![![![4088999, -987544, -2665998, 309716, 417136], ![4171360, -877519, -2594520, 293068, 404592], ![2022960, -334584, -1170587, 126100, 181544], ![-1177960, 355642, 836576, -101757, -131640], ![-814320, 187792, 522378, -60116, -81641]]]
  hmulB := by decide  
  f := ![![![-199291, 340368, -282034, -4948, 49344]], ![![493440, -836629, 690632, 18164, -118480]], ![![195838, -331850, 273857, 7396, -46904]], ![![93337, -157477, 129662, 4187, -21944]], ![![-3862, 7522, -6626, 796, 1527]]]
  g := ![![![-52515, 981560, -2665998, 309716, 417136], ![-47948, 958087, -2594520, 293068, 404592], ![-19314, 434354, -1170587, 126100, 181544], ![18209, -306451, 836576, -101757, -131640], ![10074, -192522, 522378, -60116, -81641]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [6, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 130], [0, 1]]
 g := ![![[60, 107], [80, 75], [33], [101], [28], [41], [1]], ![[54, 24], [66, 56], [33], [101], [28], [41], [1]]]
 h' := ![![[33, 130], [44, 99], [108, 72], [31, 66], [47, 106], [52, 40], [125, 33], [0, 1]], ![[0, 1], [36, 32], [126, 59], [113, 65], [8, 25], [62, 91], [35, 98], [33, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [79, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [6, 98, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60794, 70060, -34472, -50360, 42480]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1770, 24188, -34472, -50360, 42480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -158, 132, 0, -24]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![91, -158, 132, 0, -24]] 
 ![![131, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![91, -158, 132, 0, -24], ![-240, 391, -316, -24, 48], ![240, -470, 415, -52, -96], ![-360, 416, -260, -201, -32], ![340, -838, 804, -240, -241]]]
  hmulB := by decide  
  f := ![![![121, -854, -852, 160, 136]], ![![15, -43, -48, 8, 8]], ![![63, -356, -357, 68, 56]], ![![117, -822, -832, 151, 136]], ![![41, -216, -192, 48, 23]]]
  g := ![![![-41, -158, 132, 0, -24], ![123, 391, -316, -24, 48], ![-75, -470, 415, -52, -96], ![289, 416, -260, -201, -32], ![-1, -838, 804, -240, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 113, -92, -4, 12]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![479, 113, -92, -4, 12]] 
 ![![131, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![479, 113, -92, -4, 12], ![120, 295, 234, -48, -40], ![-200, 269, 343, -54, -56], ![-340, 66, 206, -23, -32], ![-70, -35, -4, 4, 1]]]
  hmulB := by decide  
  f := ![![![-211, 299, -222, -64, 12]], ![![-107, 148, -108, -36, 4]], ![![-88, 117, -83, -34, 0]], ![![-227, 291, -200, -99, -4]], ![![-235, 298, -204, -104, -11]]]
  g := ![![![-28, 113, -92, -4, 12], ![-151, 295, 234, -48, -40], ![-159, 269, 343, -54, -56], ![-59, 66, 206, -23, -32], ![14, -35, -4, 4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2

def I131N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1274249, 482175, 998866, -127244, -158114]] i)))

def SI131N3: IdealEqSpanCertificate' Table ![![-1274249, 482175, 998866, -127244, -158114]] 
 ![![131, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-1274249, 482175, 998866, -127244, -158114], ![-1581140, 576927, 1218838, -154124, -192748], ![-963740, 339343, 731051, -91774, -115500], ![213070, -92332, -178302, 23339, 28326], ![272980, -101835, -212578, 27002, 33637]]]
  hmulB := by decide  
  f := ![![![-2806479, 4784065, -3960300, -78420, 689182]], ![![-1704118, 2904927, -2404730, -47616, 418480]], ![![-1007216, 1716963, -1421327, -28130, 247340]], ![![-2517830, 4292026, -3552982, -70357, 618330]], ![![-1852849, 3158536, -2614716, -51678, 454983]]]
  g := ![![![-432719, 482175, 998866, -127244, -158114], ![-522218, 576927, 1218838, -154124, -192748], ![-309830, 339343, 731051, -91774, -115500], ![80416, -92332, -178302, 23339, 28326], ![91695, -101835, -212578, 27002, 33637]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N3 : Nat.card (O ⧸ I131N3) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N3)

lemma isPrimeI131N3 : Ideal.IsPrime I131N3 := prime_ideal_of_norm_prime hp131.out _ NI131N3
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![4088999, -987544, -2665998, 309716, 417136]] ![![91, -158, 132, 0, -24]]
  ![![-401571, 109402, 273786, -32604, -42968]] where
 M := ![![![-401571, 109402, 273786, -32604, -42968]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-401571, 109402, 273786, -32604, -42968]] ![![479, 113, -92, -4, 12]]
  ![![-219888349, 59896517, 149908646, -17851436, -23526588]] where
 M := ![![![-219888349, 59896517, 149908646, -17851436, -23526588]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N2 : IdealMulLeCertificate' Table 
  ![![-219888349, 59896517, 149908646, -17851436, -23526588]] ![![-1274249, 482175, 998866, -127244, -158114]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![30788877978721, -16554208278506, -28859797292506, 3938366622064, 4611020325378]]]
 hmul := by decide  
 g := ![![![![235029602891, -126368002126, -220303796126, 30063867344, 35198628438]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2, I131N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
    exact isPrimeI131N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1 ⊙ MulI131N2)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3154624, 1048015, 2332488, -289349, -367949]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-3154624, 1048015, 2332488, -289349, -367949]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![109, 74, 1, 0, 0], ![17, 59, 0, 1, 0], ![50, 124, 0, 0, 1]] where
  M :=![![![-3154624, 1048015, 2332488, -289349, -367949], ![-3679490, 1174809, 2674728, -329110, -421498], ![-2107490, 643752, 1503919, -183370, -236722], ![656135, -244033, -510242, 64772, 80731], ![659760, -215932, -484686, 59942, 76429]]]
  hmulB := by decide  
  f := ![![![-2448, 2353, -676, -2603, 1847]], ![![18470, -21259, 9912, 15606, -14106]], ![![7514, -9033, 4547, 5927, -5819]], ![![9237, -10767, 5158, 7625, -6988]], ![![11850, -13812, 6502, 9962, -9507]]]
  g := ![![![-1708609, -794590, 2332488, -289349, -367949], ![-1960256, -912933, 2674728, -329110, -421498], ![-1102783, -514408, 1503919, -183370, -236722], ![373247, 172859, -510242, 64772, 80731], ![355110, 165234, -484686, 59942, 76429]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [62, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 136], [0, 1]]
 g := ![![[49, 37], [28], [98], [75, 118], [77], [28], [1]], ![[120, 100], [28], [98], [120, 19], [77], [28], [1]]]
 h' := ![![[113, 136], [27, 96], [16, 24], [8, 80], [90, 23], [53, 112], [75, 113], [0, 1]], ![[0, 1], [52, 41], [125, 113], [6, 57], [86, 114], [105, 25], [103, 24], [113, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [30, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [62, 24, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4992, 26821, -25632, 10039, 31516]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7609, -18808, -25632, 10039, 31516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1231763, -333576, -837874, 99656, 131476]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1231763, -333576, -837874, 99656, 131476]] 
 ![![137, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![1231763, -333576, -837874, 99656, 131476], ![1314760, -327131, -866464, 101276, 135672], ![678360, -149428, -428407, 48844, 66880], ![-322980, 103306, 234960, -28921, -37028], ![-249280, 65532, 167662, -19820, -26289]]]
  hmulB := by decide  
  f := ![![![-35901, 82112, -76898, 19184, 21564]], ![![-13887, 33717, -32198, 9308, 9532]], ![![-27337, 66764, -63873, 18700, 19004]], ![![-2819, 22834, -26598, 17327, 11672]], ![![2620, 13564, -18922, 17476, 10351]]]
  g := ![![![768805, -333576, -837874, 99656, 131476], ![788261, -327131, -866464, 101276, 135672], ![385059, -149428, -428407, 48844, 66880], ![-219303, 103306, 234960, -28921, -37028], ![-153378, 65532, 167662, -19820, -26289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, -6, 12, 8]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![7, 1, -6, 12, 8]] 
 ![![137, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![7, 1, -6, 12, 8], ![80, -31, -22, 108, 32], ![160, 25, -139, 278, 184], ![880, -340, -242, 1189, 356], ![490, 329, -702, 1032, 909]]]
  hmulB := by decide  
  f := ![![![-33009, 9177, 22768, -2720, -3576]], ![![-20982, 5829, 14466, -1728, -2272]], ![![-377, 98, 255, -30, -40]], ![![-12227, 3397, 8430, -1007, -1324]], ![![50, -15, -32, 4, 5]]]
  g := ![![![-5, 1, -6, 12, 8], ![-20, -31, -22, 108, 32], ![-117, 25, -139, 278, 184], ![-221, -340, -242, 1189, 356], ![-582, 329, -702, 1032, 909]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2

def I137N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22802, 7584, 16868, -2093, -2661]] i)))

def SI137N3: IdealEqSpanCertificate' Table ![![-22802, 7584, 16868, -2093, -2661]] 
 ![![137, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-22802, 7584, 16868, -2093, -2661], ![-26610, 8507, 19354, -2382, -3050], ![-15250, 4665, 10889, -1328, -1714], ![4735, -1763, -3684, 468, 583], ![4770, -1563, -3506, 434, 553]]]
  hmulB := by decide  
  f := ![![![-2826, 4662, -3746, -303, 823]], ![![-2374, 3921, -3154, -248, 688]], ![![-620, 1003, -791, -95, 197]], ![![-2065, 3481, -2852, -116, 545]], ![![-680, 951, -636, -318, 337]]]
  g := ![![![-7902, 7584, 16868, -2093, -2661], ![-8918, 8507, 19354, -2382, -3050], ![-4925, 4665, 10889, -1328, -1714], ![1807, -1763, -3684, 468, 583], ![1632, -1563, -3506, 434, 553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N3 : Nat.card (O ⧸ I137N3) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N3)

lemma isPrimeI137N3 : Ideal.IsPrime I137N3 := prime_ideal_of_norm_prime hp137.out _ NI137N3
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-3154624, 1048015, 2332488, -289349, -367949]] ![![1231763, -333576, -837874, 99656, 131476]]
  ![![-740418094292, 306925721933, 606179467522, -78649386723, -96187230471]] where
 M := ![![![-740418094292, 306925721933, 606179467522, -78649386723, -96187230471]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-740418094292, 306925721933, 606179467522, -78649386723, -96187230471]] ![![7, 1, -6, 12, 8]]
  ![![16642651086, -5436125304, -12215924724, 1510148657, 1926200041]] where
 M := ![![![16642651086, -5436125304, -12215924724, 1510148657, 1926200041]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N2 : IdealMulLeCertificate' Table 
  ![![16642651086, -5436125304, -12215924724, 1510148657, 1926200041]] ![![-22802, 7584, 16868, -2093, -2661]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-32199055596067, 17312416291262, 30181620069262, -4118749826128, -4822212096006]]]
 hmul := by decide  
 g := ![![![![-235029602891, 126368002126, 220303796126, -30063867344, -35198628438]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2, I137N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
    exact isPrimeI137N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1 ⊙ MulI137N2)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![166, -95, -162, 15, 23]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![166, -95, -162, 15, 23]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![124, 5, 131, 1, 0], ![17, 47, 113, 0, 1]] where
  M :=![![![166, -95, -162, 15, 23], ![230, -127, -220, -18, 14], ![70, -62, -109, -154, -50], ![-365, 65, 202, -554, -265], ![-560, 146, 264, -762, -321]]]
  hmulB := by decide  
  f := ![![![834, -1431, 1190, 23, -207]], ![![-2070, 3519, -2908, -58, 506]], ![![2530, -4318, 3577, 70, -622]], ![![3039, -5194, 4307, 84, -749]], ![![1492, -2552, 2117, 41, -368]]]
  g := ![![![-15, -9, -34, 15, 23], ![16, -5, 4, -18, 14], ![144, 22, 185, -154, -50], ![524, 110, 739, -554, -265], ![715, 137, 981, -762, -321]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [54, 32, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 109, 21], [47, 29, 118], [0, 1]]
 g := ![![[67, 43, 117], [137, 133, 117], [112, 1], [124, 77, 11], [25, 100], [43, 1], []], ![[34, 45, 1, 105], [60, 38, 75, 87], [86, 121], [35, 17, 104, 68], [109, 36], [126, 7], [50, 24]], ![[116, 4, 138, 81], [105, 1, 111, 24], [7, 100], [7, 15, 108, 116], [99, 117], [131, 66], [92, 24]]]
 h' := ![![[135, 109, 21], [108, 70, 16], [88, 127, 123], [115, 104, 1], [53, 111, 17], [41, 99, 10], [0, 0, 1], [0, 1]], ![[47, 29, 118], [113, 23, 127], [129, 44, 118], [73, 62, 128], [129, 29, 44], [49, 77, 6], [96, 124, 29], [135, 109, 21]], ![[0, 1], [120, 46, 135], [22, 107, 37], [20, 112, 10], [67, 138, 78], [39, 102, 123], [21, 15, 109], [47, 29, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 25], []]
 b := ![[], [79, 121, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [54, 32, 96, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2011633, 2369587, -1187393, -1582174, 1373415]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1228992, -390432, 366054, -1582174, 1373415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-834, 1431, -1190, -23, 207]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-834, 1431, -1190, -23, 207]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![94, 8, 1, 0, 0], ![82, 53, 0, 1, 0], ![17, 134, 0, 0, 1]] where
  M :=![![![-834, 1431, -1190, -23, 207], ![2070, -3519, 2908, 58, -506], ![-2530, 4318, -3577, -70, 622], ![2075, -3541, 2934, 56, -509], ![-4610, 7860, -6508, -124, 1129]]]
  hmulB := by decide  
  f := ![![![-166, 95, 162, -15, -23]], ![![-230, 127, 220, 18, -14]], ![![-126, 72, 123, -8, -16]], ![![-183, 104, 178, 2, -17]], ![![-238, 133, 230, 21, -14]]]
  g := ![![![787, -112, -1190, -23, 207], ![-1924, 273, 2908, 58, -506], ![2366, -336, -3577, -70, 622], ![-1940, 275, 2934, 56, -509], ![4303, -610, -6508, -124, 1129]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [5, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[103, 28], [136, 42], [100], [10, 131], [117], [13], [1]], ![[0, 111], [51, 97], [100], [99, 8], [117], [13], [1]]]
 h' := ![![[41, 138], [15, 81], [54, 96], [89, 129], [42, 100], [99, 123], [134, 41], [0, 1]], ![[0, 1], [0, 58], [98, 43], [96, 10], [111, 39], [138, 16], [8, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [14, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [5, 98, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28812, 44349, -27726, -16277, 35330]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23824, -25938, -27726, -16277, 35330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![166, -95, -162, 15, 23]] ![![-834, 1431, -1190, -23, 207]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [84, 34, 24, 106, 100, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 82, 20, 130, 88], [22, 106, 81, 21, 143], [39, 109, 46, 54, 82], [123, 0, 2, 93, 134], [0, 1]]
 g := ![![[124, 81, 112, 73, 80], [81, 122, 140, 119], [8, 83, 90, 101, 19], [56, 86, 50, 39], [8, 106, 60, 49, 1], [], []], ![[58, 125, 142, 98, 22, 58, 139, 61], [58, 90, 57, 61], [2, 145, 66, 90, 101, 35, 71, 132], [65, 48, 139, 6], [138, 78, 80, 112, 15, 65, 43, 49], [118, 103, 130, 26], [95, 109, 36, 145]], ![[25, 14, 143, 44, 109, 32, 129, 118], [95, 134, 20, 86], [62, 87, 126, 107, 130, 94, 129, 20], [143, 51, 46, 120], [5, 110, 89, 49, 137, 61, 131, 25], [73, 137, 22, 35], [120, 9, 22, 36]], ![[49, 23, 60, 14, 50, 140, 39, 26], [70, 15, 127, 133], [47, 11, 91, 136, 94, 113, 46, 63], [73, 109, 51, 125], [139, 42, 144, 65, 70, 16, 120, 64], [94, 43, 60, 100], [130, 34, 102, 19]], ![[56, 40, 83, 5, 148, 101, 124, 137], [18, 145, 81, 102], [114, 18, 35, 146, 44, 142, 101, 87], [126, 20, 59, 140], [11, 134, 63, 88, 51, 139, 52, 87], [142, 81, 82, 112], [96, 109, 40, 76]]]
 h' := ![![[14, 82, 20, 130, 88], [15, 98, 141, 118, 26], [73, 4, 67, 124, 87], [29, 73, 130, 105, 67], [73, 62, 104, 137, 121], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[22, 106, 81, 21, 143], [3, 70, 19, 65, 105], [133, 119, 88, 93, 106], [29, 96, 87, 86, 15], [107, 70, 63, 134, 30], [26, 106, 12, 67, 76], [113, 42, 62, 51, 18], [14, 82, 20, 130, 88]], ![[39, 109, 46, 54, 82], [36, 37, 48, 57, 46], [87, 122, 75, 100, 58], [74, 79, 107, 108, 29], [49, 47, 19, 56, 57], [1, 94, 133, 58, 57], [89, 126, 81, 47, 66], [22, 106, 81, 21, 143]], ![[123, 0, 2, 93, 134], [100, 88, 39, 127, 64], [136, 40, 87, 130, 27], [57, 103, 110, 60, 98], [123, 98, 64, 12, 107], [145, 124, 24, 21, 104], [137, 34, 92, 93, 139], [39, 109, 46, 54, 82]], ![[0, 1], [17, 5, 51, 80, 57], [28, 13, 130, 0, 20], [75, 96, 13, 88, 89], [123, 21, 48, 108, 132], [111, 123, 129, 3, 60], [62, 96, 62, 107, 75], [123, 0, 2, 93, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 24, 117, 108], [], [], []]
 b := ![[], [143, 74, 129, 52, 141], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [84, 34, 24, 106, 100, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25742280121171, 58087705668337, -45622776244095, -398323567864, 55531900256691]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-172766980679, 389850373613, -306193129155, -2673312536, 372697317159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19836, -6617, -14520, 1809, 2289]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![19836, -6617, -14520, 1809, 2289]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![147, 20, 150, 132, 1]] where
  M :=![![![19836, -6617, -14520, 1809, 2289], ![22890, -7089, -16852, 2046, 2658], ![13290, -4238, -9135, 1142, 1434], ![-4275, 1745, 3046, -412, -479], ![-3860, 878, 3414, -366, -545]]]
  hmulB := by decide  
  f := ![![![-4, -1, 4, -7, -5]], ![![-50, 21, 12, -66, -18]], ![![-90, -22, 87, -162, -114]], ![![-545, 225, 134, -726, -201]], ![![-578, 175, 212, -815, -300]]]
  g := ![![![-2097, -347, -2370, -1989, 2289], ![-2436, -399, -2752, -2310, 2658], ![-1308, -218, -1485, -1246, 1434], ![438, 75, 496, 416, -479], ![505, 78, 564, 474, -545]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [14, 77, 114, 75, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 9, 73], [67, 10, 116, 133], [91, 131, 113, 18], [0, 1]]
 g := ![![[49, 13, 84, 118], [27, 25, 141, 97], [149, 81, 2, 18], [12, 8, 110], [82, 8, 56, 38], [1], []], ![[32, 140, 130, 148, 112], [144, 130, 142, 58, 46], [62, 109, 64, 54, 7], [55, 89, 116], [41, 5, 24, 10, 3], [136, 110, 76], [44]], ![[23, 132, 115, 66, 97, 149], [64, 66, 80, 19, 29, 119], [3, 72, 26, 87, 48, 140], [100, 134, 29], [26, 0, 51, 132, 27, 3], [116, 95, 50], [125, 63, 22]], ![[48, 143, 69, 20, 53, 36], [113, 36, 54, 29, 106, 50], [99, 11, 104, 10, 132, 78], [112, 5, 11], [57, 117, 65, 111, 9, 62], [22, 38, 116], [29, 2, 22]]]
 h' := ![![[69, 9, 73], [75, 16, 116, 32], [28, 97, 11, 90], [110, 22, 99, 138], [60, 112, 15, 84], [137, 74, 37, 76], [0, 0, 1], [0, 1]], ![[67, 10, 116, 133], [47, 28, 101, 23], [107, 27, 135, 58], [1, 118, 104, 32], [4, 77, 96, 56], [2, 95, 71, 123], [68, 119, 5, 128], [69, 9, 73]], ![[91, 131, 113, 18], [80, 1, 77, 50], [124, 138, 10, 102], [4, 122, 88, 148], [137, 139, 10, 123], [25, 42, 143, 146], [21, 44, 10, 79], [67, 10, 116, 133]], ![[0, 1], [87, 106, 8, 46], [110, 40, 146, 52], [95, 40, 11, 135], [105, 125, 30, 39], [70, 91, 51, 108], [23, 139, 135, 95], [91, 131, 113, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [144, 4, 48], []]
 b := ![[], [], [15, 39, 72, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [14, 77, 114, 75, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-156180298, 183414120, -91778880, -123121005, 105364350]
  a := ![4, 0, 0, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-103607548, -12740880, -105274380, -92921955, 105364350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, -4, 7, 5]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![4, 1, -4, 7, 5]] 
 ![![151, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![4, 1, -4, 7, 5], ![50, -21, -12, 66, 18], ![90, 22, -87, 162, 114], ![545, -225, -134, 726, 201], ![250, 248, -446, 584, 573]]]
  hmulB := by decide  
  f := ![![![-19836, 6617, 14520, -1809, -2289]], ![![-10398, 3465, 7612, -948, -1200]], ![![-17034, 5681, 12465, -1553, -1965]], ![![-8379, 2793, 6134, -764, -967]], ![![-3784, 1265, 2766, -345, -436]]]
  g := ![![![-1, 1, -4, 7, 5], ![-10, -21, -12, 66, 18], ![-27, 22, -87, 162, 114], ![-112, -225, -134, 726, 201], ![-103, 248, -446, 584, 573]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![19836, -6617, -14520, 1809, 2289]] ![![4, 1, -4, 7, 5]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB1640I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1640I3 : PrimesBelowBoundCertificateInterval O 103 151 1640 where
  m := 9
  g := ![3, 1, 2, 3, 4, 4, 2, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1640I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2, I131N3]
    · exact ![I137N0, I137N1, I137N2, I137N3]
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1225043, 107, 107]
    · exact ![15386239549]
    · exact ![1442897, 12769]
    · exact ![2048383, 127, 127]
    · exact ![17161, 131, 131, 131]
    · exact ![18769, 137, 137, 137]
    · exact ![2685619, 19321]
    · exact ![73439775749]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
      exact NI131N3
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
      exact NI137N3
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I127N1, I127N2, I131N1, I131N2, I131N3, I137N1, I137N2, I137N3, I151N1]
  Il := ![[I107N1, I107N2], [], [], [I127N1, I127N2], [I131N1, I131N2, I131N3], [I137N1, I137N2, I137N3], [], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
