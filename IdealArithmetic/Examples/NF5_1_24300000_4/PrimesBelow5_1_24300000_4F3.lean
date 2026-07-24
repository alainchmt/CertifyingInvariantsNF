
import IdealArithmetic.Examples.NF5_1_24300000_4.RI5_1_24300000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7193, 7887, 3450, 1774, 737]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![7193, 7887, 3450, 1774, 737]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![65, 16, 1, 0, 0], ![15, 12, 0, 1, 0], ![38, 19, 0, 0, 1]] where
  M :=![![![7193, 7887, 3450, 1774, 737], ![2948, 13154, 9361, 8374, 3548], ![14192, 24231, 20250, 25818, 16748], ![32022, 31927, 24183, 32811, 24044], ![46614, 49953, 35327, 44040, 31037]]]
  hmulB := by decide  
  f := ![![![-40267, -199403, 138364, -314732, 192907]], ![![771628, -23728, 186411, 662542, -629464]], ![![67391, -115418, 99940, -100402, 35445]], ![![102055, -46212, 56447, 27483, -48891]], ![![108432, -60285, 68230, 13582, -43023]]]
  g := ![![![-2539, -772, 3450, 1774, 737], ![-8093, -2846, 9361, 8374, 3548], ![-21736, -8671, 20250, 25818, 16748], ![-27530, -11267, 24183, 32811, 24044], ![-38221, -15266, 35327, 44040, 31037]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [15, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 106], [0, 1]]
 g := ![![[63, 3], [66, 102], [85], [43, 101], [37], [18, 1]], ![[10, 104], [83, 5], [85], [42, 6], [37], [36, 106]]]
 h' := ![![[18, 106], [80, 89], [18, 40], [104, 70], [13, 84], [51, 95], [0, 1]], ![[0, 1], [77, 18], [96, 67], [80, 37], [27, 23], [49, 12], [18, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [56, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [15, 89, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2165, 1860, 1581, 2094, 333]
  a := ![0, -8, -3, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1352, -513, 1581, 2094, 333]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25385, 8990, 4674, 10004, 10990]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![25385, 8990, 4674, 10004, 10990]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![29, 88, 1, 0, 0], ![8, 102, 0, 1, 0], ![19, 64, 0, 0, 1]] where
  M :=![![![25385, 8990, 4674, 10004, 10990], ![43960, 51053, 30970, 31328, 20008], ![80032, 126266, 91069, 101956, 62656], ![103332, 142330, 110304, 138061, 91952], ![161924, 196298, 147632, 186592, 128057]]]
  hmulB := by decide  
  f := ![![![2912731, -1417890, 1684086, 646204, -1316442]], ![![-5265768, 3926579, -4050774, 735288, 1292408]], ![![-3492979, 2776928, -2814189, 728304, 719866]], ![![-4749836, 3654412, -3736960, 820405, 1075992]], ![![-2722993, 2110620, -2153854, 492124, 604391]]]
  g := ![![![-3729, -19870, 4674, 10004, 10990], ![-13878, -66825, 30970, 31328, 20008], ![-42683, -208386, 91069, 101956, 62656], ![-55580, -275996, 110304, 138061, 91952], ![-75189, -374050, 147632, 186592, 128057]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [3, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 106], [0, 1]]
 g := ![![[5, 36], [77, 105], [83], [46, 34], [64], [92, 1]], ![[0, 71], [0, 2], [83], [71, 73], [64], [77, 106]]]
 h' := ![![[92, 106], [90, 6], [70, 76], [76, 46], [14, 81], [45, 8], [0, 1]], ![[0, 1], [0, 101], [0, 31], [28, 61], [83, 26], [32, 99], [92, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [15, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [3, 15, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10605, 35913, -1113, 13486, 25366]
  a := ![3, -61, 2, -65, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5310, -26777, -1113, 13486, 25366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 21, 15, 18, 12]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![17, 21, 15, 18, 12]] 
 ![![107, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![17, 21, 15, 18, 12], ![48, 62, 45, 54, 36], ![144, 183, 134, 162, 108], ![192, 243, 177, 215, 144], ![264, 333, 243, 294, 197]]]
  hmulB := by decide  
  f := ![![![91, -69, 15, -18, 12]], ![![3, -1, 0, 0, 0]], ![![82, -63, 14, -18, 12]], ![![12, -9, 3, -1, 0]], ![![26, -21, 3, -6, 5]]]
  g := ![![![-20, 21, 15, 18, 12], ![-60, 62, 45, 54, 36], ![-179, 183, 134, 162, 108], ![-237, 243, 177, 215, 144], ![-325, 333, 243, 294, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![7193, 7887, 3450, 1774, 737]] ![![25385, 8990, 4674, 10004, 10990]]
  ![![1108066181, 1300102827, 896552602, 1053229426, 710518223]] where
 M := ![![![1108066181, 1300102827, 896552602, 1053229426, 710518223]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![1108066181, 1300102827, 896552602, 1053229426, 710518223]] ![![17, 21, 15, 18, 12]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![600142496125, 760482210018, 554341205189, 670728949592, 448565304235]]]
 hmul := by decide  
 g := ![![![![5608808375, 7107310374, 5180758927, 6268494856, 4192199105]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31459, -43087, 38688, -31800, 7937]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![31459, -43087, 38688, -31800, 7937]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![33, 42, 57, 1, 0], ![81, 104, 42, 0, 1]] where
  M :=![![![31459, -43087, 38688, -31800, 7937], ![31748, 46284, -27213, 93250, -63600], ![-254400, 34185, -80916, -181626, 186500], ![357126, -188363, 217199, 58959, -149826], ![-315526, 218587, -230401, 20748, 90759]]]
  hmulB := by decide  
  f := ![![![44169, 56253, 41010, 49546, 33077]], ![![132308, 167802, 122407, 148174, 99092]], ![![396368, 501981, 365986, 442998, 296348]], ![![276459, 350311, 255429, 309151, 206777]], ![![318403, 403710, 294397, 356282, 238258]]]
  g := ![![![4018, 4285, 13926, -31800, 7937], ![19322, 25176, -24507, 93250, -63600], ![-85938, -107647, 22374, -181626, 186500], ![96765, 118507, 28892, 58959, -149826], ![-76621, -92585, -47935, 20748, 90759]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [75, 26, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 89, 15], [83, 19, 94], [0, 1]]
 g := ![![[66, 53, 64], [47, 9], [31, 33, 71], [60, 22, 28], [31, 27], [1]], ![[61, 25, 81, 31], [55, 21], [91, 61, 86, 25], [40, 58, 5, 43], [95, 25], [29, 1, 82, 105]], ![[104, 108, 67, 1], [34, 89], [78, 23, 66, 94], [4, 49, 82, 27], [69, 105], [13, 10, 6, 4]]]
 h' := ![![[64, 89, 15], [60, 8, 8], [73, 78, 3], [78, 88, 92], [30, 88, 30], [34, 83, 38], [0, 1]], ![[83, 19, 94], [44, 51, 54], [71, 86, 28], [74, 67, 16], [85, 94, 37], [4, 78, 5], [64, 89, 15]], ![[0, 1], [71, 50, 47], [21, 54, 78], [36, 63, 1], [62, 36, 42], [88, 57, 66], [83, 19, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 89], []]
 b := ![[], [80, 85, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [75, 26, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45365, -61448, -40745, -54910, -33817]
  a := ![1, -6, -1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![41338, 52860, 41371, -54910, -33817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44169, -56253, -41010, -49546, -33077]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-44169, -56253, -41010, -49546, -33077]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![46, 104, 1, 0, 0], ![6, 11, 0, 1, 0], ![74, 31, 0, 0, 1]] where
  M :=![![![-44169, -56253, -41010, -49546, -33077], ![-132308, -167802, -122407, -148174, -99092], ![-396368, -501981, -365986, -442998, -296348], ![-526542, -666949, -486135, -588247, -393452], ![-720750, -913287, -665723, -805500, -538701]]]
  hmulB := by decide  
  f := ![![![-31459, 43087, -38688, 31800, -7937]], ![![-31748, -46284, 27213, -93250, 63600]], ![![-41234, -26291, 10380, -73886, 55622]], ![![-8212, -571, -1376, -8201, 7356]], ![![-27492, 14083, -16412, -5122, 11867]]]
  g := ![![![42085, 53020, -41010, -49546, -33077], ![125874, 158388, -122407, -148174, -99092], ![376392, 473581, -365986, -442998, -296348], ![499822, 628980, -486135, -588247, -393452], ![684398, 861304, -665723, -805500, -538701]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [27, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 108], [0, 1]]
 g := ![![[105, 105], [75], [37, 34], [105, 81], [22], [108, 1]], ![[0, 4], [75], [3, 75], [24, 28], [22], [107, 108]]]
 h' := ![![[108, 108], [43, 43], [91, 27], [108, 19], [26, 100], [27, 83], [0, 1]], ![[0, 1], [0, 66], [64, 82], [89, 90], [35, 9], [53, 26], [108, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [54, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [27, 1, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8891, 10284, 8333, 9116, 6493]
  a := ![1, 26, 4, 18, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8345, -10623, 8333, 9116, 6493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![31459, -43087, 38688, -31800, 7937]] ![![-44169, -56253, -41010, -49546, -33077]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 33, 13, -8, -16]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-1, 33, 13, -8, -16]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![25, 34, 107, 1, 0], ![37, 101, 94, 0, 1]] where
  M :=![![![-1, 33, 13, -8, -16], ![-64, -12, 1, -6, -16], ![-64, -85, -44, -30, -12], ![8, -69, -55, -53, -22], ![-12, -55, -57, -74, -45]]]
  hmulB := by decide  
  f := ![![![-1, 5, -5, 8, -4]], ![![-16, -2, -3, -18, 16]], ![![64, -21, 30, 26, -36]], ![![55, -19, 26, 21, -30]], ![![39, -18, 21, 8, -17]]]
  g := ![![![7, 17, 21, -8, -16], ![6, 16, 19, -6, -16], ![10, 19, 38, -30, -12], ![19, 35, 68, -53, -22], ![31, 62, 107, -74, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [81, 71, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 93, 73], [71, 19, 40], [0, 1]]
 g := ![![[78, 63, 57], [65, 30], [22, 4], [24, 11], [82, 26, 7], [1]], ![[89, 75, 52, 42], [17, 104], [75, 49], [63, 64], [13, 39, 64, 54], [12, 71, 38, 71]], ![[21, 99, 21, 107], [108, 50], [34, 81], [3, 30], [110, 56, 17, 38], [107, 108, 21, 42]]]
 h' := ![![[10, 93, 73], [98, 37, 82], [39, 85, 16], [37, 19, 111], [25, 102, 24], [32, 42, 81], [0, 1]], ![[71, 19, 40], [29, 58, 78], [84, 57, 68], [31, 36, 106], [7, 87, 105], [28, 53, 85], [10, 93, 73]], ![[0, 1], [4, 18, 66], [86, 84, 29], [44, 58, 9], [93, 37, 97], [74, 18, 60], [71, 19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 103], []]
 b := ![[], [35, 64, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [81, 71, 32, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-717111, -385312, -628708, -469056, -286964]
  a := ![-1, -6, -4, 5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![191389, 394212, 677300, -469056, -286964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![917, 1394, 1028, 1192, 752]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![917, 1394, 1028, 1192, 752]] 
 ![![113, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![917, 1394, 1028, 1192, 752], ![3008, 3889, 2898, 3560, 2384], ![9536, 11850, 8657, 10564, 7120], ![12736, 15994, 11596, 13997, 9372], ![17240, 21906, 15920, 19188, 12805]]]
  hmulB := by decide  
  f := ![![![-99731, 53926, -61632, -14616, 40784]], ![![-24151, 12643, -14618, -4120, 10208]], ![![-56637, 32080, -36075, -6268, 22000]], ![![-80747, 42268, -48872, -13779, 34132]], ![![-41713, 23544, -26508, -4732, 16269]]]
  g := ![![![-2201, 1394, 1028, 1192, 752], ![-6467, 3889, 2898, 3560, 2384], ![-19317, 11850, 8657, 10564, 7120], ![-25711, 15994, 11596, 13997, 9372], ![-35237, 21906, 15920, 19188, 12805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17501, -14995, 7237, -36716, 26668]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-17501, -14995, 7237, -36716, 26668]] 
 ![![113, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![-17501, -14995, 7237, -36716, 26668], ![106672, -20312, 38341, 67810, -73432], ![-293728, 139391, -167176, -70182, 135620], ![217904, -187577, 186145, -65461, -33466], ![-120268, 162717, -146425, 118774, -28745]]]
  hmulB := by decide  
  f := ![![![-155413, -197455, -140341, -165364, -109376]], ![![-135904, -172798, -122911, -144906, -95848]], ![![-80474, -102271, -73000, -86390, -57236]], ![![-68006, -86211, -61643, -73141, -48538]], ![![-88969, -112838, -80676, -95702, -63497]]]
  g := ![![![10165, -14995, 7237, -36716, 26668], ![10274, -20312, 38341, 67810, -73432], ![-82256, 139391, -167176, -70182, 135620], ![115446, -187577, 186145, -65461, -33466], ![-101989, 162717, -146425, 118774, -28745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-1, 33, 13, -8, -16]] ![![917, 1394, 1028, 1192, 752]]
  ![![-155413, -197455, -140341, -165364, -109376]] where
 M := ![![![-155413, -197455, -140341, -165364, -109376]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-155413, -197455, -140341, -165364, -109376]] ![![-17501, -14995, 7237, -36716, 26668]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]] where
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [4, 62, 22, 74, 90, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 55, 97, 97, 123], [98, 108, 15, 76, 123], [31, 117, 82, 82, 34], [0, 100, 60, 126, 101], [0, 1]]
 g := ![![[23, 58, 90, 7, 84], [49, 63, 50, 75, 15], [68, 35, 34, 1, 103], [107, 101, 126, 66, 74], [25, 37, 1], []], ![[123, 48, 22, 44, 2, 58, 71, 43], [104, 35, 114, 31, 21, 37, 104, 63], [29, 45, 4, 10, 4, 87, 78, 126], [97, 111, 37, 101, 58, 104, 19, 92], [12, 96, 75, 115, 54, 99, 1, 91], [40, 59, 9, 85, 49, 63, 2, 63]], ![[66, 55, 77, 110, 50, 58, 39, 54], [88, 6, 120, 4, 113, 104, 60, 66], [98, 12, 104, 126, 59, 29, 72, 10], [21, 3, 69, 105, 110, 98, 80, 65], [111, 2, 26, 1, 22, 115, 85, 89], [22, 59, 82, 10, 29, 14, 10, 63]], ![[71, 49, 113, 78, 6, 58, 96, 62], [111, 47, 49, 12, 49, 89, 23, 79], [49, 25, 50, 24, 43, 33, 76, 72], [47, 31, 12, 16, 61, 26, 66, 73], [47, 45, 112, 59, 20, 98, 99, 103], [122, 120, 35, 79, 0, 34, 121, 61]], ![[0, 117, 19, 94, 122, 41, 78, 10], [24, 82, 37, 33, 19, 82, 61, 57], [73, 15, 81, 59, 86, 86, 17, 90], [71, 41, 15, 123, 89, 125, 38, 118], [32, 72, 59, 124, 27, 35, 109, 91], [22, 32, 57, 61, 16, 104, 59, 77]]]
 h' := ![![[35, 55, 97, 97, 123], [58, 82, 99, 13, 81], [109, 12, 91, 86, 74], [80, 41, 26, 0, 105], [27, 80, 73, 68, 70], [0, 0, 0, 1], [0, 1]], ![[98, 108, 15, 76, 123], [17, 25, 58, 78, 23], [4, 30, 34, 3, 4], [87, 108, 30, 17, 64], [24, 23, 55, 54, 55], [43, 19, 109, 125, 124], [35, 55, 97, 97, 123]], ![[31, 117, 82, 82, 34], [66, 116, 111, 85, 80], [5, 103, 30, 13, 89], [59, 51, 81, 123, 76], [68, 63, 38, 38, 98], [34, 120, 63, 115, 94], [98, 108, 15, 76, 123]], ![[0, 100, 60, 126, 101], [50, 68, 2, 42, 46], [51, 39, 124, 94, 23], [100, 75, 107, 26, 64], [88, 120, 39, 17, 105], [93, 83, 111, 25, 57], [31, 117, 82, 82, 34]], ![[0, 1], [31, 90, 111, 36, 24], [89, 70, 102, 58, 64], [97, 106, 10, 88, 72], [126, 95, 49, 77, 53], [39, 32, 98, 115, 106], [0, 100, 60, 126, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 124, 11, 108], [], [], []]
 b := ![[], [52, 107, 95, 103, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [4, 62, 22, 74, 90, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15289477676, 8865688644, -9868247472, -1426130244, 5808590364]
  a := ![0, -2, 4, -18, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-120389588, 69808572, -77702736, -11229372, 45736932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 33038369407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-212017, 176957, -177018, 55940, 36991]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-212017, 176957, -177018, 55940, 36991]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![81, 127, 85, 1, 0], ![58, 96, 109, 0, 1]] where
  M :=![![![-212017, 176957, -177018, 55940, 36991], ![147964, -296104, 250939, -280054, 111880], ![447520, 230729, -72344, 725638, -560108], ![-1194198, 418405, -570213, -492425, 669698], ![1265414, -645517, 753431, 239512, -548365]]]
  hmulB := by decide  
  f := ![![![-166589, -210657, -153624, -186086, -124563]], ![![-498252, -630862, -459783, -556374, -372172]], ![![-1488688, -1886581, -1375206, -1663910, -1112748]], ![![-1567073, -1985091, -1446982, -1750951, -1171121]], ![![-1698228, -2151510, -1568299, -1897686, -1269209]]]
  g := ![![![-52585, -79989, -68427, 55940, 36991], ![124758, 187254, 90539, -280054, 111880], ![-197274, -291259, -5342, 725638, -560108], ![-1147, -10188, -242070, -492425, 669698], ![104352, 164729, 306616, 239512, -548365]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [11, 5, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 45, 22], [111, 85, 109], [0, 1]]
 g := ![![[6, 117, 125], [105, 85, 129], [70, 16], [115, 1], [125, 12], [45, 1], []], ![[85, 55, 74, 85], [21, 29, 68, 124], [40, 75], [83, 45], [72, 49], [69, 20], [49, 91]], ![[71, 63, 110, 108], [2, 83, 16, 121], [85, 39], [16, 53], [93, 45], [73, 60], [93, 91]]]
 h' := ![![[65, 45, 22], [24, 123, 115], [81, 46, 103], [14, 114, 127], [121, 96, 130], [29, 26, 55], [0, 0, 1], [0, 1]], ![[111, 85, 109], [2, 122, 36], [78, 97, 73], [16, 76, 72], [55, 109, 62], [89, 119, 7], [18, 19, 85], [65, 45, 22]], ![[0, 1], [65, 17, 111], [99, 119, 86], [95, 72, 63], [3, 57, 70], [90, 117, 69], [32, 112, 45], [111, 85, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 85], []]
 b := ![[], [8, 30, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [11, 5, 86, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-224783, -86648, -258274, -75034, -168434]
  a := ![13, -6, -3, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![119253, 195514, 186862, -75034, -168434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166589, -210657, -153624, -186086, -124563]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-166589, -210657, -153624, -186086, -124563]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![84, 92, 1, 0, 0], ![66, 68, 0, 1, 0], ![26, 115, 0, 0, 1]] where
  M :=![![![-166589, -210657, -153624, -186086, -124563], ![-498252, -630862, -459783, -556374, -372172], ![-1488688, -1886581, -1375206, -1663910, -1112748], ![-1976370, -2504845, -1826147, -2209767, -1477824], ![-2706522, -3429623, -2500355, -3025784, -2023681]]]
  hmulB := by decide  
  f := ![![![-212017, 176957, -177018, 55940, 36991]], ![![147964, -296104, 250939, -280054, 111880]], ![![-28620, -92721, 62172, -155270, 98016]], ![![-39128, -61355, 36721, -120947, 81824]], ![![97472, -229745, 190908, -232918, 101371]]]
  g := ![![![215711, 312224, -153624, -186086, -124563], ![645196, 933606, -459783, -556374, -372172], ![1929604, 2791941, -1375206, -1663910, -1112748], ![2562504, 3707745, -1826147, -2209767, -1477824], ![3508708, 5076944, -2500355, -3025784, -2023681]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [63, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 130], [0, 1]]
 g := ![![[116, 52], [33, 81], [13], [107], [113], [129], [1]], ![[0, 79], [74, 50], [13], [107], [113], [129], [1]]]
 h' := ![![[28, 130], [17, 107], [15, 122], [110, 12], [63, 99], [34, 84], [68, 28], [0, 1]], ![[0, 1], [0, 24], [25, 9], [53, 119], [84, 32], [28, 47], [66, 103], [28, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [69, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [63, 103, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-209, 594, 23, -10, 855]
  a := ![-1, 0, 2, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-181, -757, 23, -10, 855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-212017, 176957, -177018, 55940, 36991]] ![![-166589, -210657, -153624, -186086, -124563]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32741, -46484, 41476, -35388, 9570]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![32741, -46484, 41476, -35388, 9570]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![8, 63, 86, 1, 0], ![134, 41, 102, 0, 1]] where
  M :=![![![32741, -46484, 41476, -35388, 9570], ![38280, 48399, -27344, 102092, -70776], ![-283104, 42252, -93153, -196240, 204184], ![389228, -208356, 238982, 59985, -160852], ![-340844, 239472, -251358, 27084, 95373]]]
  hmulB := by decide  
  f := ![![![2061, -1044, -696, 276, 974]], ![![3896, 2615, 904, 556, 552]], ![![2208, 5908, 3719, 2912, 1112]], ![![3300, 4877, 2736, 2133, 1028]], ![![4850, 4191, 2388, 2648, 1977]]]
  g := ![![![-7055, 13070, 15392, -35388, 9570], ![63544, -25413, -11592, 102092, -70776], ![-190320, 29444, -29513, -196240, 204184], ![156668, 19033, 83848, 59985, -160852], ![-97354, -39249, -89844, 27084, 95373]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [80, 31, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 84, 103], [117, 52, 34], [0, 1]]
 g := ![![[86, 75, 16], [15, 50], [116, 38], [106, 57, 39], [13, 9], [87, 1], []], ![[11, 32, 100, 38], [13, 119], [51, 99], [92, 121, 88, 115], [2, 18], [71, 101], [56, 60]], ![[99, 57, 17, 61], [40, 4], [106, 72], [5, 68, 20, 63], [129, 17], [28, 69], [125, 60]]]
 h' := ![![[107, 84, 103], [16, 79, 133], [95, 109, 119], [14, 99, 60], [100, 30, 54], [27, 100, 3], [0, 0, 1], [0, 1]], ![[117, 52, 34], [47, 58, 120], [26, 105, 16], [74, 126, 28], [9, 81, 7], [124, 113, 44], [119, 69, 52], [107, 84, 103]], ![[0, 1], [120, 0, 21], [13, 60, 2], [37, 49, 49], [56, 26, 76], [52, 61, 90], [127, 68, 84], [117, 52, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 6], []]
 b := ![[], [49, 2, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [80, 31, 50, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2464810, 2703114, 2202036, 2533368, 1570960]
  a := ![3, 10, 7, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1666502, -1615390, -2743836, 2533368, 1570960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247119, 313012, 228188, 276162, 184724]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![247119, 313012, 228188, 276162, 184724]] 
 ![![137, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![247119, 313012, 228188, 276162, 184724], ![738896, 936193, 682460, 825824, 552324], ![2209296, 2799504, 2040841, 2469568, 1651648], ![2933848, 3717580, 2710170, 3279577, 2193406], ![4017364, 5090404, 3710966, 4490664, 3003415]]]
  hmulB := by decide  
  f := ![![![556279, -528420, 511784, -236318, -45896]], ![![55506, -48263, 47772, -17348, -8140]], ![![302914, -303368, 290217, -150500, -12528]], ![![563852, -520660, 507714, -218655, -58450]], ![![85904, -92220, 86870, -51320, 1383]]]
  g := ![![![-463937, 313012, 228188, 276162, 184724], ![-1387398, 936193, 682460, 825824, 552324], ![-4148894, 2799504, 2040841, 2469568, 1651648], ![-5509672, 3717580, 2710170, 3279577, 2193406], ![-7544284, 5090404, 3710966, 4490664, 3003415]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0, 0, -1]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![1, -1, 0, 0, -1]] 
 ![![137, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![1, -1, 0, 0, -1], ![-4, 0, -3, -2, 0], ![0, -9, 0, -6, -4], ![-6, -5, -7, -3, -6], ![-10, -11, -7, -12, -3]]]
  hmulB := by decide  
  f := ![![![255, 63, -18, -34, 7]], ![![164, 42, -11, -22, 4]], ![![119, 30, -8, -16, 3]], ![![204, 49, -15, -27, 6]], ![![90, 21, -7, -12, 3]]]
  g := ![![![1, -1, 0, 0, -1], ![3, 0, -3, -2, 0], ![12, -9, 0, -6, -4], ![11, -5, -7, -3, -6], ![21, -11, -7, -12, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![32741, -46484, 41476, -35388, 9570]] ![![247119, 313012, 228188, 276162, 184724]]
  ![![2867, 3624, 2644, 3198, 2138]] where
 M := ![![![2867, 3624, 2644, 3198, 2138]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![2867, 3624, 2644, 3198, 2138]] ![![1, -1, 0, 0, -1]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-52197, -66171, -48224, -58362, -39045]]]
 hmul := by decide  
 g := ![![![![-381, -483, -352, -426, -285]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-305, -167, -13, 52, 22]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-305, -167, -13, 52, 22]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![102, 29, 65, 1, 0], ![42, 6, 29, 0, 1]] where
  M :=![![![-305, -167, -13, 52, 22], ![88, -244, -123, 18, 104], ![416, 87, -36, -38, 36], ![28, 311, 141, -9, -90], ![-224, 157, 127, 42, -61]]]
  hmulB := by decide  
  f := ![![![29, -33, 31, -20, 2]], ![![8, 42, -29, 66, -40]], ![![-160, 5, -38, -138, 132]], ![![-50, -14, 0, -65, 54]], ![![-26, -6, -1, -32, 27]]]
  g := ![![![-47, -13, -29, 52, 22], ![-44, -10, -31, 18, 104], ![20, 7, 10, -38, 36], ![34, 8, 24, -9, -90], ![-14, -5, -6, 42, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [110, 4, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 52, 134], [26, 86, 5], [0, 1]]
 g := ![![[49, 116, 4], [77, 123, 66], [47, 7], [92, 13, 24], [51, 80], [57, 1], []], ![[63, 5, 26, 58], [43, 62, 70, 134], [130, 117], [105, 82, 121, 48], [57, 122], [0, 29], [71, 25]], ![[71, 26, 115, 86], [2, 37, 120, 35], [85, 30], [123, 125, 74, 99], [82, 89], [94, 63], [61, 25]]]
 h' := ![![[31, 52, 134], [9, 111, 2], [7, 12, 109], [27, 54, 110], [36, 24, 21], [124, 79, 48], [0, 0, 1], [0, 1]], ![[26, 86, 5], [38, 36, 34], [129, 67, 1], [23, 78, 16], [121, 95, 18], [54, 23, 119], [101, 51, 86], [31, 52, 134]], ![[0, 1], [1, 131, 103], [83, 60, 29], [26, 7, 13], [19, 20, 100], [137, 37, 111], [82, 88, 52], [26, 86, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 54], []]
 b := ![[], [43, 128, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [110, 4, 82, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![161655, 185364, 133966, 180448, 91465]
  a := ![1, 4, 2, -2, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-158889, -40262, -102501, 180448, 91465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10515, 13453, 9841, 11912, 7950]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![10515, 13453, 9841, 11912, 7950]] 
 ![![139, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![10515, 13453, 9841, 11912, 7950], ![31800, 40218, 29353, 35582, 23824], ![95296, 120559, 87866, 106354, 71164], ![126428, 160231, 116767, 141239, 94442], ![172984, 219329, 159881, 193418, 129327]]]
  hmulB := by decide  
  f := ![![![247841, -140053, 157621, 27888, -96534]], ![![118468, -66092, 74713, 14522, -46824]], ![![183474, -106667, 118890, 16474, -69080]], ![![204604, -112761, 128013, 27015, -81974]], ![![82158, -48457, 53749, 6410, -30381]]]
  g := ![![![-26185, 13453, 9841, 11912, 7950], ![-78226, 40218, 29353, 35582, 23824], ![-234064, 120559, 87866, 106354, 71164], ![-310938, 160231, 116767, 141239, 94442], ![-425744, 219329, 159881, 193418, 129327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81055, 227812, -185888, 245020, -113624]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-81055, 227812, -185888, 245020, -113624]] 
 ![![139, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-81055, 227812, -185888, 245020, -113624], ![-454496, -135547, 564, -599024, 490040], ![1960160, -562916, 844533, 981208, -1198048], ![-2168848, 1361700, -1479788, -54003, 736188], ![1699624, -1415452, 1416756, -444088, -299023]]]
  hmulB := by decide  
  f := ![![![-623381, -770412, -543552, -641668, -427688]], ![![-371088, -459491, -324532, -383280, -255384]], ![![-633403, -784368, -554643, -655828, -437176]], ![![-323315, -400696, -284244, -337111, -224932]], ![![-166994, -207996, -148724, -177520, -118591]]]
  g := ![![![-43377, 227812, -185888, 245020, -113624], ![259524, -135547, 564, -599024, 490040], ![-710979, -562916, 844533, 981208, -1198048], ![523777, 1361700, -1479788, -54003, 736188], ![-286510, -1415452, 1416756, -444088, -299023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-305, -167, -13, 52, 22]] ![![10515, 13453, 9841, 11912, 7950]]
  ![![623381, 770412, 543552, 641668, 427688]] where
 M := ![![![623381, 770412, 543552, 641668, 427688]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![623381, 770412, 543552, 641668, 427688]] ![![-81055, 227812, -185888, 245020, -113624]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
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


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [137, 147, 32, 13, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 77, 140, 20, 40], [93, 131, 24, 83, 56], [11, 15, 111, 36, 139], [85, 74, 23, 10, 63], [0, 1]]
 g := ![![[108, 48, 22, 81, 102], [88, 20, 99, 120], [84, 84, 30, 95, 9], [55, 9, 130, 81], [141, 122, 12, 144, 1], [], []], ![[11, 37, 25, 70, 45, 70, 98, 60], [62, 88, 4, 104], [24, 129, 66, 14, 10, 117, 100, 56], [63, 136, 5, 76], [10, 142, 57, 78, 29, 51, 121, 32], [37, 92, 117, 39], [88, 3, 7, 110]], ![[69, 6, 52, 47, 44, 80, 116, 77], [120, 63, 107, 119], [105, 21, 125, 36, 137, 8, 92, 89], [58, 8, 137, 54], [14, 68, 89, 2, 82, 128, 47, 131], [148, 30, 45, 47], [35, 133, 23, 7]], ![[41, 54, 6, 100, 6, 5, 12, 8], [139, 42, 49, 9], [24, 114, 127, 64, 113, 40, 47, 137], [27, 107, 134, 30], [35, 53, 139, 83, 38, 87, 116, 105], [126, 10, 48, 16], [78, 2, 121, 100]], ![[11, 59, 136, 131, 81, 143, 53, 1], [105, 124, 33, 39], [124, 60, 110, 16, 26, 39, 82, 19], [0, 50, 19, 49], [113, 33, 6, 143, 20, 15, 137, 103], [9, 103, 28, 100], [48, 73, 40, 95]]]
 h' := ![![[104, 77, 140, 20, 40], [46, 87, 83, 56, 129], [114, 109, 82, 112, 57], [42, 87, 114, 76, 146], [53, 107, 48, 38, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[93, 131, 24, 83, 56], [32, 53, 69, 103, 134], [35, 118, 72, 148, 36], [44, 70, 142, 50, 43], [35, 44, 41, 12, 134], [66, 42, 43, 94, 57], [101, 136, 139, 37, 121], [104, 77, 140, 20, 40]], ![[11, 15, 111, 36, 139], [125, 131, 91, 56, 13], [18, 96, 141, 40, 87], [129, 145, 121, 125, 50], [124, 52, 9, 83, 59], [90, 141, 67, 62, 81], [129, 106, 38, 10, 14], [93, 131, 24, 83, 56]], ![[85, 74, 23, 10, 63], [74, 104, 118, 60, 124], [55, 132, 26, 34, 146], [114, 95, 142, 28, 39], [45, 64, 58, 120, 103], [69, 50, 48, 97, 8], [14, 63, 137, 16, 4], [11, 15, 111, 36, 139]], ![[0, 1], [103, 72, 86, 23, 47], [83, 141, 126, 113, 121], [148, 50, 77, 19, 20], [44, 31, 142, 45, 142], [86, 65, 140, 45, 2], [53, 142, 132, 86, 10], [85, 74, 23, 10, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 38, 108, 43], [], [], []]
 b := ![[], [88, 61, 116, 80, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [137, 147, 32, 13, 5, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5369513, -5151079, -4285389, -5490948, -2328572]
  a := ![4, -1, -1, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36037, -34571, -28761, -36852, -15628]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47065, 57913, 41890, 50788, 34229]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![47065, 57913, 41890, 50788, 34229]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![147, 7, 55, 1, 0], ![69, 94, 74, 0, 1]] where
  M :=![![![47065, 57913, 41890, 50788, 34229], ![136916, 173972, 126371, 152238, 101576], ![406304, 517101, 377124, 455894, 304476], ![540494, 684913, 499841, 605481, 405106], ![741754, 938475, 684377, 828828, 554693]]]
  hmulB := by decide  
  f := ![![![27025, -25873, 25012, -11762, -2069]], ![![-8276, 38206, -30011, 45886, -23524]], ![![-94096, -15925, -8842, -107070, 91772]], ![![-7105, -29735, 20392, -47925, 29691]], ![![-40151, 4862, -12377, -29410, 29860]]]
  g := ![![![-64772, -23279, -34996, 50788, 34229], ![-193714, -69138, -104393, 152238, 101576], ![-580258, -207251, -312770, 455894, 304476], ![-770977, -275718, -415758, 605481, 405106], ![-1055429, -377513, -569195, 828828, 554693]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [131, 105, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 105, 28], [26, 45, 123], [0, 1]]
 g := ![![[119, 49, 80], [61, 94, 47], [85, 2, 100], [104, 137], [22, 73, 25], [141, 1], []], ![[145, 11, 50, 114], [124, 52, 14, 53], [46, 34, 6, 114], [45, 105], [80, 30, 88, 106], [133, 62], [3, 29]], ![[91, 127, 25, 39], [26, 52, 94, 37], [40, 24, 93, 59], [84, 88], [23, 118, 60, 62], [35, 2], [59, 29]]]
 h' := ![![[115, 105, 28], [12, 16, 69], [39, 129, 97], [135, 116, 141], [138, 41, 99], [102, 13, 146], [0, 0, 1], [0, 1]], ![[26, 45, 123], [135, 98, 80], [87, 77, 125], [66, 117, 80], [26, 105, 16], [102, 90, 139], [148, 104, 45], [115, 105, 28]], ![[0, 1], [142, 37, 2], [111, 96, 80], [144, 69, 81], [124, 5, 36], [69, 48, 17], [44, 47, 105], [26, 45, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 19], []]
 b := ![[], [133, 144, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [131, 105, 10, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145806913, -179608280, -135492080, -158597220, -108398148]
  a := ![7, -46, -24, -23, -71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![202963289, 73642372, 109992172, -158597220, -108398148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27025, 25873, -25012, 11762, 2069]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-27025, 25873, -25012, 11762, 2069]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![2, 41, 1, 0, 0], ![110, 67, 0, 1, 0], ![84, 41, 0, 0, 1]] where
  M :=![![![-27025, 25873, -25012, 11762, 2069], ![8276, -38206, 30011, -45886, 23524], ![94096, 15925, 8842, 107070, -91772], ![-187682, 78221, -98815, -59987, 95308], ![186478, -106485, 119413, 19436, -71749]]]
  hmulB := by decide  
  f := ![![![-47065, -57913, -41890, -50788, -34229]], ![![-136916, -173972, -126371, -152238, -101576]], ![![-40490, -51429, -37365, -45028, -30050]], ![![-98616, -123917, -89898, -108557, -72688]], ![![-68270, -85669, -62148, -75078, -50295]]]
  g := ![![![-9567, 1182, -25012, 11762, 2069], ![19998, 5571, 30011, -45886, 23524], ![-26440, -24885, 8842, 107070, -91772], ![-9254, 28087, -98815, -59987, 95308], ![25408, -22271, 119413, 19436, -71749]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [112, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 150], [0, 1]]
 g := ![![[141, 32], [9, 123], [22, 50], [127], [70, 44], [43], [1]], ![[43, 119], [57, 28], [1, 101], [127], [124, 107], [43], [1]]]
 h' := ![![[63, 150], [49, 118], [103, 24], [114, 79], [12, 60], [27, 73], [39, 63], [0, 1]], ![[0, 1], [84, 33], [105, 127], [108, 72], [17, 91], [96, 78], [82, 88], [63, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [124, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [112, 88, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7097, 8358, 5262, 8299, 2579]
  a := ![1, -12, -7, -5, -22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7503, -5756, 5262, 8299, 2579]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![47065, 57913, 41890, 50788, 34229]] ![![-27025, 25873, -25012, 11762, 2069]]
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


lemma PB307I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB307I3 : PrimesBelowBoundCertificateInterval O 103 151 307 where
  m := 9
  g := ![3, 2, 3, 1, 2, 3, 3, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB307I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1, I139N2]
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
    · exact ![11449, 11449, 107]
    · exact ![1295029, 11881]
    · exact ![1442897, 113, 113]
    · exact ![33038369407]
    · exact ![2248091, 17161]
    · exact ![2571353, 137, 137]
    · exact ![2685619, 139, 139]
    · exact ![73439775749]
    · exact ![3442951, 22801]
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N2, I113N1, I113N2, I137N1, I137N2, I139N1, I139N2]
  Il := ![[I107N2], [], [I113N1, I113N2], [], [], [I137N1, I137N2], [I139N1, I139N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
