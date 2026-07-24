
import IdealArithmetic.Examples.NF5_1_9000000_1.RI5_1_9000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12465, -5719, -3600, -4616, 562]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![12465, -5719, -3600, -4616, 562]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![103, 48, 1, 0, 0], ![85, 102, 0, 1, 0], ![35, 23, 0, 0, 1]] where
  M :=![![![12465, -5719, -3600, -4616, 562], ![2248, -2053, -2206, -17556, -28820], ![-57640, 25695, 15503, 9058, -23848], ![-48820, 24788, 17740, 57187, 65432], ![39932, -17847, -10810, -7026, 15223]]]
  hmulB := by decide  
  f := ![![![-240565, -104873, -74006, -50676, -87782]], ![![-351128, -152577, -108394, -73800, -128492]], ![![-391489, -170434, -120601, -82390, -143010]], ![![-525919, -228813, -162146, -110633, -192258]], ![![-153865, -66963, -47416, -32374, -56223]]]
  g := ![![![7065, 5841, -3600, -4616, 562], ![25518, 23901, -2206, -17556, -28820], ![-14857, -10223, 15503, 9058, -23848], ![-84365, -76306, 17740, 57187, 65432], ![11381, 8108, -10810, -7026, 15223]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [9, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 106], [0, 1]]
 g := ![![[30, 12], [10, 4], [30], [44, 23], [41], [51, 1]], ![[0, 95], [0, 103], [30], [40, 84], [41], [102, 106]]]
 h' := ![![[51, 106], [17, 71], [5, 2], [32, 43], [57, 68], [76, 24], [0, 1]], ![[0, 1], [0, 36], [0, 105], [85, 64], [101, 39], [16, 83], [51, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [90, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [9, 56, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-715, -132, 513, 84, -444]
  a := ![0, -7, 2, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-422, -216, 513, 84, -444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3015, 1311, 928, 634, 1100]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![3015, 1311, 928, 634, 1100]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![1, 56, 1, 0, 0], ![51, 75, 0, 1, 0], ![101, 47, 0, 0, 1]] where
  M :=![![![3015, 1311, 928, 634, 1100], ![4400, 1911, 1354, 924, 1604], ![3208, 1395, 987, 674, 1168], ![136, 64, 44, 31, 52], ![-408, -179, -126, -86, -149]]]
  hmulB := by decide  
  f := ![![![13, -15, 10, -14, 8]], ![![32, -29, -2, -24, -100]], ![![15, -14, -1, -12, -52]], ![![29, -28, 4, -23, -64]], ![![27, -27, 8, -24, -37]]]
  g := ![![![-1321, -1401, 928, 634, 1100], ![-1926, -2043, 1354, 924, 1604], ![-1403, -1489, 987, 674, 1168], ![-63, -67, 44, 31, 52], ![179, 190, -126, -86, -149]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [95, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 106], [0, 1]]
 g := ![![[26, 69], [94, 102], [52], [0, 41], [89], [98, 1]], ![[47, 38], [32, 5], [52], [59, 66], [89], [89, 106]]]
 h' := ![![[98, 106], [58, 60], [89, 67], [0, 65], [106, 83], [106, 93], [0, 1]], ![[0, 1], [53, 47], [21, 40], [57, 42], [1, 24], [18, 14], [98, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [92, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [95, 9, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33581, 12937, 18662, 16854, 6250]
  a := ![3, -62, -1, -63, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14421, -24205, 18662, 16854, 6250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 28, 19, 14, 11]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![25, 28, 19, 14, 11]] 
 ![![107, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![25, 28, 19, 14, 11], ![44, 39, 28, 44, 62], ![124, -13, -5, 10, 70], ![118, -55, -37, -87, -71], ![-60, 21, 12, 0, -37]]]
  hmulB := by decide  
  f := ![![![2523, -2018, 301, -580, -949]], ![![106, -71, -10, -20, -68]], ![![2069, -1675, 280, -482, -737]], ![![1325, -1061, 160, -305, -496]], ![![663, -529, 77, -152, -252]]]
  g := ![![![-27, 28, 19, 14, 11], ![-64, 39, 28, 44, 62], ![-19, -13, -5, 10, 70], ![97, -55, -37, -87, -71], ![-1, 21, 12, 0, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![12465, -5719, -3600, -4616, 562]] ![![3015, 1311, 928, 634, 1100]]
  ![![12503, -5416, -3122, 626, 9654]] where
 M := ![![![12503, -5416, -3122, 626, 9654]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![12503, -5416, -3122, 626, 9654]] ![![25, 28, 19, 14, 11]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-818229, 347750, 194205, -148944, -818443]]]
 hmul := by decide  
 g := ![![![![-7647, 3250, 1815, -1392, -7649]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13785, 5993, 4243, 2898, 5027]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![13785, 5993, 4243, 2898, 5027]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![36, 84, 1, 0, 0], ![28, 102, 0, 1, 0], ![14, 86, 0, 0, 1]] where
  M :=![![![13785, 5993, 4243, 2898, 5027], ![20108, 8743, 6190, 4228, 7334], ![14668, 6376, 4515, 3084, 5350], ![646, 279, 197, 135, 235], ![-1872, -814, -576, -394, -683]]]
  hmulB := by decide  
  f := ![![![53, -41, 5, 0, -11]], ![![-44, 91, -82, 32, 22]], ![![-16, 56, -61, 24, 14]], ![![-26, 73, -75, 29, 15]], ![![-30, 68, -64, 26, 17]]]
  g := ![![![-2665, -9893, 4243, 2898, 5027], ![-3888, -14433, 6190, 4228, 7334], ![-2836, -10528, 4515, 3084, 5350], ![-124, -461, 197, 135, 235], ![362, 1344, -576, -394, -683]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [66, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 108], [0, 1]]
 g := ![![[60, 38], [25], [2, 7], [107, 100], [89], [73, 1]], ![[0, 71], [25], [77, 102], [104, 9], [89], [37, 108]]]
 h' := ![![[73, 108], [78, 93], [86, 104], [23, 15], [60, 10], [87, 31], [0, 1]], ![[0, 1], [0, 16], [48, 5], [28, 94], [27, 99], [61, 78], [73, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [57, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [66, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-497, 41, 276, 5, -327]
  a := ![1, -6, 1, -7, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-55, 41, 276, 5, -327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15887, -6907, -4890, -3340, -5794]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-15887, -6907, -4890, -3340, -5794]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![17, 87, 1, 0, 0], ![47, 70, 0, 1, 0], ![102, 73, 0, 0, 1]] where
  M :=![![![-15887, -6907, -4890, -3340, -5794], ![-23176, -10075, -7134, -4872, -8452], ![-16904, -7349, -5203, -3554, -6164], ![-740, -324, -228, -157, -272], ![2156, 939, 664, 454, 787]]]
  hmulB := by decide  
  f := ![![![-51, 37, -8, 8, -38]], ![![-152, 71, 58, 76, 124]], ![![-127, 61, 45, 62, 94]], ![![-117, 61, 32, 51, 62]], ![![-150, 82, 32, 58, 47]]]
  g := ![![![7479, 9865, -4890, -3340, -5794], ![10910, 14391, -7134, -4872, -8452], ![7957, 10496, -5203, -3554, -6164], ![351, 462, -228, -157, -272], ![-1016, -1340, 664, 454, 787]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [35, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 108], [0, 1]]
 g := ![![[42, 81], [83], [45, 71], [84, 61], [3], [56, 1]], ![[0, 28], [83], [97, 38], [12, 48], [3], [3, 108]]]
 h' := ![![[56, 108], [41, 9], [60, 44], [3, 17], [8, 37], [2, 49], [0, 1]], ![[0, 1], [0, 100], [17, 65], [83, 92], [9, 72], [21, 60], [56, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [108, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [35, 53, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2819, 1505, 3469, 5698, 8079]
  a := ![1, 25, -3, 24, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10584, -11825, 3469, 5698, 8079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -99, -45, -40, -83]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-81, -99, -45, -40, -83]] 
 ![![109, 0, 0, 0, 0], ![94, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![104, 0, 0, 0, 1]] where
  M :=![![![-81, -99, -45, -40, -83], ![-332, 43, -118, -4, -74], ![-148, -118, 47, -48, 62], ![290, -213, -11, -61, -169], ![-148, 128, 8, 38, 97]]]
  hmulB := by decide  
  f := ![![![3451, -1745, -1243, -3922, -4417]], ![![2814, -1435, -1032, -3396, -3944]], ![![1345, -689, -498, -1674, -1973]], ![![2263, -1116, -772, -2109, -2096]], ![![3472, -1750, -1242, -3854, -4285]]]
  g := ![![![208, -99, -45, -40, -83], ![88, 43, -118, -4, -74], ![47, -118, 47, -48, 62], ![388, -213, -11, -61, -169], ![-230, 128, 8, 38, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![13785, 5993, 4243, 2898, 5027]] ![![-15887, -6907, -4890, -3340, -5794]]
  ![![-420926043, -182992876, -129561857, -88492146, -153508985]] where
 M := ![![![-420926043, -182992876, -129561857, -88492146, -153508985]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-420926043, -182992876, -129561857, -88492146, -153508985]] ![![-81, -99, -45, -40, -83]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![111080406591, 48290960733, 34190765750, 23352661836, 40510300388]]]
 hmul := by decide  
 g := ![![![![1019086299, 443036337, 313676750, 214244604, 371654132]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [77, 103, 76, 60, 55, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 106, 85, 8, 76], [76, 80, 102, 109, 12], [30, 31, 20, 65, 67], [2, 8, 19, 44, 71], [0, 1]]
 g := ![![[30, 25, 56, 15, 8], [44, 37, 48, 30], [85, 11, 26, 104], [75, 96, 13, 15], [27, 58, 1], []], ![[88, 9, 105, 24, 74, 82, 102, 73], [45, 24, 79, 61], [4, 31, 57, 72], [79, 49, 51, 53], [88, 104, 13, 76, 1, 93, 12, 71], [22, 74, 13, 56, 73, 77, 99, 84]], ![[56, 37, 20, 4, 108, 82, 30, 6], [17, 54, 7, 98], [65, 13, 1, 72], [44, 82], [92, 106, 17, 93, 44, 96, 85, 12], [46, 32, 45, 73, 95, 112, 73, 33]], ![[31, 100, 74, 33, 57, 98, 112, 73], [103, 0, 54, 112], [28, 64, 16, 88], [44, 24, 78, 82], [71, 16, 86, 79, 100, 84, 56, 79], [56, 55, 27, 91, 18, 89, 49, 70]], ![[72, 62, 92, 38, 37, 51, 6, 67], [102, 22, 109, 1], [39, 67, 28, 63], [50, 50, 15, 56], [81, 56, 16, 95, 35, 25, 0, 3], [10, 26, 15, 73, 66, 61, 15, 40]]]
 h' := ![![[63, 106, 85, 8, 76], [6, 93, 71, 108, 11], [111, 109, 42, 46, 16], [92, 19, 102, 99, 45], [68, 98, 33, 84, 44], [0, 0, 0, 1], [0, 1]], ![[76, 80, 102, 109, 12], [95, 83, 67, 84, 36], [82, 80, 22, 78, 93], [27, 1, 69, 47, 80], [102, 39, 94, 82, 36], [92, 104, 50, 14, 29], [63, 106, 85, 8, 76]], ![[30, 31, 20, 65, 67], [33, 4, 81, 50, 31], [72, 34, 58, 84, 18], [52, 20, 60, 41, 80], [29, 12, 7, 67], [45, 99, 80, 83, 1], [76, 80, 102, 109, 12]], ![[2, 8, 19, 44, 71], [28, 95, 20, 34, 84], [7, 22, 32, 49, 98], [4, 47, 82, 52, 38], [62, 9, 27, 99, 46], [88, 21, 9, 0, 72], [30, 31, 20, 65, 67]], ![[0, 1], [25, 64, 100, 63, 64], [46, 94, 72, 82, 1], [87, 26, 26, 100, 96], [78, 68, 65, 7, 100], [29, 2, 87, 15, 11], [2, 8, 19, 44, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 2, 107, 95], [], [], []]
 b := ![[], [1, 42, 54, 40, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [77, 103, 76, 60, 55, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1386343664, -739461039, -92893571, 829759, 1537820277]
  a := ![-1, -7, 5, -5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12268528, -6543903, -822067, 7343, 13609029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 18424351793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267, 120, 74, 62, -76]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-267, 120, 74, 62, -76]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![36, 122, 1, 0, 0], ![53, 57, 0, 1, 0], ![30, 20, 0, 0, 1]] where
  M :=![![![-267, 120, 74, 62, -76], ![-304, 159, 116, 424, 524], ![1048, -456, -265, 16, 748], ![1648, -794, -530, -1209, -962], ![-740, 324, 188, 8, -493]]]
  hmulB := by decide  
  f := ![![![12947, 5652, 3978, 2730, 4720]], ![![18880, 8225, 5844, 3976, 6940]], ![![21916, 9550, 6775, 4616, 8044]], ![![13881, 6053, 4284, 2925, 5086]], ![![6018, 2624, 1856, 1268, 2203]]]
  g := ![![![-31, -86, 74, 62, -76], ![-336, -383, 116, 424, 524], ![-100, 126, -265, 16, 748], ![895, 1197, -530, -1209, -962], ![54, -104, 188, 8, -493]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [15, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 126], [0, 1]]
 g := ![![[11, 17], [5, 44], [45, 13], [24, 1], [108, 8], [89, 1]], ![[0, 110], [111, 83], [59, 114], [113, 126], [58, 119], [51, 126]]]
 h' := ![![[89, 126], [52, 115], [87, 60], [21, 34], [31, 1], [62, 32], [0, 1]], ![[0, 1], [0, 12], [93, 67], [126, 93], [120, 126], [116, 95], [89, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [42, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [15, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6735, -3500, -2232, -3704, -4680]
  a := ![0, -4, -2, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3337, 4516, -2232, -3704, -4680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 25, -150, 10, -234]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![91, 25, -150, 10, -234]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![5, 22, 1, 0, 0], ![17, 27, 0, 1, 0], ![78, 121, 0, 0, 1]] where
  M :=![![![91, 25, -150, 10, -234], ![-936, 663, 30, 188, 528], ![1056, -1057, 475, -310, 36], ![540, 70, -762, 35, -1230], ![-336, -7, 414, -10, 691]]]
  hmulB := by decide  
  f := ![![![685, 215, 156, 98, 234]], ![![936, 335, 234, 40, 120]], ![![191, 70, 49, 12, 30]], ![![287, 102, 72, 25, 60]], ![![1314, 450, 318, 98, 259]]]
  g := ![![![149, 247, -150, 10, -234], ![-358, -543, 30, 188, 528], ![9, -59, 475, -310, 36], ![785, 1297, -762, 35, -1230], ![-442, -728, 414, -10, 691]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [47, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 126], [0, 1]]
 g := ![![[45, 100], [58, 16], [74, 117], [115, 81], [97, 2], [44, 1]], ![[0, 27], [0, 111], [15, 10], [123, 46], [58, 125], [88, 126]]]
 h' := ![![[44, 126], [68, 10], [78, 4], [56, 25], [13, 9], [91, 111], [0, 1]], ![[0, 1], [0, 117], [0, 123], [13, 102], [28, 118], [22, 16], [44, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [7, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [47, 83, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2099, -1467, 797, -70, -1191]
  a := ![13, -7, 4, -6, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![726, 1000, 797, -70, -1191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1291, -492, -220, 1164, 2898]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![1291, -492, -220, 1164, 2898]] 
 ![![127, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![1291, -492, -220, 1164, 2898], ![11592, -5295, -3312, -3908, 1188], ![2376, -1550, -1387, -8408, -12912], ![-31620, 14102, 8514, 5071, -12906], ![-1136, 840, 814, 5640, 8975]]]
  hmulB := by decide  
  f := ![![![580525, 251732, 178808, 121820, 211650]], ![![431775, 187237, 132984, 90608, 157410]], ![![265395, 115106, 81749, 55700, 96774]], ![![443623, 192342, 136646, 93083, 161736]], ![![374198, 162276, 115254, 78528, 136427]]]
  g := ![![![-2291, -492, -220, 1164, 2898], ![7673, -5295, -3312, -3908, 1188], ![16535, -1550, -1387, -8408, -12912], ![-9937, 14102, 8514, 5071, -12906], ![-11092, 840, 814, 5640, 8975]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-267, 120, 74, 62, -76]] ![![91, 25, -150, 10, -234]]
  ![![543, -461, 92, -120, -274]] where
 M := ![![![543, -461, 92, -120, -274]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![543, -461, 92, -120, -274]] ![![1291, -492, -220, 1164, 2898]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-318643, 108839, 35052, -493776, -1072388]]]
 hmul := by decide  
 g := ![![![![-2509, 857, 276, -3888, -8444]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -36, -9, -10, -41]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![57, -36, -9, -10, -41]] 
 ![![131, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![57, -36, -9, -10, -41], ![-164, 151, -52, 44, 22], ![44, -97, 107, -30, 110], ![302, -195, -41, -55, -211], ![-172, 113, 20, 32, 115]]]
  hmulB := by decide  
  f := ![![![7619, 3326, 2353, 1588, 2743]], ![![898, 393, 278, 188, 324]], ![![1981, 865, 612, 414, 715]], ![![1402, 609, 431, 291, 505]], ![![6797, 2967, 2099, 1416, 2446]]]
  g := ![![![45, -36, -9, -10, -41], ![-32, 151, -52, 44, 22], ![-109, -97, 107, -30, 110], ![232, -195, -41, -55, -211], ![-127, 113, 20, 32, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -27, 17, -8, 9]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![23, -27, 17, -8, 9]] 
 ![![131, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![23, -27, 17, -8, 9], ![36, -3, -38, 0, -66], ![-132, 98, -3, 28, 66], ![114, -137, 89, -41, 51], ![-60, 74, -50, 22, -31]]]
  hmulB := by decide  
  f := ![![![541, 329, 229, 178, 237]], ![![127, 76, 53, 42, 57]], ![![166, 96, 67, 52, 72]], ![![102, 59, 41, 29, 39]], ![![38, 26, 18, 14, 17]]]
  g := ![![![2, -27, 17, -8, 9], ![17, -3, -38, 0, -66], ![-32, 98, -3, 28, 66], ![9, -137, 89, -41, 51], ![-4, 74, -50, 22, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, -123, -88, -60, -102]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-293, -123, -88, -60, -102]] 
 ![![131, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-293, -123, -88, -60, -102], ![-408, -195, -126, -92, -156], ![-312, -125, -103, -62, -120], ![-36, 8, 0, 1, 12], ![52, 9, 10, 6, 5]]]
  hmulB := by decide  
  f := ![![![-919, 403, 238, 40, -558]], ![![-459, 202, 120, 32, -258]], ![![-302, 133, 79, 22, -168]], ![![-118, 50, 28, -23, -120]], ![![-450, 197, 116, 14, -283]]]
  g := ![![![148, -123, -88, -60, -102], ![227, -195, -126, -92, -156], ![163, -125, -103, -62, -120], ![-10, 8, 0, 1, 12], ![-11, 9, 10, 6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2

def I131N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -4, -4, -2, 6]] i)))

def SI131N3: IdealEqSpanCertificate' Table ![![11, -4, -4, -2, 6]] 
 ![![131, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![11, -4, -4, -2, 6], ![24, -15, -4, -24, -24], ![-48, 22, 9, -4, -48], ![-108, 56, 28, 65, 48], ![44, -22, -8, 0, 25]]]
  hmulB := by decide  
  f := ![![![98953, 43016, 30460, 20802, 36090]], ![![54733, 23793, 16848, 11506, 19962]], ![![26486, 11514, 8153, 5568, 9660]], ![![1546, 672, 476, 325, 564]], ![![5185, 2254, 1596, 1090, 1891]]]
  g := ![![![3, -4, -4, -2, 6], ![11, -15, -4, -24, -24], ![-12, 22, 9, -4, -48], ![-42, 56, 28, 65, 48], ![13, -22, -8, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N3 : Nat.card (O ⧸ I131N3) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N3)

lemma isPrimeI131N3 : Ideal.IsPrime I131N3 := prime_ideal_of_norm_prime hp131.out _ NI131N3

def I131N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -15, -11, -48, -65]] i)))

def SI131N4: IdealEqSpanCertificate' Table ![![27, -15, -11, -48, -65]] 
 ![![131, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![27, -15, -11, -48, -65], ![-260, 115, 66, 12, -158], ![-316, 152, 103, 236, 194], ![518, -219, -117, 139, 593], ![204, -98, -68, -162, -139]]]
  hmulB := by decide  
  f := ![![![391865, 170369, 120609, 82386, 142903]], ![![258627, 112442, 79601, 54374, 94315]], ![![365135, 158747, 112382, 76766, 133155]], ![![164663, 71590, 50680, 34619, 60048]], ![![197022, 85658, 60640, 41422, 71849]]]
  g := ![![![73, -15, -11, -48, -65], ![-63, 115, 66, 12, -158], ![-393, 152, 103, 236, 194], ![-103, -219, -117, 139, 593], ![266, -98, -68, -162, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N4 : Nat.card (O ⧸ I131N4) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N4)

lemma isPrimeI131N4 : Ideal.IsPrime I131N4 := prime_ideal_of_norm_prime hp131.out _ NI131N4
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![57, -36, -9, -10, -41]] ![![23, -27, 17, -8, 9]]
  ![![2523, -3977, 3524, -1200, 3056]] where
 M := ![![![2523, -3977, 3524, -1200, 3056]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![2523, -3977, 3524, -1200, 3056]] ![![-293, -123, -88, -60, -102]]
  ![![-13999, 42590, -53334, 13152, -58934]] where
 M := ![![![-13999, 42590, -53334, 13152, -58934]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N2 : IdealMulLeCertificate' Table 
  ![![-13999, 42590, -53334, 13152, -58934]] ![![11, -4, -4, -2, 6]]
  ![![-585309, 276858, 245358, 74054, 611824]] where
 M := ![![![-585309, 276858, 245358, 74054, 611824]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N3 : IdealMulLeCertificate' Table 
  ![![-585309, 276858, 245358, 74054, 611824]] ![![27, -15, -11, -48, -65]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-2147483, 1736143, -285449, 499634, 771459]]]
 hmul := by decide  
 g := ![![![![-16393, 13253, -2179, 3814, 5889]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2, I131N3, I131N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
    exact isPrimeI131N3
    exact isPrimeI131N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1 ⊙ MulI131N2 ⊙ MulI131N3)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [106, 81, 24, 82, 132, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 57, 34, 135, 34], [62, 84, 107, 8, 33], [54, 14, 50, 101, 111], [46, 118, 83, 30, 96], [0, 1]]
 g := ![![[101, 59, 10, 96, 30], [2, 119, 126, 123], [49, 82, 133, 61], [17, 93, 12, 42, 122], [103, 80, 5, 1], [], []], ![[27, 117, 69, 72, 13, 67, 17, 60], [22, 54, 101, 78], [130, 4, 75, 38], [73, 59, 94, 45, 80, 76, 111, 22], [23, 47, 102, 22], [110, 101, 100, 16], [71, 134, 27, 60]], ![[93, 28, 52, 52, 118, 90, 18, 85], [51, 81, 16, 112], [87, 133, 13, 87], [35, 93, 61, 54, 102, 17, 25, 41], [13, 77, 93, 7], [99, 104, 111, 61], [13, 27, 82, 130]], ![[126, 13, 96, 9, 136, 21, 125, 52], [100, 121, 22, 32], [132, 20, 6, 69], [64, 76, 61, 127, 54, 83, 106, 24], [8, 131, 98, 120], [67, 71, 125, 14], [26, 75, 46, 128]], ![[119, 135, 12, 46, 107, 24, 1, 114], [25, 52, 68, 44], [130, 23, 32, 126], [19, 100, 131, 64, 115, 69, 46, 33], [11, 89, 88, 64], [114, 86, 0, 121], [68, 98, 54, 37]]]
 h' := ![![[117, 57, 34, 135, 34], [45, 45, 84, 60, 116], [42, 14, 105, 37, 73], [116, 119, 126, 121, 91], [42, 28, 108, 83, 56], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[62, 84, 107, 8, 33], [115, 134, 15, 36, 50], [23, 41, 41, 34, 30], [68, 102, 65, 39, 60], [12, 98, 106, 50, 7], [126, 2, 134, 101, 61], [135, 96, 32, 71, 4], [117, 57, 34, 135, 34]], ![[54, 14, 50, 101, 111], [57, 84, 107, 0, 84], [95, 58, 89, 40, 48], [136, 16, 88, 61, 19], [3, 101, 134, 76, 61], [55, 0, 47, 9, 125], [0, 62, 91, 120, 46], [62, 84, 107, 8, 33]], ![[46, 118, 83, 30, 96], [116, 21, 0, 21, 51], [21, 91, 51, 79, 13], [54, 70, 103, 20, 84], [120, 123, 53, 24, 72], [3, 91, 37, 81, 95], [23, 87, 49, 124, 98], [54, 14, 50, 101, 111]], ![[0, 1], [21, 127, 68, 20, 110], [43, 70, 125, 84, 110], [64, 104, 29, 33, 20], [84, 61, 10, 41, 78], [90, 44, 56, 83, 129], [114, 29, 101, 96, 126], [46, 118, 83, 30, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 55, 4, 60], [], [], []]
 b := ![[], [8, 54, 24, 47, 103], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [106, 81, 24, 82, 132, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9161738, -5087084, -2210084, -5730436, -6676284]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![66874, -37132, -16132, -41828, -48732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1287, -558, -395, -270, -467]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1287, -558, -395, -270, -467]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![107, 136, 1, 0, 0], ![43, 45, 0, 1, 0], ![38, 106, 0, 0, 1]] where
  M :=![![![-1287, -558, -395, -270, -467], ![-1868, -821, -576, -396, -686], ![-1372, -589, -425, -286, -502], ![-70, -21, -15, -11, -13], ![180, 73, 52, 36, 59]]]
  hmulB := by decide  
  f := ![![![67, -32, -21, -48, -31]], ![![-124, 43, 32, -76, -226]], ![![-73, 19, 16, -110, -245]], ![![-19, 4, 4, -37, -78]], ![![-74, 23, 18, -72, -181]]]
  g := ![![![506, 826, -395, -270, -467], ![740, 1209, -576, -396, -686], ![543, 887, -425, -286, -502], ![18, 28, -15, -11, -13], ![-66, -107, 52, 36, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [128, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 138], [0, 1]]
 g := ![![[40, 44], [118, 35], [121], [137, 55], [20], [112], [1]], ![[79, 95], [89, 104], [121], [12, 84], [20], [112], [1]]]
 h' := ![![[23, 138], [47, 105], [8, 70], [117, 128], [60, 74], [102, 24], [11, 23], [0, 1]], ![[0, 1], [99, 34], [89, 69], [3, 11], [94, 65], [98, 115], [123, 116], [23, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [124, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [128, 116, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3173, -1117, -538, -561, 2043]
  a := ![3, 3, 0, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![52, -858, -538, -561, 2043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -31, 2, -8, -18]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![41, -31, 2, -8, -18]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![71, 107, 1, 0, 0], ![48, 124, 0, 1, 0], ![131, 28, 0, 0, 1]] where
  M :=![![![41, -31, 2, -8, -18], ![-72, 81, -46, 24, -12], ![-24, -17, 57, -10, 84], ![204, -160, 16, -49, -108], ![-124, 95, -8, 30, 55]]]
  hmulB := by decide  
  f := ![![![-3133, -1361, -964, -660, -1146]], ![![-4584, -1979, -1402, -956, -1668]], ![![-5153, -2229, -1579, -1078, -1878]], ![![-5172, -2236, -1584, -1081, -1884]], ![![-3873, -1680, -1190, -814, -1415]]]
  g := ![![![19, 9, 2, -8, -18], ![26, 17, -46, 24, -12], ![-105, -52, 57, -10, 84], ![112, 52, 16, -49, -108], ![-59, -31, -8, 30, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [11, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 138], [0, 1]]
 g := ![![[40, 38], [125, 122], [121], [74, 4], [86], [112], [1]], ![[0, 101], [99, 17], [121], [121, 135], [86], [112], [1]]]
 h' := ![![[116, 138], [15, 49], [42, 20], [20, 11], [28, 137], [1, 15], [128, 116], [0, 1]], ![[0, 1], [0, 90], [138, 119], [45, 128], [74, 2], [73, 124], [101, 23], [116, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [108, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [11, 23, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![631, -345, 91, 374, 1131]
  a := ![1, 5, -3, 4, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1237, -634, 91, 374, 1131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -5, -3, 0, 7]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![9, -5, -3, 0, 7]] 
 ![![139, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![9, -5, -3, 0, 7], ![28, -15, -10, -20, -14], ![-28, 10, 5, -16, -46], ![-106, 49, 31, 45, 5], ![20, -8, -4, 10, 31]]]
  hmulB := by decide  
  f := ![![![283, -249, 5, -74, -157]], ![![138, -121, 0, -36, -80]], ![![104, -94, 5, -28, -54]], ![![197, -172, 4, -51, -108]], ![![22, -20, 0, -6, -13]]]
  g := ![![![3, -5, -3, 0, 7], ![26, -15, -10, -20, -14], ![8, 10, 5, -16, -46], ![-67, 49, 31, 45, 5], ![-4, -8, -4, 10, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1287, -558, -395, -270, -467]] ![![41, -31, 2, -8, -18]]
  ![![-283, 249, -5, 74, 157]] where
 M := ![![![-283, 249, -5, 74, 157]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-283, 249, -5, 74, 157]] ![![9, -5, -3, 0, 7]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -16, -30, -4, -62]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![47, -16, -30, -4, -62]] 
 ![![149, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![145, 0, 0, 0, 1]] where
  M :=![![![47, -16, -30, -4, -62], ![-248, 195, -24, 56, 100], ![200, -230, 139, -68, 68], ![260, -98, -150, -25, -322], ![-152, 62, 80, 16, 179]]]
  hmulB := by decide  
  f := ![![![-2805, -1192, -842, -516, -914]], ![![-514, -221, -156, -96, -168]], ![![-2069, -882, -623, -384, -678]], ![![-1136, -478, -338, -209, -374]], ![![-2729, -1158, -818, -500, -887]]]
  g := ![![![87, -16, -30, -4, -62], ![-138, 195, -24, 56, 100], ![-99, -230, 139, -68, 68], ![452, -98, -150, -25, -322], ![-251, 62, 80, 16, 179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 1, 0, 1]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![3, 0, 1, 0, 1]] 
 ![![149, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![100, 0, 0, 0, 1]] where
  M :=![![![3, 0, 1, 0, 1], ![4, 1, 0, 0, -2], ![-4, 5, 1, 2, 2], ![2, -3, 3, 1, 5], ![0, 1, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![23, 14, -3, 6, 19]], ![![9, 5, -1, 2, 7]], ![![8, 5, -1, 2, 6]], ![![15, 11, -2, 5, 14]], ![![16, 9, -2, 4, 13]]]
  g := ![![![-1, 0, 1, 0, 1], ![1, 1, 0, 0, -2], ![-5, 5, 1, 2, 2], ![-4, -3, 3, 1, 5], ![1, 1, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3741, 1703, 1060, 1166, -548]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-3741, 1703, 1060, 1166, -548]] 
 ![![149, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![105, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-3741, 1703, 1060, 1166, -548], ![-2192, 1295, 1074, 5548, 8092], ![16184, -7149, -4253, -1470, 8552], ![18200, -8980, -6216, -17049, -17008], ![-11280, 4997, 2986, 1258, -5557]]]
  hmulB := by decide  
  f := ![![![374999, 163015, 115842, 78842, 137368]], ![![265432, 115369, 81986, 55800, 97212]], ![![266923, 116058, 82451, 56128, 97780]], ![![2627, 1143, 826, 553, 984]], ![![206038, 89565, 63640, 43318, 75463]]]
  g := ![![![-1667, 1703, 1060, 1166, -548], ![-6166, 1295, 1074, 5548, 8092], ![3399, -7149, -4253, -1470, 8552], ![20245, -8980, -6216, -17049, -17008], ![-2618, 4997, 2986, 1258, -5557]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2

def I149N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 83, 59, 42, 75]] i)))

def SI149N3: IdealEqSpanCertificate' Table ![![197, 83, 59, 42, 75]] 
 ![![149, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![197, 83, 59, 42, 75], ![300, 115, 82, 52, 102], ![204, 90, 63, 32, 54], ![-42, 27, 17, 15, -9], ![-24, -12, -8, 2, 5]]]
  hmulB := by decide  
  f := ![![![-1535, 949, 277, 264, 1149]], ![![-1226, 749, 236, 208, 936]], ![![-92, 70, -5, 20, 42]], ![![-539, 334, 96, 93, 402]], ![![-1339, 827, 243, 230, 1004]]]
  g := ![![![-150, 83, 59, 42, 75], ![-204, 115, 82, 52, 102], ![-134, 90, 63, 32, 54], ![-20, 27, 17, 15, -9], ![5, -12, -8, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N3 : Nat.card (O ⧸ I149N3) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N3)

lemma isPrimeI149N3 : Ideal.IsPrime I149N3 := prime_ideal_of_norm_prime hp149.out _ NI149N3

def I149N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9221, -3962, -2836, -1922, -3342]] i)))

def SI149N4: IdealEqSpanCertificate' Table ![![-9221, -3962, -2836, -1922, -3342]] 
 ![![149, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-9221, -3962, -2836, -1922, -3342], ![-13368, -5875, -4080, -2832, -4848], ![-9696, -4284, -3043, -2064, -3648], ![-612, -24, -180, -43, -120], ![1348, 452, 412, 236, 437]]]
  hmulB := by decide  
  f := ![![![-14257, 7574, 5692, 22190, 28602]], ![![-12628, 6781, 5152, 20840, 27384]], ![![-2234, 1240, 973, 4348, 5988]], ![![-9403, 4826, 3496, 11863, 14070]], ![![-13684, 7236, 5412, 20748, 26501]]]
  g := ![![![8429, -3962, -2836, -1922, -3342], ![12364, -5875, -4080, -2832, -4848], ![9134, -4284, -3043, -2064, -3648], ![193, -24, -180, -43, -120], ![-1040, 452, 412, 236, 437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N4 : Nat.card (O ⧸ I149N4) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N4)

lemma isPrimeI149N4 : Ideal.IsPrime I149N4 := prime_ideal_of_norm_prime hp149.out _ NI149N4
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![47, -16, -30, -4, -62]] ![![3, 0, 1, 0, 1]]
  ![![189, -216, 129, -64, 61]] where
 M := ![![![189, -216, 129, -64, 61]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![189, -216, 129, -64, 61]] ![![-3741, 1703, 1060, 1166, -548]]
  ![![1279, -537, -311, 250, 1299]] where
 M := ![![![1279, -537, -311, 250, 1299]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N2 : IdealMulLeCertificate' Table 
  ![![1279, -537, -311, 250, 1299]] ![![197, 83, 59, 42, 75]]
  ![![-14257, 7574, 5692, 22190, 28602]] where
 M := ![![![-14257, 7574, 5692, 22190, 28602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N3 : IdealMulLeCertificate' Table 
  ![![-14257, 7574, 5692, 22190, 28602]] ![![-9221, -3962, -2836, -1922, -3342]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2, I149N3, I149N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
    exact isPrimeI149N3
    exact isPrimeI149N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1 ⊙ MulI149N2 ⊙ MulI149N3)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0, 0, 0]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]] where
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [119, 130, 25, 82, 131, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 131, 39, 10, 8], [55, 38, 138, 27, 33], [132, 97, 22, 45], [104, 35, 103, 69, 110], [0, 1]]
 g := ![![[34, 75, 23, 128, 49], [91, 103, 32, 70, 91], [103, 91, 41, 49, 68], [26, 99, 119, 8], [150, 14, 16, 20, 1], [], []], ![[111, 124, 126, 51, 132, 104, 107, 10], [90, 93, 58, 110, 115, 82, 110, 127], [57, 57, 142, 14, 73, 137, 11, 25], [25, 54, 46, 99], [92, 48, 113, 8, 99, 115, 105, 1], [64, 106, 70, 88], [125, 116, 81, 64]], ![[51, 55, 53, 70, 67, 126, 44, 26], [72, 120, 129, 19, 73, 44, 130, 89], [126, 67, 42, 81, 26, 108, 104, 117], [76, 46, 66, 25], [140, 17, 127, 123, 97, 17, 10, 71], [80, 90, 72, 124], [100, 85, 6, 32]], ![[135, 111, 50, 90, 136, 8, 45], [2, 18, 121, 0, 24, 7, 2], [25, 4, 102, 15, 149, 106, 55], [124, 24, 29, 97], [127, 140, 8, 24, 74, 42, 9], [6, 68, 17, 123], [49, 62]], ![[11, 25, 82, 69, 82, 21, 139, 42], [108, 53, 80, 117, 142, 67, 62, 103], [60, 9, 135, 56, 7, 125, 129, 80], [127, 23, 79, 20], [114, 148, 12, 99, 84, 48, 67, 127], [132, 79, 91, 105], [57, 47, 27, 20]]]
 h' := ![![[31, 131, 39, 10, 8], [43, 145, 99, 47, 7], [125, 65, 74, 106, 53], [44, 93, 143, 73, 81], [119, 125, 76, 104, 92], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[55, 38, 138, 27, 33], [11, 34, 81, 79, 48], [0, 77, 45, 79, 65], [49, 105, 135, 83, 18], [149, 84, 36, 127, 34], [116, 22, 59, 113, 64], [129, 114, 40, 78, 115], [31, 131, 39, 10, 8]], ![[132, 97, 22, 45], [84, 74, 47, 82, 15], [93, 14, 79, 78, 25], [59, 133, 133, 66, 22], [88, 94, 94, 17, 5], [92, 27, 23, 33, 139], [34, 91, 95, 55, 44], [55, 38, 138, 27, 33]], ![[104, 35, 103, 69, 110], [120, 2, 110, 37, 150], [96, 27, 146, 81, 83], [137, 84, 134, 124, 13], [104, 141, 59, 144, 61], [140, 48, 35, 17, 11], [117, 82, 43, 10, 127], [132, 97, 22, 45]], ![[0, 1], [102, 47, 116, 57, 82], [9, 119, 109, 109, 76], [23, 38, 59, 107, 17], [6, 9, 37, 61, 110], [120, 54, 34, 139, 87], [107, 15, 123, 8, 16], [104, 35, 103, 69, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 40, 107, 115], [], [], []]
 b := ![[], [50, 46, 38, 42, 80], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 5
  hpos := by decide
  P := [119, 130, 25, 82, 131, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4356803, -2513546, -1012002, -850583, -3594555]
  a := ![4, 0, 0, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28853, -16646, -6702, -5633, -23805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 78502725751 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB187I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB187I3 : PrimesBelowBoundCertificateInterval O 103 151 187 where
  m := 9
  g := ![3, 3, 1, 3, 5, 1, 3, 5, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB187I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2, I131N3, I131N4]
    · exact ![I137N0]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2, I149N3, I149N4]
    · exact ![I151N0]
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
    · exact ![11881, 11881, 109]
    · exact ![18424351793]
    · exact ![16129, 16129, 127]
    · exact ![131, 131, 131, 131, 131]
    · exact ![48261724457]
    · exact ![19321, 19321, 139]
    · exact ![149, 149, 149, 149, 149]
    · exact ![78502725751]
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
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
      exact NI131N4
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
      exact NI149N3
      exact NI149N4
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
  β := ![I107N2, I109N2, I127N2, I131N0, I131N1, I131N2, I131N3, I131N4, I139N2, I149N0, I149N1, I149N2, I149N3, I149N4]
  Il := ![[I107N2], [I109N2], [], [I127N2], [I131N0, I131N1, I131N2, I131N3, I131N4], [], [I139N2], [I149N0, I149N1, I149N2, I149N3, I149N4], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
