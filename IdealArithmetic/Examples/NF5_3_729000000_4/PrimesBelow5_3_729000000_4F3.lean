
import IdealArithmetic.Examples.NF5_3_729000000_4.RI5_3_729000000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39249837, 1124530, 4440726, 1154418, -3791980]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-39249837, 1124530, 4440726, 1154418, -3791980]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![36, 30, 1, 0, 0], ![84, 88, 0, 1, 0], ![92, 86, 0, 0, 1]] where
  M :=![![![-39249837, 1124530, 4440726, 1154418, -3791980], ![12033392, -343859, -1361252, -353892, 1162172], ![-3687508, 110184, 418241, 108632, -358204], ![2413368, -59364, -270804, -70603, 228972], ![-5447410, 162950, 617898, 160486, -529227]]]
  hmulB := by decide  
  f := ![![![124297, 469414, -217310, -110954, 239300]], ![![-530776, -1988017, 917828, 453012, -987796]], ![![-86240, -322506, 148817, 72968, -159452]], ![![-391652, -1459796, 672868, 325277, -714140]], ![![-324966, -1213892, 559930, 273238, -598027]]]
  g := ![![![493225, 863778, 4440726, 1154418, -3791980], ![-150976, -264585, -1361252, -353892, 1162172], ![47528, 82326, 418241, 108632, -358204], ![-27780, -50596, -270804, -70603, 228972], ![70246, 121652, 617898, 160486, -529227]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [63, 9, 1] where
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
 g := ![![[46, 37], [57, 81], [61], [104, 29], [3], [98, 1]], ![[34, 70], [77, 26], [61], [57, 78], [3], [89, 106]]]
 h' := ![![[98, 106], [47, 12], [99, 98], [82, 32], [86, 55], [32, 18], [0, 1]], ![[0, 1], [46, 95], [73, 9], [8, 75], [19, 52], [84, 89], [98, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [62, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [63, 9, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355429, -773953, -584093, -282254, 1121980]
  a := ![47, 70, 42, 53, -188]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-549915, -513113, -584093, -282254, 1121980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -37, 13, 8, -15]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-10, -37, 13, 8, -15]] 
 ![![107, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-10, -37, 13, 8, -15], ![27, 113, -72, -38, 87], ![-207, -762, 269, 160, -303], ![381, 1527, -861, -451, 1011], ![-15, -11, -103, -44, 134]]]
  hmulB := by decide  
  f := ![![![-12134, 179, 1333, 350, -1101]], ![![-1329, 11, 144, 38, -117]], ![![-7963, 76, 865, 228, -705]], ![![-9095, 47, 979, 259, -789]], ![![-6047, 28, 650, 172, -523]]]
  g := ![![![-3, -37, 13, 8, -15], ![20, 113, -72, -38, 87], ![-62, -762, 269, 160, -303], ![232, 1527, -861, -451, 1011], ![35, -11, -103, -44, 134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5813, -22747, 10651, 6190, -12832]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-5813, -22747, 10651, 6190, -12832]] 
 ![![107, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-5813, -22747, 10651, 6190, -12832], ![27020, 105293, -49236, -28218, 58736], ![-124372, -482586, 225365, 127272, -266080], ![345570, 1335903, -623109, -347359, 729024], ![27736, 108223, -50623, -29142, 60579]]]
  hmulB := by decide  
  f := ![![![308635425, -8841451, -34918751, -9077556, 29817200]], ![![221217823, -6337214, -25028399, -6506438, 21371808]], ![![181991017, -5213517, -20590318, -5352704, 17582128]], ![![11360634, -325529, -1285351, -334141, 1097584]], ![![210964835, -6043548, -23868396, -6204880, 20381291]]]
  g := ![![![18567, -22747, 10651, 6190, -12832], ![-85547, 105293, -49236, -28218, 58736], ![390201, -482586, 225365, 127272, -266080], ![-1075630, 1335903, -623109, -347359, 729024], ![-88055, 108223, -50623, -29142, 60579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2

def I107N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![888, -24, -100, -26, 85]] i)))

def SI107N3: IdealEqSpanCertificate' Table ![![888, -24, -100, -26, 85]] 
 ![![107, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![75, 0, 0, 0, 1]] where
  M :=![![![888, -24, -100, -26, 85], ![-269, 17, 32, 8, -29], ![97, 36, 1, 0, -11], ![-21, 102, 18, 1, -33], ![145, 60, -2, -2, -12]]]
  hmulB := by decide  
  f := ![![![152, 480, 34, -18, -65]], ![![139, 437, 36, -14, -66]], ![![129, 408, 27, -16, -53]], ![![115, 342, 80, 13, -121]], ![![135, 420, 46, -8, -79]]]
  g := ![![![51, -24, -100, -26, 85], ![-23, 17, 32, 8, -29], ![-24, 36, 1, 0, -11], ![-80, 102, 18, 1, -33], ![-41, 60, -2, -2, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N3 : Nat.card (O ⧸ I107N3) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N3)

lemma isPrimeI107N3 : Ideal.IsPrime I107N3 := prime_ideal_of_norm_prime hp107.out _ NI107N3
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-39249837, 1124530, 4440726, 1154418, -3791980]] ![![-10, -37, 13, 8, -15]]
  ![![343356, -9287, -38705, -10074, 32965]] where
 M := ![![![343356, -9287, -38705, -10074, 32965]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![343356, -9287, -38705, -10074, 32965]] ![![-5813, -22747, 10651, 6190, -12832]]
  ![![152, 480, 34, -18, -65]] where
 M := ![![![152, 480, 34, -18, -65]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N2 : IdealMulLeCertificate' Table 
  ![![152, 480, 34, -18, -65]] ![![888, -24, -100, -26, 85]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2, I107N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
    exact isPrimeI107N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1 ⊙ MulI107N2)
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


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [69, 38, 27, 45, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 99, 29, 55, 77], [17, 103, 101, 61, 73], [22, 92, 73, 52, 70], [26, 32, 15, 50, 107], [0, 1]]
 g := ![![[8, 28, 95, 101, 60], [1, 10, 63, 27], [81, 10, 89], [96, 15, 20, 78, 3], [58, 1], []], ![[63, 73, 19, 55, 98, 36, 24, 58], [64, 58, 73, 75], [66, 23, 97, 33, 49, 38, 66, 32], [63, 103, 5, 85, 87, 45, 30, 92], [31, 75, 64, 64], [10, 4, 21, 73, 50, 93, 99, 41]], ![[41, 81, 28, 86, 20, 27, 45, 22], [39, 89, 26, 7], [3, 2, 0, 99, 77, 90, 68, 74], [93, 39, 31, 54, 56, 106, 100, 89], [2, 9, 18, 71], [82, 79, 14, 0, 102, 51, 79, 105]], ![[64, 29, 51, 14, 52, 32, 95, 59], [103, 10, 61, 1], [57, 102, 58, 36, 33, 62, 32, 41], [18, 10, 90, 80, 64, 90, 92, 52], [74, 98, 92, 35], [24, 77, 82, 103, 103, 12, 66, 86]], ![[19, 35, 18, 47, 35, 32], [42, 35, 100, 21], [69, 106, 70, 57, 89, 88, 74, 18], [27, 0, 28, 41, 93, 40, 76, 103], [35, 79, 25, 9], [30, 34, 75, 74, 60, 77, 27, 101]]]
 h' := ![![[102, 99, 29, 55, 77], [68, 45, 13, 0, 96], [79, 18, 84, 105, 38], [25, 93, 47, 31], [31, 16, 31, 88, 49], [0, 0, 0, 1], [0, 1]], ![[17, 103, 101, 61, 73], [48, 106, 5, 54, 88], [39, 0, 34, 52, 27], [47, 21, 33, 72, 76], [20, 21, 88, 63, 16], [57, 54, 74, 10, 101], [102, 99, 29, 55, 77]], ![[22, 92, 73, 52, 70], [108, 53, 90, 54, 75], [69, 73, 83, 60, 15], [91, 67, 21, 81, 107], [77, 5, 5, 11, 7], [18, 74, 54, 91, 17], [17, 103, 101, 61, 73]], ![[26, 32, 15, 50, 107], [44, 101, 29, 87, 68], [75, 35, 15, 56, 1], [86, 94, 16, 21, 25], [99, 80, 87, 103, 97], [54, 47, 80, 108, 97], [22, 92, 73, 52, 70]], ![[0, 1], [45, 22, 81, 23], [0, 92, 2, 54, 28], [79, 52, 101, 13, 10], [4, 96, 7, 62, 49], [28, 43, 10, 8, 3], [26, 32, 15, 50, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 56, 60, 38], [], [], []]
 b := ![[], [15, 36, 18, 83, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [69, 38, 27, 45, 51, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5603136035989887428507, 15761835755615481347650, 4261132799571254530220, 1006620481944432318690, -7991597011267801746964]
  a := ![562, 811, 499, 623, -2245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![51404917761375114023, 144603997757940195850, 39092961463956463580, 9235050293068186410, -73317403773099098596]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3836372, 15185978, -7135932, -4304280, 8827653]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![3836372, 15185978, -7135932, -4304280, 8827653]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![88, 33, 1, 0, 0], ![86, 48, 0, 1, 0], ![91, 98, 0, 0, 1]] where
  M :=![![![3836372, 15185978, -7135932, -4304280, 8827653], ![-18312585, -72184597, 33875726, 20162376, -41509149], ![86571489, 339844968, -159283127, -93547556, 193332981], ![-245975529, -962337114, 450565152, 261680875, -542571729], ![-18641539, -73576814, 34542966, 20645028, -42452228]]]
  hmulB := by decide  
  f := ![![![250470364780, -7175098030, -28337982682, -7366806980, 24197839821]], ![![-76788357225, 2199709927, 8687761168, 2258490476, -7418488773]], ![![172839980648, -4951262093, -19554954241, -5083550708, 16698001104]], ![![157869299143, -4522405870, -17861185654, -4643234713, 15251690229]], ![![135418774309, -3879280082, -15321154994, -3982922452, 13082755471]]]
  g := ![![![1757965, -3609140, -7135932, -4304280, 8827653], ![-8460250, 16902823, 33875726, 20162376, -41509149], ![40312170, -78408507, -159283127, -93547556, 193332981], ![-115276432, 219295224, 450565152, 261680875, -542571729], ![-8590639, 17308516, 34542966, 20645028, -42452228]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [110, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 112], [0, 1]]
 g := ![![[34, 30], [36], [36], [100], [90, 8], [102, 1]], ![[43, 83], [36], [36], [100], [2, 105], [91, 112]]]
 h' := ![![[102, 112], [31, 97], [6, 107], [89, 6], [44, 10], [80, 11], [0, 1]], ![[0, 1], [94, 16], [72, 6], [23, 107], [47, 103], [72, 102], [102, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [39, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [110, 11, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-334323, -742314, -524894, -249554, 1014599]
  a := ![45, 66, 40, 50, -179]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-221332, -627194, -524894, -249554, 1014599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1299, -34, -146, -38, 124]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1299, -34, -146, -38, 124]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![49, 109, 1, 0, 0], ![17, 75, 0, 1, 0], ![67, 18, 0, 0, 1]] where
  M :=![![![1299, -34, -146, -38, 124], ![-392, 29, 48, 12, -44], ![148, 72, 5, 0, -20], ![-24, 168, 36, 5, -60], ![218, 106, 2, -2, -23]]]
  hmulB := by decide  
  f := ![![![11, 38, -2, -6, 4]], ![![16, 13, 72, 44, -116]], ![![23, 39, 67, 38, -108]], ![![11, 5, 58, 35, -92]], ![![11, 30, 12, 4, -19]]]
  g := ![![![7, 146, -146, -38, 124], ![0, -47, 48, 12, -44], ![11, -1, 5, 0, -20], ![19, -27, 36, 5, -60], ![15, 4, 2, -2, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [6, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 112], [0, 1]]
 g := ![![[38, 64], [51], [25], [36], [57, 4], [111, 1]], ![[23, 49], [51], [25], [36], [49, 109], [109, 112]]]
 h' := ![![[111, 112], [32, 105], [98, 27], [19, 5], [110, 6], [12, 111], [0, 1]], ![[0, 1], [48, 8], [44, 86], [9, 108], [98, 107], [16, 2], [111, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [34, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [6, 2, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7209996, -15865273, -11530296, -5525605, 22258302]
  a := ![-209, -304, -187, -235, 837]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7430057, 11103610, -11530296, -5525605, 22258302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-190435422, 5455012, 21545616, 5601054, -18397765]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-190435422, 5455012, 21545616, 5601054, -18397765]] 
 ![![113, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-190435422, 5455012, 21545616, 5601054, -18397765], ![58382501, -1673963, -6605696, -1717200, 5640941], ![-17901505, 505068, 2023541, 526208, -1726213], ![11687661, -350838, -1326090, -344395, 1135857], ![-26445445, 746216, 2989350, 777358, -2550126]]]
  hmulB := by decide  
  f := ![![![-2156990, -8781788, 4161802, 2727106, -5466517]], ![![-1506347, -6135455, 2908042, 1907820, -3823031]], ![![-1688987, -6851748, 3243665, 2104322, -4229504]], ![![-291037, -1283266, 621986, 491983, -940838]], ![![-1411033, -5746620, 2723658, 1786328, -3579859]]]
  g := ![![![-9400909, 5455012, 21545616, 5601054, -18397765], ![2883054, -1673963, -6605696, -1717200, 5640941], ![-878977, 505068, 2023541, 526208, -1726213], ![586805, -350838, -1326090, -344395, 1135857], ![-1298551, 746216, 2989350, 777358, -2550126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![3836372, 15185978, -7135932, -4304280, 8827653]] ![![1299, -34, -146, -38, 124]]
  ![![2156990, 8781788, -4161802, -2727106, 5466517]] where
 M := ![![![2156990, 8781788, -4161802, -2727106, 5466517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![2156990, 8781788, -4161802, -2727106, 5466517]] ![![-190435422, 5455012, 21545616, 5601054, -18397765]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-178, -708, 328, 204, -413]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-178, -708, 328, 204, -413]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![121, 124, 82, 1, 0], ![7, 3, 68, 0, 1]] where
  M :=![![![-178, -708, 328, 204, -413], ![841, 3355, -1604, -976, 2005], ![-4169, -16440, 7607, 4600, -9389], ![11757, 46464, -22020, -13093, 27033], ![789, 3216, -1666, -1000, 2104]]]
  hmulB := by decide  
  f := ![![![8682, -264, -986, -256, 845]], ![![-2689, 1, 286, 76, -229]], ![![689, -396, -169, -36, 221]], ![![6085, -512, -770, -193, 726]], ![![792, -231, -140, -32, 162]]]
  g := ![![![-173, -195, 92, 204, -413], ![826, 932, -456, -976, 2005], ![-3898, -4399, 2117, 4600, -9389], ![11077, 12511, -6194, -13093, 27033], ![843, 952, -494, -1000, 2104]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [14, 0, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 112, 101], [79, 14, 26], [0, 1]]
 g := ![![[116, 2, 87], [52, 65, 19], [87, 61, 36], [110, 72, 98], [124, 10, 60], [1]], ![[19, 9, 10, 96], [126, 102, 6, 97], [116, 41, 66, 111], [84, 126, 7, 119], [123, 70, 74, 56], [83, 53, 94, 77]], ![[89, 25, 98, 38], [28, 49, 58, 31], [55, 4, 33, 13], [0, 69, 55, 32], [86, 29, 47, 99], [56, 98, 37, 50]]]
 h' := ![![[27, 112, 101], [34, 16, 77], [52, 37, 20], [111, 121, 6], [42, 56, 112], [113, 0, 106], [0, 1]], ![[79, 14, 26], [26, 126, 27], [84, 86, 80], [78, 41, 113], [25, 108, 112], [106, 108, 87], [27, 112, 101]], ![[0, 1], [8, 112, 23], [62, 4, 27], [122, 92, 8], [15, 90, 30], [3, 19, 61], [79, 14, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 36], []]
 b := ![[], [21, 22, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [14, 0, 21, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![537256460, 1026324984, 1359316856, 629011606, -2245243458]
  a := ![40, 60, 38, 49, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-471310580, -553034518, 806747404, 629011606, -2245243458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8682, 264, 986, 256, -845]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-8682, 264, 986, 256, -845]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![114, 91, 1, 0, 0], ![90, 62, 0, 1, 0], ![113, 71, 0, 0, 1]] where
  M :=![![![-8682, 264, 986, 256, -845], ![2689, -1, -286, -76, 229], ![-689, 396, 169, 36, -221], ![789, 732, 90, 7, -231], ![-1025, 564, 244, 52, -318]]]
  hmulB := by decide  
  f := ![![![178, 708, -328, -204, 413]], ![![-841, -3355, 1604, 976, -2005]], ![![-410, -1639, 795, 480, -992]], ![![-377, -1502, 724, 435, -899]], ![![-318, -1271, 618, 372, -770]]]
  g := ![![![-383, -357, 986, 256, -845], ![128, 114, -286, -76, 229], ![14, -12, 169, 36, -221], ![126, 67, 90, 7, -231], ![19, -18, 244, 52, -318]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [60, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 126], [0, 1]]
 g := ![![[40, 36], [113, 35], [11, 107], [24, 25], [34, 70], [13, 1]], ![[0, 91], [60, 92], [5, 20], [95, 102], [55, 57], [26, 126]]]
 h' := ![![[13, 126], [78, 121], [102, 17], [84, 19], [119, 122], [109, 109], [0, 1]], ![[0, 1], [0, 6], [69, 110], [77, 108], [54, 5], [2, 18], [13, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [66, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [60, 114, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-174236, -484176, -100408, -21120, 244992]
  a := ![20, 30, 14, 14, -80]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114260, -58520, -100408, -21120, 244992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-178, -708, 328, 204, -413]] ![![-8682, 264, 986, 256, -845]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3285, 10621, -4035, -682, 2222]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3285, 10621, -4035, -682, 2222]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![129, 129, 21, 84, 1]] where
  M :=![![![3285, 10621, -4035, -682, 2222], ![-7018, -19463, 10678, -2614, -814], ![19754, 27090, 6899, 42268, -68434], ![34404, 250947, -113259, -183307, 301914], ![-2476, -7585, 18531, -22, -11469]]]
  hmulB := by decide  
  f := ![![![-13508453, 386941, 1528327, 397308, -1305034]], ![![4141322, -118783, -468580, -121810, 400154]], ![![-1269910, 35610, 143497, 37320, -122362]], ![![828900, -25347, -94155, -24443, 80754]], ![![-8910507, 253921, 1007815, 262022, -860279]]]
  g := ![![![-2163, -2107, -387, -1430, 2222], ![748, 653, 212, 502, -814], ![67540, 67596, 11023, 44204, -68434], ![-297042, -295389, -49263, -194993, 301914], ![11275, 11236, 1980, 7354, -11469]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [120, 48, 99, 35, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 117, 72, 124], [24, 106, 92, 103], [96, 38, 98, 35], [0, 1]]
 g := ![![[105, 8, 114, 44], [129, 70, 86, 7], [86, 55, 11], [85, 35, 27], [43, 80, 46], [1], []], ![[25, 80, 98, 13, 101, 47], [13, 1, 47, 70, 8, 116], [80, 88, 91], [10, 110, 41], [63, 50, 9], [45, 32, 89], [73, 28, 49]], ![[12, 124, 10, 63, 26, 54], [117, 1, 58, 51, 75, 23], [127, 79, 55], [73, 127, 64], [85, 48, 100], [22, 11, 94], [78, 27, 129]], ![[25, 9, 126, 70, 46, 64], [76, 85, 27, 81, 123, 28], [87, 91, 1], [45, 50, 89], [49, 12, 129], [28, 92, 15], [24, 10, 46]]]
 h' := ![![[107, 117, 72, 124], [109, 29, 117, 100], [92, 2, 5, 20], [71, 118, 83, 50], [70, 118, 2, 114], [11, 83, 32, 96], [0, 0, 1], [0, 1]], ![[24, 106, 92, 103], [23, 66, 6, 55], [23, 3, 75, 83], [86, 19, 6, 109], [32, 81, 54, 98], [16, 43, 92, 128], [69, 96, 105, 73], [107, 117, 72, 124]], ![[96, 38, 98, 35], [8, 22, 15, 25], [57, 35, 6, 45], [106, 31, 110, 102], [73, 29, 24, 123], [29, 64, 125, 10], [124, 69, 62, 15], [24, 106, 92, 103]], ![[0, 1], [123, 14, 124, 82], [52, 91, 45, 114], [55, 94, 63, 1], [79, 34, 51, 58], [123, 72, 13, 28], [48, 97, 94, 43], [96, 38, 98, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [31, 94, 44], []]
 b := ![[], [], [47, 32, 121, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [120, 48, 99, 35, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-332331135717, 355093409062, -3108581293174, -1523622389803, 4608015187317]
  a := ![43, 64, 40, 51, -159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4540200689310, -4534953173701, -762419085701, -2966388535301, 4608015187317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13508453, 386941, 1528327, 397308, -1305034]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-13508453, 386941, 1528327, 397308, -1305034]] 
 ![![131, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-13508453, 386941, 1528327, 397308, -1305034], ![4141322, -118783, -468580, -121810, 400154], ![-1269910, 35610, 143497, 37320, -122362], ![828900, -25347, -94155, -24443, 80754], ![-1876008, 52607, 211985, 55132, -180763]]]
  hmulB := by decide  
  f := ![![![3285, 10621, -4035, -682, 2222]], ![![1777, 5770, -2167, -400, 1232]], ![![1204, 3612, -1241, 104, 190]], ![![714, 3375, -1419, -1493, 2610]], ![![934, 3023, -1029, -198, 557]]]
  g := ![![![-484772, 386941, 1528327, 397308, -1305034], ![148699, -118783, -468580, -121810, 400154], ![-45178, 35610, 143497, 37320, -122362], ![30573, -25347, -94155, -24443, 80754], ![-66741, 52607, 211985, 55132, -180763]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3285, 10621, -4035, -682, 2222]] ![![-13508453, 386941, 1528327, 397308, -1305034]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65861, -243516, 112028, 52220, -116086]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-65861, -243516, 112028, 52220, -116086]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![43, 112, 1, 0, 0], ![105, 64, 0, 1, 0], ![45, 120, 0, 0, 1]] where
  M :=![![![-65861, -243516, 112028, 52220, -116086], ![267110, 973277, -444808, -193704, 440678], ![-1041166, -3718368, 1690693, 660016, -1564150], ![2450910, 8535504, -3839232, -1279379, 3227742], ![287778, 1053204, -480344, -214516, 483155]]]
  hmulB := by decide  
  f := ![![![200186079, -6115332, -22737764, -5902940, 19500134]], ![![-62083030, -189203, 6564544, 1747992, -5169622]], ![![12190235, -2151532, -1800055, -429972, 1936296]], ![![124282465, -4925956, -14380108, -3709511, 12581704]], ![![11540929, -2288688, -1762964, -417048, 1939125]]]
  g := ![![![-37535, -16076, 112028, 52220, -116086], ![145272, 75237, -444808, -193704, 440678], ![-530335, -347584, 1690693, 660016, -1564150], ![1143243, 971392, -3839232, -1279379, 3227742], ![158575, 77388, -480344, -214516, 483155]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [99, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 136], [0, 1]]
 g := ![![[106, 18], [93], [107], [64, 18], [100], [11], [1]], ![[0, 119], [93], [107], [95, 119], [100], [11], [1]]]
 h' := ![![[55, 136], [91, 93], [16, 40], [103, 92], [86, 44], [81, 127], [38, 55], [0, 1]], ![[0, 1], [0, 44], [24, 97], [94, 45], [40, 93], [79, 10], [49, 82], [55, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [39, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [99, 82, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43675, -112713, -42912, -15661, 88730]
  a := ![13, 18, 11, 13, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3992, -36145, -42912, -15661, 88730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15403121, 439204, 1742218, 452954, -1487230]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-15403121, 439204, 1742218, 452954, -1487230]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![22, 37, 1, 0, 0], ![130, 130, 0, 1, 0], ![55, 57, 0, 0, 1]] where
  M :=![![![-15403121, 439204, 1742218, 452954, -1487230], ![4718426, -145717, -536302, -139196, 460286], ![-1466254, -12528, 153157, 40964, -118702], ![906990, -139638, -129156, -31181, 135462], ![-2166030, -18412, 226274, 60518, -175393]]]
  hmulB := by decide  
  f := ![![![507, 3928, -4554, -2990, 6782]], ![![-15970, -60749, 17314, 14812, -24286]], ![![-3994, -14561, 2979, 2908, -4116]], ![![-16340, -60452, 14552, 13007, -19894]], ![![-6743, -24693, 5370, 5048, -7361]]]
  g := ![![![-224951, -278356, 1742218, 452954, -1487230], ![67860, 84355, -536302, -139196, 460286], ![-26514, -30939, 153157, 40964, -118702], ![2566, 7090, -129156, -31181, 135462], ![-39159, -45697, 226274, 60518, -175393]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [40, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 136], [0, 1]]
 g := ![![[102, 44], [1], [98], [37, 93], [38], [78], [1]], ![[52, 93], [1], [98], [87, 44], [38], [78], [1]]]
 h' := ![![[30, 136], [53, 110], [97, 136], [27, 80], [19, 97], [124, 77], [97, 30], [0, 1]], ![[0, 1], [65, 27], [67, 1], [98, 57], [52, 40], [105, 60], [38, 107], [30, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [13, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [40, 107, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140093, -258825, -303179, -161742, 571915]
  a := ![-32, -48, -29, -39, 131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28460, -4481, -303179, -161742, 571915]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 76, 14, 2, -28]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![39, 76, 14, 2, -28]] 
 ![![137, 0, 0, 0, 0], ![125, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![39, 76, 14, 2, -28], ![128, 385, 78, 12, -148], ![668, 1944, 391, 60, -748], ![1356, 3954, 792, 121, -1524], ![964, 2804, 562, 86, -1081]]]
  hmulB := by decide  
  f := ![![![367, 1384, -646, -366, 764]], ![![323, 1217, -568, -322, 672]], ![![402, 1520, -709, -400, 836]], ![![-66, -258, 120, 61, -132]], ![![221, 832, -388, -220, 459]]]
  g := ![![![-65, 76, 14, 2, -28], ![-333, 385, 78, 12, -148], ![-1678, 1944, 391, 60, -748], ![-3408, 3954, 792, 121, -1524], ![-2417, 2804, 562, 86, -1081]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-65861, -243516, 112028, 52220, -116086]] ![![-15403121, 439204, 1742218, 452954, -1487230]]
  ![![-367, -1384, 646, 366, -764]] where
 M := ![![![-367, -1384, 646, 366, -764]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-367, -1384, 646, 366, -764]] ![![39, 76, 14, 2, -28]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4873654, -19751886, 9348258, 6047958, -12165027]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-4873654, -19751886, 9348258, 6047958, -12165027]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![95, 117, 1, 0, 0], ![94, 25, 0, 1, 0], ![8, 93, 0, 0, 1]] where
  M :=![![![-4873654, -19751886, 9348258, 6047958, -12165027], ![24537387, 98840075, -46691376, -29687148, 59995803], ![-121856127, -488223720, 230271587, 144114432, -292520931], ![359887095, 1436054904, -676455156, -418243357, 851810391], ![24581781, 99195354, -46878528, -29963346, 60465074]]]
  hmulB := by decide  
  f := ![![![-136946896258, 3917233530, 15492685812, 4027636662, -13227936249]], ![![41973861273, -1232454979, -4755900630, -1235721672, 4067726145]], ![![-58359263858, 1641401937, 6595616927, 1715251938, -5625274977]], ![![-85002614314, 2423360687, 9614392032, 2499625211, -8207157552]], ![![20064037798, -596853831, -2275184604, -590996790, 1947676019]]]
  g := ![![![-9814000, -959349, 9348258, 6047958, -12165027], ![48711105, 5210792, -46691376, -29687148, 59995803], ![-238879468, -27542544, 230271587, 144114432, -292520931], ![698730355, 85028962, -676455156, -418243357, 851810391], ![48999107, 5106582, -46878528, -29963346, 60465074]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [102, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 138], [0, 1]]
 g := ![![[4, 83], [136, 63], [11], [33, 131], [25], [81], [1]], ![[56, 56], [8, 76], [11], [100, 8], [25], [81], [1]]]
 h' := ![![[9, 138], [28, 19], [56, 52], [109, 17], [4, 100], [57, 5], [37, 9], [0, 1]], ![[0, 1], [60, 120], [107, 87], [123, 122], [70, 39], [102, 134], [118, 130], [9, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [14, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [102, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128260, -242497, -268496, -142013, 507998]
  a := ![-31, -46, -29, -37, 125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![249382, -90086, -268496, -142013, 507998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1255495, 32623, 141265, 36794, -119886]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1255495, 32623, 141265, 36794, -119886]] 
 ![![139, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-1255495, 32623, 141265, 36794, -119886], ![378666, -28123, -46876, -11822, 43854], ![-148338, -85038, -4067, 824, 23250], ![13572, -186483, -44991, -7775, 79638], ![-219082, -125467, -5977, 1222, 34285]]]
  hmulB := by decide  
  f := ![![![106847, 405035, -187797, -97296, 208890]], ![![5910, 22499, -10450, -5502, 11754]], ![![117016, 442708, -205133, -105452, 226962]], ![![42402, 164247, -76719, -43037, 90174]], ![![92595, 351080, -162804, -84408, 181183]]]
  g := ![![![-67221, 32623, 141265, 36794, -119886], ![19580, -28123, -46876, -11822, 43854], ![-11318, -85038, -4067, 824, 23250], ![-6342, -186483, -44991, -7775, 79638], ![-16711, -125467, -5977, 1222, 34285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -104, 80, 46, -105]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-22, -104, 80, 46, -105]] 
 ![![139, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-22, -104, 80, 46, -105], ![249, 929, -300, -208, 369], ![-597, -2676, 1877, 1064, -2409], ![3129, 11910, -4530, -2911, 5541], ![555, 1844, -98, -178, 62]]]
  hmulB := by decide  
  f := ![![![-313738, 7232, 35086, 9158, -29571]], ![![-112187, 2517, 12530, 3272, -10545]], ![![-4841, -224, 463, 128, -315]], ![![-198727, 3878, 22060, 5773, -18435]], ![![-9511, -276, 948, 258, -688]]]
  g := ![![![10, -104, 80, 46, -105], ![-207, 929, -300, -208, 369], ![327, -2676, 1877, 1064, -2409], ![-2513, 11910, -4530, -2911, 5541], ![-547, 1844, -98, -178, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2

def I139N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245958325, 7023859, 27822361, 7233228, -23752680]] i)))

def SI139N3: IdealEqSpanCertificate' Table ![![-245958325, 7023859, 27822361, 7233228, -23752680]] 
 ![![139, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![-245958325, 7023859, 27822361, 7233228, -23752680], ![75364032, -2272537, -8553148, -2221102, 7328712], ![-23316948, 80694, 2500927, 662520, -2005464], ![14684574, -1644645, -1947213, -480413, 1933848], ![-34445230, 120233, 3694763, 978756, -2963027]]]
  hmulB := by decide  
  f := ![![![-100783, -342757, 134355, 42242, -103224]], ![![-69891, -237928, 92369, 29588, -71424]], ![![-56792, -188546, 71587, 18004, -47784]], ![![-49437, -183918, 70044, 40627, -79488]], ![![-84031, -285272, 108216, 34576, -82643]]]
  g := ![![![-4292586, 7023859, 27822361, 7233228, -23752680], ![1374695, -2272537, -8553148, -2221102, 7328712], ![-118118, 80694, 2500927, 662520, -2005464], ![861048, -1644645, -1947213, -480413, 1933848], ![-174998, 120233, 3694763, 978756, -2963027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N3 : Nat.card (O ⧸ I139N3) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N3)

lemma isPrimeI139N3 : Ideal.IsPrime I139N3 := prime_ideal_of_norm_prime hp139.out _ NI139N3
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-4873654, -19751886, 9348258, 6047958, -12165027]] ![![-1255495, 32623, 141265, 36794, -119886]]
  ![![640, 2627, -1459, -836, 1809]] where
 M := ![![![640, 2627, -1459, -836, 1809]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![640, 2627, -1459, -836, 1809]] ![![-22, -104, 80, 46, -105]]
  ![![-100783, -342757, 134355, 42242, -103224]] where
 M := ![![![-100783, -342757, 134355, 42242, -103224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N2 : IdealMulLeCertificate' Table 
  ![![-100783, -342757, 134355, 42242, -103224]] ![![-245958325, 7023859, 27822361, 7233228, -23752680]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2, I139N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
    exact isPrimeI139N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1 ⊙ MulI139N2)
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


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [63, 6, 144, 137, 120, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 103, 97, 123, 78], [86, 105, 70, 73, 137], [91, 112, 11, 44, 94], [148, 126, 120, 58, 138], [0, 1]]
 g := ![![[52, 15, 143, 140, 73], [72, 33, 71, 102], [101, 120, 127, 108, 25], [33, 21, 54, 45], [137, 58, 108, 29, 1], [], []], ![[137, 92, 122, 89, 100, 143, 94, 139], [67, 30, 52, 118], [134, 20, 13, 11, 53, 137, 108, 79], [125, 91, 14, 144], [57, 55, 111, 23, 64, 45, 117, 60], [99, 119, 93, 46], [9, 82, 136, 124]], ![[31, 0, 68, 121, 100, 107, 96, 12], [119, 94, 128, 123], [23, 91, 69, 110, 3, 23, 115, 11], [57, 101, 37, 19], [25, 68, 83, 48, 71, 141, 51, 134], [137, 111, 104, 47], [5, 130, 40, 144]], ![[110, 71, 106, 91, 119, 14, 134, 117], [2, 93, 21, 140], [124, 40, 78, 22, 33, 75, 123, 38], [124, 146, 86, 76], [60, 69, 51, 41, 105, 38, 16, 2], [57, 57, 103, 47], [66, 71, 41, 45]], ![[31, 26, 33, 46, 74, 22, 37, 90], [100, 87, 23, 49], [19, 19, 114, 133, 47, 10, 68, 52], [138, 69, 55, 85], [81, 67, 82, 119, 63, 0, 135, 109], [136, 128, 94, 25], [141, 32, 147, 121]]]
 h' := ![![[2, 103, 97, 123, 78], [82, 109, 73, 140, 85], [44, 23, 120, 88, 20], [128, 135, 121, 17, 144], [11, 143, 89, 55, 55], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[86, 105, 70, 73, 137], [75, 52, 75, 138, 106], [78, 122, 97, 78, 72], [104, 20, 38, 93, 24], [23, 28, 147, 12, 137], [67, 146, 131, 42, 140], [33, 109, 45, 146, 33], [2, 103, 97, 123, 78]], ![[91, 112, 11, 44, 94], [139, 91, 144, 94, 44], [22, 75, 58, 114, 47], [20, 92, 103, 19, 58], [83, 58, 8, 74, 67], [135, 124, 19, 132, 115], [78, 6, 122, 29, 135], [86, 105, 70, 73, 137]], ![[148, 126, 120, 58, 138], [17, 4, 113, 45, 30], [128, 112, 145, 131, 17], [57, 52, 106, 55, 91], [11, 75, 68, 11, 134], [2, 16, 52, 55, 117], [100, 19, 96, 45, 135], [91, 112, 11, 44, 94]], ![[0, 1], [27, 42, 42, 30, 33], [48, 115, 27, 36, 142], [29, 148, 79, 114, 130], [140, 143, 135, 146, 54], [11, 12, 96, 69, 74], [58, 15, 34, 78, 144], [148, 126, 120, 58, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 80, 22, 55], [], [], []]
 b := ![[], [83, 45, 119, 132, 112], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [63, 6, 144, 137, 120, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2023755101, -7141434708, 2270942376, 1289652812, -2159902808]
  a := ![2, 3, 2, 3, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13582249, -47929092, 15241224, 8655388, -14495992]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-463612492, -1846089739, 869061271, 533921202, -1089348663]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-463612492, -1846089739, 869061271, 533921202, -1089348663]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![63, 67, 36, 1, 0], ![96, 113, 15, 0, 1]] where
  M :=![![![-463612492, -1846089739, 869061271, 533921202, -1089348663], ![2243216103, 8892629309, -4180555680, -2533247074, 5188668207], ![-10743858591, -42410246922, 19911556073, 11904865232, -24477252327], ![30850464417, 121363440747, -56919719157, -33660337471, 69426625803], ![2274030399, 9027105667, -4245554329, -2583580974, 5285403986]]]
  hmulB := by decide  
  f := ![![![-63016859596, 1806966493, 7130078183, 1853514516, -6088771521]], ![![19322770509, -544460467, -2184042420, -567959762, 1862947737]], ![![-5906980113, 216087786, 679255685, 175593256, -590400129]], ![![-19100563602, 563742353, 2164891074, 562440753, -1852275453]], ![![-26248188261, 764935146, 2972734966, 772524746, -2541305470]]]
  g := ![![![466733930, 566076746, -13323656, 533921202, -1089348663], ![-2226982557, -2699995524, 60836529, -2533247074, 5188668207], ![10523614935, 12754260235, -274866274, 11904865232, -24477252327], ![-29890757298, -36215911685, 751344654, -33660337471, 69426625803], ![-2267279145, -2749163043, 62796695, -2583580974, 5285403986]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [5, 3, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 137, 54], [47, 13, 97], [0, 1]]
 g := ![![[41, 103, 94], [129, 138, 58], [107, 59, 19], [88, 91], [59, 99, 2], [144, 1], []], ![[136, 7, 65, 147], [52, 144, 117, 89], [68, 128, 117, 79], [104, 145], [124, 17, 116, 143], [4, 18], [122, 47]], ![[49, 28, 90, 80], [29, 18, 51, 9], [111, 106, 54, 39], [35, 76], [134, 106, 125, 86], [127, 45], [79, 47]]]
 h' := ![![[97, 137, 54], [110, 60, 68], [69, 57, 71], [62, 77, 64], [7, 100, 98], [35, 16, 46], [0, 0, 1], [0, 1]], ![[47, 13, 97], [111, 104, 47], [53, 10, 75], [38, 148, 7], [135, 147, 30], [0, 6, 103], [41, 5, 13], [97, 137, 54]], ![[0, 1], [46, 138, 36], [21, 84, 5], [34, 77, 80], [71, 55, 23], [124, 129, 2], [2, 146, 137], [47, 13, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 142], []]
 b := ![[], [149, 69, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [5, 3, 7, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70714160521, 173494156944, 99345523812, 39192898087, -176133473461]
  a := ![170, 256, 148, 191, -673]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![96095198896, 115567235008, 8810617845, 39192898087, -176133473461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1377293108993, -39454612690, -155825651780, -40508794026, 133059722610]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![1377293108993, -39454612690, -155825651780, -40508794026, 133059722610]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![30, 80, 1, 0, 0], ![144, 97, 0, 1, 0], ![85, 131, 0, 0, 1]] where
  M :=![![![1377293108993, -39454612690, -155825651780, -40508794026, 133059722610], ![-422245848894, 12095861297, 47772499686, 12419048648, -40792998354], ![129450699882, -3708308124, -14645930905, -3807389812, 12506179074], ![-84568628190, 2422594176, 9568015374, 2487323249, -8170140522], ![191234497950, -5478197102, -21636091912, -5624568102, 18475086461]]]
  hmulB := by decide  
  f := ![![![-49784165941, -148478222414, -33466146436, -5365432710, 50992600818]], ![![-222770407830, -664399082185, -149751772590, -24008831192, 228177820686]], ![![-134516514708, -401187257240, -90425324953, -14497366704, 137781698514]], ![![-202049766228, -602601039103, -135822845292, -21775687239, 206954216988]], ![![-229536163699, -684577534229, -154299880842, -24738002944, 235107804965]]]
  g := ![![![3809619737, -7118364978, -155825651780, -40508794026, 133059722610], ![-1167940296, 2182324185, 47772499686, 12419048648, -40792998354], ![358063170, -669049554, -14645930905, -3807389812, 12506179074], ![-233918496, 437082235, 9568015374, 2487323249, -8170140522], ![528958363, -988371289, -21636091912, -5624568102, 18475086461]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [120, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 150], [0, 1]]
 g := ![![[7, 124], [108, 110], [87, 55], [58], [62, 49], [128], [1]], ![[37, 27], [120, 41], [93, 96], [58], [125, 102], [128], [1]]]
 h' := ![![[66, 150], [26, 107], [130, 84], [6, 120], [110, 71], [97, 7], [31, 66], [0, 1]], ![[0, 1], [142, 44], [87, 67], [74, 31], [115, 80], [106, 144], [8, 85], [66, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [47, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [120, 85, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-231905, -496296, -401592, -195424, 760417]
  a := ![39, 60, 34, 44, -155]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163434, -324685, -401592, -195424, 760417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-463612492, -1846089739, 869061271, 533921202, -1089348663]] ![![1377293108993, -39454612690, -155825651780, -40508794026, 133059722610]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-828597098, -3033979429, 1390106755, 619551792, -1398410547]]]
 hmul := by decide  
 g := ![![![![-5487398, -20092579, 9206005, 4102992, -9260997]]]]
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


lemma PB1321I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1321I3 : PrimesBelowBoundCertificateInterval O 103 151 1321 where
  m := 9
  g := ![4, 1, 3, 2, 2, 3, 4, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1321I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2, I107N3]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1, I139N2, I139N3]
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
    · exact ![11449, 107, 107, 107]
    · exact ![15386239549]
    · exact ![12769, 12769, 113]
    · exact ![2048383, 16129]
    · exact ![294499921, 131]
    · exact ![18769, 18769, 137]
    · exact ![19321, 139, 139, 139]
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
      exact NI107N3
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
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
      exact NI139N3
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I107N3, I113N2, I131N1, I137N2, I139N1, I139N2, I139N3]
  Il := ![[I107N1, I107N2, I107N3], [], [I113N2], [], [I131N1], [I137N2], [I139N1, I139N2, I139N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
