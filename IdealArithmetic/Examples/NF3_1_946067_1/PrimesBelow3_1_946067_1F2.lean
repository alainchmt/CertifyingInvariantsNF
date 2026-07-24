
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4377608, 1159709, -209126]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![4377608, 1159709, -209126]] 
 ![![83, 0, 0], ![0, 83, 0], ![69, 62, 1]] where
  M :=![![![4377608, 1159709, -209126], ![-44125586, -3987432, 1159709], ![244698599, 2262774, -3987432]]]
  hmulB := by decide  
  f := ![![![-159945235926, -50012721708, -6157220003]], ![![-1299173420633, -406234036046, -50012721708]], ![![-1230574188416, -384783979779, -47371939303]]]
  g := ![![![226594, 170187, -209126], ![-1495729, -914330, 1159709], ![6263029, 3005826, -3987432]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [54, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 82], [0, 1]]
 g := ![![[6, 44], [11, 7], [16], [51], [63, 64], [1]], ![[26, 39], [67, 76], [16], [51], [77, 19], [1]]]
 h' := ![![[8, 82], [70, 58], [79, 16], [69, 4], [1, 47], [29, 8], [0, 1]], ![[0, 1], [36, 25], [41, 67], [18, 79], [45, 36], [10, 75], [8, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [48, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [54, 75, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![476, 216, -34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, 28, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![159945235926, 50012721708, 6157220003]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![159945235926, 50012721708, 6157220003]] 
 ![![83, 0, 0], ![21, 1, 0], ![57, 0, 1]] where
  M :=![![![159945235926, 50012721708, 6157220003], ![1299173420633, 406234036046, 50012721708], ![10552684280388, 3299682288953, 406234036046]]]
  hmulB := by decide  
  f := ![![![-4377608, -1159709, 209126]], ![![-575954, -245379, 38939]], ![![-5954485, -823689, 191658]]]
  g := ![![![-14955222411, 50012721708, 6157220003], ![-121475499683, 406234036046, 50012721708], ![-986698600509, 3299682288953, 406234036046]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![4377608, 1159709, -209126]] ![![159945235926, 50012721708, 6157220003]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2490986715069959743343798, -778898006169795781027404, -95892529342556136961801]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-2490986715069959743343798, -778898006169795781027404, -95892529342556136961801]] 
 ![![89, 0, 0], ![0, 89, 0], ![44, 23, 1]] where
  M :=![![![-2490986715069959743343798, -778898006169795781027404, -95892529342556136961801], ![-20233323691279344898940011, -6326687888772205221815838, -778898006169795781027404], ![-164347479301826909796782244, -51389243938071176140036171, -6326687888772205221815838]]]
  hmulB := by decide  
  f := ![![![-378762757440, 478875662029, -53215013202]], ![![-11228367785622, -2507363285520, 478875662029]], ![![-1953654558523, -322159188114, 69273217531]]]
  g := ![![![19418927820252924527814, 16029552457404442349371, -95892529342556136961801], ![157732455957209769283885, 130201868012731435301286, -778898006169795781027404], ![1281199862967978875990052, 1057579522513365662491327, -6326687888772205221815838]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [54, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 88], [0, 1]]
 g := ![![[6, 87], [18], [67], [7, 68], [31, 45], [1]], ![[31, 2], [18], [67], [47, 21], [47, 44], [1]]]
 h' := ![![[32, 88], [12, 40], [70, 75], [67, 45], [17, 54], [35, 32], [0, 1]], ![[0, 1], [46, 49], [67, 14], [83, 44], [54, 35], [80, 57], [32, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [30, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [54, 57, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2534, 1309, 529]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-290, -122, 529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-378762757440, 478875662029, -53215013202]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-378762757440, 478875662029, -53215013202]] 
 ![![89, 0, 0], ![66, 1, 0], ![5, 0, 1]] where
  M :=![![![-378762757440, 478875662029, -53215013202], ![-11228367785622, -2507363285520, 478875662029], ![101042764688119, 7926658695538, -2507363285520]]]
  hmulB := by decide  
  f := ![![![-2490986715069959743343798, -778898006169795781027404, -95892529342556136961801]], ![![-2074589290852771774827311, -648696138157064345726118, -79862976885151694612430]], ![![-1986543964912097848466306, -621165550212586011743519, -76473601522303212433987]]]
  g := ![![![-356387431296, 478875662029, -53215013202], ![1706328435377, -2507363285520, 478875662029], ![-4602021267301, 7926658695538, -2507363285520]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-2490986715069959743343798, -778898006169795781027404, -95892529342556136961801]] ![![-378762757440, 478875662029, -53215013202]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135949423086781539530384232065, -42509554122312606181448556966, -5233481962623250857432158332]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-135949423086781539530384232065, -42509554122312606181448556966, -5233481962623250857432158332]] 
 ![![97, 0, 0], ![0, 97, 0], ![49, 34, 1]] where
  M :=![![![-135949423086781539530384232065, -42509554122312606181448556966, -5233481962623250857432158332], ![-1104264694113505930918185408052, -345288701591711573827670565345, -42509554122312606181448556966], ![-8969515919807959904285645519826, -2804646859006010178176127686692, -345288701591711573827670565345]]]
  hmulB := by decide  
  f := ![![![-888829780957449, 17265359016758, 11346249949272]], ![![2394058739296392, -434979782986569, 17265359016758]], ![![427714728058745, -111944710616036, 7299058464923]]]
  g := ![![![1242177248265543840039087899, 1396173532029669308981905426, -5233481962623250857432158332], ![10089726369894966721369009106, 11340578748112546766408045067, -42509554122312606181448556966], ![81954953177174301167734146207, 92115144279507044659429603454, -345288701591711573827670565345]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 96], [0, 1]]
 g := ![![[49, 96], [50], [66], [48], [95], [41, 1]], ![[8, 1], [50], [66], [48], [95], [82, 96]]]
 h' := ![![[41, 96], [20, 75], [73, 27], [44, 39], [52, 57], [64, 17], [0, 1]], ![[0, 1], [88, 22], [16, 70], [91, 58], [61, 40], [82, 80], [41, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [2, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [15, 56, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105, 59, 113]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -39, 113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![888829780957449, -17265359016758, -11346249949272]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![888829780957449, -17265359016758, -11346249949272]] 
 ![![97, 0, 0], ![63, 1, 0], ![8, 0, 1]] where
  M :=![![![888829780957449, -17265359016758, -11346249949272], ![-2394058739296392, 434979782986569, -17265359016758], ![-3642990752535938, -3084673099966712, 434979782986569]]]
  hmulB := by decide  
  f := ![![![135949423086781539530384232065, 42509554122312606181448556966, 5233481962623250857432158332]], ![![99681220088461267230230845651, 31168975374200059415040511899, 3837308430593581548450252906]], ![![103681559840228991964213601818, 32419827752417639460079547860, 3991304714357707017393070433]]]
  g := ![![![21312550501107, -17265359016758, -11346249949272], ![-305769713353775, 434979782986569, -17265359016758], ![1930016250324478, -3084673099966712, 434979782986569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-135949423086781539530384232065, -42509554122312606181448556966, -5233481962623250857432158332]] ![![888829780957449, -17265359016758, -11346249949272]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40760, 640, 539]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-40760, 640, 539]] 
 ![![101, 0, 0], ![17, 1, 0], ![14, 0, 1]] where
  M :=![![![-40760, 640, 539], ![113729, -19200, 640], ![135040, 139329, -19200]]]
  hmulB := by decide  
  f := ![![![-279469440, -87386331, -10758400]], ![![-69514880, -21736367, -2676031]], ![![-221297901, -69196874, -8519040]]]
  g := ![![![-586, 640, 539], ![4269, -19200, 640], ![-19453, 139329, -19200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6780, -2120, -261]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-6780, -2120, -261]] 
 ![![101, 0, 0], ![42, 1, 0], ![54, 0, 1]] where
  M :=![![![-6780, -2120, -261], ![-55071, -17220, -2120], ![-447320, -139871, -17220]]]
  hmulB := by decide  
  f := ![![![-1880, 69, 20]], ![![-740, 18, 9]], ![![-861, 106, 0]]]
  g := ![![![954, -2120, -261], ![7749, -17220, -2120], ![62942, -139871, -17220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-40760, 640, 539]] ![![-6780, -2120, -261]]
  ![![1880, -69, -20]] where
 M := ![![![1880, -69, -20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![1880, -69, -20]] ![![-6780, -2120, -261]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [46, 23, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 48, 70], [96, 54, 33], [0, 1]]
 g := ![![[5, 72, 83], [32, 51, 34], [90, 28, 23], [36, 63], [63, 34], [1]], ![[98, 23, 45, 87], [87, 72, 33, 24], [9, 75, 76, 22], [67, 49], [76, 41], [0, 26, 49, 10]], ![[96, 55, 45, 63], [60, 99, 63, 17], [35, 75, 25, 56], [71, 92], [39, 52], [69, 101, 83, 93]]]
 h' := ![![[79, 48, 70], [73, 99, 17], [83, 66, 31], [5, 30, 69], [42, 30, 28], [57, 80, 72], [0, 1]], ![[96, 54, 33], [10, 12, 20], [57, 38, 11], [15, 2, 58], [78, 25, 7], [81, 69, 12], [79, 48, 70]], ![[0, 1], [56, 95, 66], [60, 102, 61], [91, 71, 79], [79, 48, 68], [88, 57, 19], [96, 54, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 31], []]
 b := ![[], [77, 32, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [46, 23, 31, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1016919, -357925, -25853]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9873, -3475, -251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [19, 71, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 86, 100], [100, 20, 7], [0, 1]]
 g := ![![[32, 3, 47], [58, 30, 76], [40, 61], [30, 42, 64], [13, 87], [1]], ![[29, 43, 34, 14], [102, 55, 44, 33], [85, 48], [4, 20, 51, 11], [82, 19], [67, 97, 64, 85]], ![[33, 41, 78, 74], [78, 69, 68, 54], [21, 102], [13, 52, 74, 70], [92, 36], [19, 5, 3, 22]]]
 h' := ![![[34, 86, 100], [75, 105, 49], [37, 9, 66], [72, 10, 32], [7, 15, 8], [88, 36, 27], [0, 1]], ![[100, 20, 7], [4, 100, 31], [66, 66, 80], [41, 79, 35], [23, 105, 55], [46, 73, 74], [34, 86, 100]], ![[0, 1], [72, 9, 27], [45, 32, 68], [4, 18, 40], [63, 94, 44], [45, 105, 6], [100, 20, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 11], []]
 b := ![[], [20, 42, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [19, 71, 80, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36273, 856, 856]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-339, 8, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4231667253841465, 9337768569230166, -1213740069362820]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![4231667253841465, 9337768569230166, -1213740069362820]] 
 ![![109, 0, 0], ![0, 109, 0], ![49, 31, 1]] where
  M :=![![![4231667253841465, 9337768569230166, -1213740069362820], ![-256099154635555020, -44317935520671335, 9337768569230166], ![1970269168107565026, 117411588133651620, -44317935520671335]]]
  hmulB := by decide  
  f := ![![![7960707995197912007878782127645, 2489206203970245438549607272690, 306453832290148357863539409384]], ![![64661758613221303509206815380024, 20218861286803846322420358503005, 2489206203970245438549607272690]], ![![26787263466167705364270080142871, 8376016611536627371882137396721, 1031197168734850683052950596479]]]
  g := ![![![584448905069905, 430859731371354, -1213740069362820], ![-6547246004842506, -3062282212539509, 9337768569230166], ![37998605583673949, 13681354030040945, -44317935520671335]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [6, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 108], [0, 1]]
 g := ![![[63, 35], [71], [32, 74], [32, 75], [5], [58, 1]], ![[22, 74], [71], [73, 35], [22, 34], [5], [7, 108]]]
 h' := ![![[58, 108], [32, 97], [26, 17], [26, 69], [84, 82], [88, 88], [0, 1]], ![[0, 1], [99, 12], [31, 92], [104, 40], [44, 27], [69, 21], [58, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [60, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [6, 51, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8076, 2738, 454]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -104, 454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7960707995197912007878782127645, -2489206203970245438549607272690, -306453832290148357863539409384]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7960707995197912007878782127645, -2489206203970245438549607272690, -306453832290148357863539409384]] 
 ![![109, 0, 0], ![78, 1, 0], ![20, 0, 1]] where
  M :=![![![-7960707995197912007878782127645, -2489206203970245438549607272690, -306453832290148357863539409384], ![-64661758613221303509206815380024, -20218861286803846322420358503005, -2489206203970245438549607272690], ![-525222509037721787533967134537590, -164230006772031121051191106287624, -20218861286803846322420358503005]]]
  hmulB := by decide  
  f := ![![![-4231667253841465, -9337768569230166, 1213740069362820]], ![![-678632029028250, -6275486356690657, 782880337991466]], ![![-18852316634719214, -2790522564387660, 629291164292915]]]
  g := ![![![1764462867525543113360196085595, -2489206203970245438549607272690, -306453832290148357863539409384], ![14332050879237464389087828378974, -20218861286803846322420358503005, -2489206203970245438549607272690], ![116413717843273234687223360788598, -164230006772031121051191106287624, -20218861286803846322420358503005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![4231667253841465, 9337768569230166, -1213740069362820]] ![![-7960707995197912007878782127645, -2489206203970245438549607272690, -306453832290148357863539409384]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [16, 25, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 58, 48], [75, 54, 65], [0, 1]]
 g := ![![[24, 22, 15], [66, 105], [46, 52], [109, 1], [94, 75, 109], [1]], ![[2, 15, 52, 55], [16, 82], [12, 97], [80, 50], [105, 101, 110, 110], [63, 96, 52, 78]], ![[39, 84, 111, 74], [33, 112], [82, 102], [29, 109], [88, 38, 79, 34], [80, 6, 42, 35]]]
 h' := ![![[68, 58, 48], [85, 10, 69], [24, 79, 52], [46, 31, 74], [78, 96, 1], [97, 88, 30], [0, 1]], ![[75, 54, 65], [14, 17, 25], [48, 111, 46], [63, 38, 60], [10, 108, 29], [75, 69, 81], [68, 58, 48]], ![[0, 1], [7, 86, 19], [14, 36, 15], [14, 44, 92], [34, 22, 83], [9, 69, 2], [75, 54, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 77], []]
 b := ![[], [87, 8, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [16, 25, 83, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64071, -9831, 3277]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-567, -87, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2624537505, 820657540, 101033674]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![2624537505, 820657540, 101033674]] 
 ![![127, 0, 0], ![0, 127, 0], ![36, 87, 1]] where
  M :=![![![2624537505, 820657540, 101033674], ![21318105214, 6665884465, 820657540], ![173158740940, 54144406814, 6665884465]]]
  hmulB := by decide  
  f := ![![![-64105, -16232, 2970]], ![![626670, 54695, -16232]], ![![384154, 32689, -9847]]]
  g := ![![![-7973817, -62750174, 101033674], ![-64768238, -509695445, 820657540], ![-526087400, -4140059383, 6665884465]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [99, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126], [0, 1]]
 g := ![![[38, 68], [104, 19], [2, 37], [56, 120], [45, 84], [48, 1]], ![[0, 59], [0, 108], [0, 90], [101, 7], [13, 43], [96, 126]]]
 h' := ![![[48, 126], [118, 24], [56, 20], [44, 52], [117, 82], [74, 46], [0, 1]], ![[0, 1], [0, 103], [0, 107], [0, 75], [116, 45], [123, 81], [48, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [16, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [99, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![943, 1083, 319]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83, -210, 319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64105, 16232, -2970]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![64105, 16232, -2970]] 
 ![![127, 0, 0], ![40, 1, 0], ![51, 0, 1]] where
  M :=![![![64105, 16232, -2970], ![-626670, -54695, 16232], ![3424952, 22610, -54695]]]
  hmulB := by decide  
  f := ![![![-2624537505, -820657540, -101033674]], ![![-994485082, -310962095, -38283500]], ![![-2417402785, -755889302, -93059857]]]
  g := ![![![-3415, 16232, -2970], ![5774, -54695, 16232], ![41811, 22610, -54695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![2624537505, 820657540, 101033674]] ![![64105, 16232, -2970]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [115, 123, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 106, 19], [37, 24, 112], [0, 1]]
 g := ![![[49, 11, 91], [48, 16, 46], [50, 27], [61, 34], [15, 34], [35, 1], []], ![[15, 1, 71, 40], [11, 110, 129, 86], [6, 46], [49, 53], [3, 5], [19, 52], [26, 99]], ![[46, 77, 31, 84], [55, 76, 101, 7], [63, 84], [59, 49], [115, 44], [16, 101], [64, 99]]]
 h' := ![![[129, 106, 19], [113, 90, 109], [74, 34, 96], [45, 61, 114], [95, 99, 77], [36, 34, 54], [0, 0, 1], [0, 1]], ![[37, 24, 112], [125, 11, 3], [109, 2, 68], [119, 109, 96], [11, 26, 61], [116, 55, 108], [27, 58, 24], [129, 106, 19]], ![[0, 1], [53, 30, 19], [107, 95, 98], [4, 92, 52], [34, 6, 124], [40, 42, 100], [35, 73, 106], [37, 24, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 100], []]
 b := ![[], [46, 99, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [115, 123, 96, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1727759, -52662, 39038]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13189, -402, 298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1728730213762865, 540550661534766, 66548854614812]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1728730213762865, 540550661534766, 66548854614812]] 
 ![![137, 0, 0], ![0, 137, 0], ![9, 130, 1]] where
  M :=![![![1728730213762865, 540550661534766, 66548854614812], ![14041808323725332, 4390684398355345, 540550661534766], ![114056189583835626, 35663834785115972, 4390684398355345]]]
  hmulB := by decide  
  f := ![![![-101677471, -8251438, 2556968]], ![![539520248, 601249, -8251438]], ![![492565559, 1557388, -7657467]]]
  g := ![![![8246646147661, -59202922907962, 66548854614812], ![66984323867974, -480882493439155, 540550661534766], ![544087810209033, -3906022897818094, 4390684398355345]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [97, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 136], [0, 1]]
 g := ![![[104, 65], [32], [122], [109, 44], [39], [34], [1]], ![[66, 72], [32], [122], [117, 93], [39], [34], [1]]]
 h' := ![![[50, 136], [75, 32], [113, 124], [113, 56], [92, 110], [83, 83], [40, 50], [0, 1]], ![[0, 1], [31, 105], [11, 13], [36, 81], [112, 27], [123, 54], [74, 87], [50, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [85, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [97, 87, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![975, 18, 154]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -146, 154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101677471, -8251438, 2556968]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-101677471, -8251438, 2556968]] 
 ![![137, 0, 0], ![7, 1, 0], ![88, 0, 1]] where
  M :=![![![-101677471, -8251438, 2556968], ![539520248, 601249, -8251438], ![-1741053418, 209462728, 601249]]]
  hmulB := by decide  
  f := ![![![1728730213762865, 540550661534766, 66548854614812]], ![![190824232263251, 59668168095611, 7345931706850]], ![![1942952178065458, 607534985402740, 74795500762473]]]
  g := ![![![-1962997, -8251438, 2556968], ![9207577, 601249, -8251438], ![-23797098, 209462728, 601249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1728730213762865, 540550661534766, 66548854614812]] ![![-101677471, -8251438, 2556968]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB276I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB276I2 : PrimesBelowBoundCertificateInterval O 79 137 276 where
  m := 11
  g := ![2, 2, 2, 3, 1, 1, 2, 1, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB276I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I109N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N1], [], [], [I109N1], [], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
