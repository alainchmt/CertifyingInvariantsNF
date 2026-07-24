
import IdealArithmetic.Examples.NF5_3_1125000000_2.RI5_3_1125000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3772, 703, 1863, -5635, -2560]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-3772, 703, 1863, -5635, -2560]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3772, 703, 1863, -5635, -2560], ![-25600, 4741, 12676, -38264, -17420], ![-87100, 16244, 43005, -130108, -59108], ![-282740, 52352, 140014, -422619, -192398], ![-370375, 69281, 182643, -553109, -251065]]]
  hmulB := by decide  
  f := ![![![-215981, 70973, 158943, -19673, -25066]], ![![-125330, 39539, 90646, -11126, -14280]], ![![-71400, 21512, 50665, -6160, -7972]], ![![22805, -8395, -17651, 2236, 2792]], ![![-85448, 28191, 62991, -7803, -9935]]]
  g := ![![![-606, 703, 1863, -5635, -2560], ![-4090, 4741, 12676, -38264, -17420], ![-13996, 16244, 43005, -130108, -59108], ![-45171, 52352, 140014, -422619, -192398], ![-59655, 69281, 182643, -553109, -251065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, -4, -11, 33, 15]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![22, -4, -11, 33, 15]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![22, -4, -11, 33, 15], ![150, -28, -74, 224, 102], ![510, -95, -252, 762, 346], ![1655, -306, -820, 2474, 1127], ![2170, -407, -1069, 3240, 1469]]]
  hmulB := by decide  
  f := ![![![-44, -53, -34, 8, 6]], ![![30, -52, -61, 10, 10]], ![![28, -67, -79, 13, 13]], ![![35, -6, -19, 2, 3]], ![![-22, -18, -12, 3, 2]]]
  g := ![![![9, -4, -11, 33, 15], ![61, -28, -74, 224, 102], ![208, -95, -252, 762, 346], ![674, -306, -820, 2474, 1127], ![885, -407, -1069, 3240, 1469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 9, -4, -6, 5]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-8, 9, -4, -6, 5]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-8, 9, -4, -6, 5], ![50, -59, 30, 40, -34], ![-170, 199, -99, -134, 114], ![545, -638, 318, 431, -365], ![-1295, 1518, -758, -1023, 870]]]
  hmulB := by decide  
  f := ![![![101, -35, -70, 9, 11]], ![![55, -14, -44, 5, 7]], ![![35, -14, -19, 3, 3]], ![![38, -10, -30, 4, 5]], ![![-5, -5, 14, 0, -2]]]
  g := ![![![-1, 9, -4, -6, 5], ![5, -59, 30, 40, -34], ![-18, 199, -99, -134, 114], ![57, -638, 318, 431, -365], ![-136, 1518, -758, -1023, 870]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-3772, 703, 1863, -5635, -2560]] ![![22, -4, -11, 33, 15]]
  ![![-13908529, 2584649, 6877334, -20782788, -9451561]] where
 M := ![![![-13908529, 2584649, 6877334, -20782788, -9451561]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-13908529, 2584649, 6877334, -20782788, -9451561]] ![![22, -4, -11, 33, 15]]
  ![![-51316251458, 9536235669, 25374246494, -76679166725, -34871981358]] where
 M := ![![![-51316251458, 9536235669, 25374246494, -76679166725, -34871981358]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-51316251458, 9536235669, 25374246494, -76679166725, -34871981358]] ![![-8, 9, -4, -6, 5]]
  ![![-57210115381, 10631553819, 28288523810, -85486023929, -38877096555]] where
 M := ![![![-57210115381, 10631553819, 28288523810, -85486023929, -38877096555]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-57210115381, 10631553819, 28288523810, -85486023929, -38877096555]] ![![-8, 9, -4, -6, 5]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-63833436282, 11914220652, 31506798172, -95345883128, -43306961176]]]
 hmul := by decide  
 g := ![![![![-31916718141, 5957110326, 15753399086, -47672941564, -21653480588]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18874, -32692, 27284, 27, -4951]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![18874, -32692, 27284, 27, -4951]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 1, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![18874, -32692, 27284, 27, -4951], ![-49510, 80869, -65438, -4790, 10010], ![50050, -97299, 85659, -10168, -19590], ![-73195, 85817, -54412, -39654, -5751], ![72000, -173657, 165490, -47148, -48703]]]
  hmulB := by decide  
  f := ![![![-968098, 319806, 714054, -88477, -112625]], ![![-1126250, 357377, 816566, -100346, -128658]], ![![-912546, 290766, 662781, -81517, -104439]], ![![-577747, 188177, 423556, -52330, -66781]], ![![-255276, 84663, 188610, -23389, -29752]]]
  g := ![![![-1171, -19992, 27284, 27, -4951], ![5166, 48769, -65438, -4790, 10010], ![1439, -60986, 85659, -10168, -19590], ![22092, 46743, -54412, -39654, -5751], ![16503, -113049, 165490, -47148, -48703]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![532650, 68273, -441871, 921343, 591290]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-486485, 170048, -441871, 921343, 591290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, 51, -40, -1, 7]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-32, 51, -40, -1, 7]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-32, 51, -40, -1, 7], ![70, -123, 104, 2, -18], ![-90, 152, -125, -2, 22], ![75, -125, 102, 4, -17], ![-160, 276, -230, -2, 41]]]
  hmulB := by decide  
  f := ![![![16, -9, -12, 3, 1]], ![![14, -5, -16, 0, 4]], ![![22, -19, -1, 11, -7]], ![![-33, 42, -26, -29, 26]], ![![90, -106, 54, 72, -61]]]
  g := ![![![-31, 51, -40, -1, 7], ![70, -123, 104, 2, -18], ![-89, 152, -125, -2, 22], ![73, -125, 102, 4, -17], ![-160, 276, -230, -2, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![18874, -32692, 27284, 27, -4951]] ![![18874, -32692, 27284, 27, -4951]]
  ![![2981924731, -5053411206, 4170567354, 112039656, -714212378]] where
 M := ![![![2981924731, -5053411206, 4170567354, 112039656, -714212378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![2981924731, -5053411206, 4170567354, 112039656, -714212378]] ![![-32, 51, -40, -1, 7]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-701834482992, 1196446404099, -990455782062, -19553298471, 172399974963]]]
 hmul := by decide  
 g := ![![![![-233944827664, 398815468033, -330151927354, -6517766157, 57466658321]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![960, -313, -704, 87, 111]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![960, -313, -704, 87, 111]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![960, -313, -704, 87, 111], ![1110, -347, -800, 98, 126], ![630, -188, -445, 54, 70], ![-205, 75, 158, -20, -25], ![-200, 64, 146, -18, -23]]]
  hmulB := by decide  
  f := ![![![0, -3, 4, -3, -1]], ![![-2, 1, 0, -2, -2]], ![![-10, 4, 3, -14, -2]], ![![-9, -11, 18, -22, -25]], ![![-62, 42, -2, -72, 3]]]
  g := ![![![192, -313, -704, 87, 111], ![222, -347, -800, 98, 126], ![126, -188, -445, 54, 70], ![-41, 75, 158, -20, -25], ![-40, 64, 146, -18, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![960, -313, -704, 87, 111]] ![![960, -313, -704, 87, 111]]
  ![![90615, -45888, -82208, 11092, 13114]] where
 M := ![![![90615, -45888, -82208, 11092, 13114]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![90615, -45888, -82208, 11092, 13114]] ![![960, -313, -704, 87, 111]]
  ![![-20632980, 4686941, 13167180, -1510643, -2057105]] where
 M := ![![![-20632980, 4686941, 13167180, -1510643, -2057105]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-20632980, 4686941, 13167180, -1510643, -2057105]] ![![960, -313, -704, 87, 111]]
  ![![-5588730075, 2111371428, 4377651096, -557480572, -692924124]] where
 M := ![![![-5588730075, 2111371428, 4377651096, -557480572, -692924124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-5588730075, 2111371428, 4377651096, -557480572, -692924124]] ![![960, -313, -704, 87, 111]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-10770054380, 107470035075, 108065240200, -19289711725, -18006392525]]]
 hmul := by decide  
 g := ![![![![-2154010876, 21494007015, 21613048040, -3857942345, -3601278505]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 5, 6, 3, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 6, 0, 6], [5, 0, 1, 3, 4], [3, 0, 6], [4, 6, 1, 4, 4], [0, 1]]
 g := ![![[5, 6, 1], []], ![[6, 6, 6, 5, 4, 1, 1, 6], [4, 0, 2, 5, 4, 6, 1, 6]], ![[0, 4, 0, 1, 1, 0, 0, 4], [6, 1, 0, 5, 4, 3, 3, 1]], ![[2, 0, 0, 4, 6, 5], [1, 6]], ![[0, 5, 0, 6, 0, 4, 6, 2], [2, 5, 2, 3, 5, 4, 2, 1]]]
 h' := ![![[1, 0, 6, 0, 6], [0, 0, 0, 1], [0, 1]], ![[5, 0, 1, 3, 4], [6, 1, 0, 0, 6], [1, 0, 6, 0, 6]], ![[3, 0, 6], [3, 1, 6, 6, 6], [5, 0, 1, 3, 4]], ![[4, 6, 1, 4, 4], [2, 6, 0, 3, 4], [3, 0, 6]], ![[0, 1], [0, 6, 1, 4, 5], [4, 6, 1, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3, 0, 2], [], [], []]
 b := ![[], [0, 6, 0, 2, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 5, 6, 3, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16080016887725, 2319789871798, 8682750709892, -24504860337251, -11842877086341]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2297145269675, 331398553114, 1240392958556, -3500694333893, -1691839583763]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106444, -28810, -72390, 8609, 11359]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![106444, -28810, -72390, 8609, 11359]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 1, 9, 1, 0], ![3, 2, 10, 0, 1]] where
  M :=![![![106444, -28810, -72390, 8609, 11359], ![113590, -28241, -74838, 8746, 11718], ![58590, -12891, -36987, 4216, 5774], ![-27925, 8929, 20312, -2500, -3201], ![-21540, 5659, 14484, -1712, -2271]]]
  hmulB := by decide  
  f := ![![![-276, 476, -396, -3, 73]], ![![730, -1189, 958, 78, -158]], ![![-790, 1475, -1267, 88, 314]], ![![-621, 1227, -1083, 138, 277]], ![![-798, 1529, -1324, 119, 364]]]
  g := ![![![1883, -5467, -23951, 8609, 11359], ![2360, -5493, -24612, 8746, 11718], ![1452, -2605, -12061, 4216, 5774], ![-302, 1621, 6802, -2500, -3201], ![-405, 1083, 4782, -1712, -2271]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 3], [9, 10, 8], [0, 1]]
 g := ![![[10, 7, 5], [9, 10, 1], []], ![[5, 2, 9, 9], [7, 3, 10, 3], [2, 9]], ![[5, 10, 3, 8], [7, 7], [8, 9]]]
 h' := ![![[1, 0, 3], [2, 7, 4], [0, 0, 1], [0, 1]], ![[9, 10, 8], [5, 6, 6], [10, 7, 10], [1, 0, 3]], ![[0, 1], [5, 9, 1], [7, 4], [9, 10, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4], []]
 b := ![[], [2, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 3, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![475264341, 244723825, -599566129, 948021481, 779251536]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-686419923, -205618248, -1538570438, 948021481, 779251536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-276, 476, -396, -3, 73]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-276, 476, -396, -3, 73]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![4, 2, 1, 0, 0], ![3, 4, 0, 1, 0], ![9, 10, 0, 0, 1]] where
  M :=![![![-276, 476, -396, -3, 73], ![730, -1189, 958, 78, -158], ![-790, 1475, -1267, 88, 314], ![1205, -1445, 908, 666, -59], ![-1510, 3019, -2622, 282, 961]]]
  hmulB := by decide  
  f := ![![![106444, -28810, -72390, 8609, 11359]], ![![113590, -28241, -74838, 8746, 11718]], ![![64686, -16783, -43293, 5104, 6786]], ![![67797, -17315, -45110, 5301, 7068]], ![![188396, -48731, -125946, 14839, 19740]]]
  g := ![![![60, 50, -396, -3, 73], ![-174, -167, 958, 78, -158], ![108, 47, -1267, 88, 314], ![-354, -485, 908, 666, -59], ![-47, -225, -2622, 282, 961]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[9, 5], [10, 4], [1]], ![[10, 6], [2, 7], [1]]]
 h' := ![![[9, 10], [10, 7], [1, 9], [0, 1]], ![[0, 1], [7, 4], [5, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [10, 2, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17911, 46163, -37939, 3673, 46926]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27228, -32901, -37939, 3673, 46926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![106444, -28810, -72390, 8609, 11359]] ![![-276, 476, -396, -3, 73]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -5, 2, 1, -1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![6, -5, 2, 1, -1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![7, 5, 11, 12, 1]] where
  M :=![![![6, -5, 2, 1, -1], ![-10, 17, -12, -6, 6], ![30, -38, 23, 18, -18], ![-85, 99, -50, -64, 51], ![190, -232, 124, 140, -127]]]
  hmulB := by decide  
  f := ![![![-2, 5, 6, -1, -1]], ![![-10, 9, 12, -2, -2]], ![![-10, 6, 11, -2, -2]], ![![-5, 1, 2, -2, -1]], ![![-18, 12, 19, -5, -4]]]
  g := ![![![1, 0, 1, 1, -1], ![-4, -1, -6, -6, 6], ![12, 4, 17, 18, -18], ![-34, -12, -47, -52, 51], ![83, 31, 117, 128, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [10, 9, 11, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 4, 4, 6], [11, 2, 6, 1], [3, 6, 3, 6], [0, 1]]
 g := ![![[8, 7, 2, 1], [3, 12, 1], []], ![[1, 7, 8, 4, 2, 7], [2, 5, 10], [12, 10, 4, 0, 8, 8]], ![[6, 3, 7, 10, 3, 10], [3, 12, 1], [10, 9, 0, 8, 4, 1]], ![[4, 10, 9, 3, 0, 6], [2, 5, 10], [2, 1, 9, 3, 4, 8]]]
 h' := ![![[11, 4, 4, 6], [9, 9, 5, 12], [0, 0, 0, 1], [0, 1]], ![[11, 2, 6, 1], [10, 7, 0, 8], [2, 9, 2, 7], [11, 4, 4, 6]], ![[3, 6, 3, 6], [12, 9, 5, 7], [9, 0, 0, 12], [11, 2, 6, 1]], ![[0, 1], [3, 1, 3, 12], [7, 4, 11, 6], [3, 6, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 4, 12], []]
 b := ![[], [], [8, 5, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [10, 9, 11, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-578978037590, 678369153656, -338535441254, -457522277594, 388521320452]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-253740560058, -97249034508, -354789997402, -393829086386, 388521320452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -5, -6, 1, 1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![2, -5, -6, 1, 1]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![2, -5, -6, 1, 1], ![10, -9, -12, 2, 2], ![10, -6, -11, 2, 2], ![5, -1, -2, 2, 1], ![0, 2, 0, 2, 1]]]
  hmulB := by decide  
  f := ![![![-6, 5, -2, -1, 1]], ![![-2, 1, 0, 0, 0]], ![![-6, 6, -3, -2, 2]], ![![1, -3, 2, 4, -3]], ![![-16, 19, -10, -11, 10]]]
  g := ![![![5, -5, -6, 1, 1], ![10, -9, -12, 2, 2], ![8, -6, -11, 2, 2], ![0, -1, -2, 2, 1], ![-3, 2, 0, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![6, -5, 2, 1, -1]] ![![2, -5, -6, 1, 1]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1373, -2341, 1938, 38, -338]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![1373, -2341, 1938, 38, -338]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![14, 12, 13, 1, 0], ![4, 4, 8, 0, 1]] where
  M :=![![![1373, -2341, 1938, 38, -338], ![-3380, 5753, -4758, -104, 828], ![4140, -7071, 5857, 106, -1036], ![-3490, 5854, -4798, -201, 834], ![7590, -12971, 10734, 208, -1967]]]
  hmulB := by decide  
  f := ![![![-13231, 4239, 9632, -1186, -1518]], ![![-15180, 4655, 10850, -1324, -1708]], ![![-8540, 2489, 5979, -722, -940]], ![![-27972, 8619, 20033, -2447, -3154]], ![![-10542, 3213, 7516, -916, -1183]]]
  g := ![![![129, -85, 244, 38, -338], ![-308, 217, -590, -104, 828], ![400, -247, 751, 106, -1036], ![-236, 290, -521, -201, 834], ![738, -447, 1398, 208, -1967]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 0, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 12, 14], [5, 4, 3], [0, 1]]
 g := ![![[4, 10, 13], [13, 13], [3, 1], []], ![[3, 14, 3, 3], [15, 8], [2, 16], [6, 9]], ![[12, 10, 9, 14], [7, 16], [9, 8], [0, 9]]]
 h' := ![![[15, 12, 14], [0, 12, 8], [7, 8, 9], [0, 0, 1], [0, 1]], ![[5, 4, 3], [1, 13, 13], [0, 6, 12], [1, 7, 4], [15, 12, 14]], ![[0, 1], [5, 9, 13], [0, 3, 13], [8, 10, 12], [5, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 1], []]
 b := ![[], [15, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 0, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13891992, -54208244, 49647144, -16119942, -61292691]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28514232, 22611872, 44091054, -16119942, -61292691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13231, -4239, -9632, 1186, 1518]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![13231, -4239, -9632, 1186, 1518]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![1, 4, 1, 0, 0], ![13, 2, 0, 1, 0], ![10, 5, 0, 0, 1]] where
  M :=![![![13231, -4239, -9632, 1186, 1518], ![15180, -4655, -10850, 1324, 1708], ![8540, -2489, -5979, 722, 940], ![-2890, 1040, 2214, -279, -350], ![-2750, 867, 1988, -244, -313]]]
  hmulB := by decide  
  f := ![![![-1373, 2341, -1938, -38, 338]], ![![3380, -5753, 4758, 104, -828]], ![![471, -800, 661, 16, -114]], ![![-447, 769, -640, -5, 112]], ![![-260, 448, -372, -4, 71]]]
  g := ![![![-455, 1431, -9632, 1186, 1518], ![-486, 1621, -10850, 1324, 1708], ![-251, 899, -5979, 722, 940], ![119, -324, 2214, -279, -350], ![92, -296, 1988, -244, -313]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[9, 15], [16], [8], [1]], ![[16, 2], [16], [8], [1]]]
 h' := ![![[5, 16], [5, 7], [10, 4], [10, 5], [0, 1]], ![[0, 1], [6, 10], [13, 13], [1, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [7, 12, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2639, 3121, -1577, -2083, 1920]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![401, 235, -1577, -2083, 1920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![1373, -2341, 1938, 38, -338]] ![![13231, -4239, -9632, 1186, 1518]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135311, -25896, -81686, 9054, 12710]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![135311, -25896, -81686, 9054, 12710]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![7, 18, 5, 9, 1]] where
  M :=![![![135311, -25896, -81686, 9054, 12710], ![127100, -17237, -69900, 7256, 10796], ![53980, -1930, -24493, 2132, 3716], ![-44970, 12488, 30888, -3693, -4850], ![-26200, 4530, 15350, -1668, -2383]]]
  hmulB := by decide  
  f := ![![![-71, 104, -74, -26, 30]], ![![300, -407, 260, 160, -164]], ![![-820, 1014, -567, -564, 484]], ![![2270, -2748, 1448, 1693, -1530]], ![![827, -1038, 579, 573, -555]]]
  g := ![![![2439, -13404, -7644, -5544, 12710], ![2712, -11135, -6520, -4732, 10796], ![1472, -3622, -2267, -1648, 3716], ![-580, 5252, 2902, 2103, -4850], ![-501, 2496, 1435, 1041, -2383]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [9, 7, 13, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 7, 4, 7], [7, 18, 3, 1], [2, 12, 12, 11], [0, 1]]
 g := ![![[11, 16, 5, 11], [0, 15, 14, 6], [1], []], ![[9, 3, 1, 18, 8, 9], [10, 16, 5, 17, 12, 1], [3, 3, 7], [13, 16, 11]], ![[11, 11, 11, 10, 17, 7], [4, 0, 13, 1, 16, 4], [2, 4, 7], [11, 11, 1]], ![[18, 10, 5, 0, 7, 4], [12, 8, 6, 15, 6, 9], [6, 8, 9], [7, 14, 7]]]
 h' := ![![[15, 7, 4, 7], [0, 3, 9, 12], [10, 12, 6, 5], [0, 0, 1], [0, 1]], ![[7, 18, 3, 1], [4, 12, 11, 2], [9, 5, 13, 7], [13, 13, 17, 8], [15, 7, 4, 7]], ![[2, 12, 12, 11], [3, 16, 13, 8], [12, 7, 15, 2], [7, 0, 4, 8], [7, 18, 3, 1]], ![[0, 1], [9, 7, 5, 16], [7, 14, 4, 5], [17, 6, 16, 3], [2, 12, 12, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 15, 2], []]
 b := ![[], [], [15, 5, 1, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [9, 7, 13, 14, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-226678131554, 283803920109, -152479111428, -166119400975, 177061292946]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77163535904, -152805229101, -54620293482, -92614265131, 177061292946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -104, 74, 26, -30]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![71, -104, 74, 26, -30]] 
 ![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![71, -104, 74, 26, -30], ![-300, 407, -260, -160, 164], ![820, -1014, 567, 564, -484], ![-2270, 2748, -1448, -1693, 1530], ![5520, -6538, 3358, 4228, -3547]]]
  hmulB := by decide  
  f := ![![![-135311, 25896, 81686, -9054, -12710]], ![![-35176, 6359, 20876, -2288, -3244]], ![![-81179, 15094, 48581, -5354, -7554]], ![![-97336, 18424, 58564, -6477, -9110]], ![![-76959, 14754, 46484, -5154, -7233]]]
  g := ![![![-19, -104, 74, 26, -30], ![72, 407, -260, -160, 164], ![-207, -1014, 567, 564, -484], ![502, 2748, -1448, -1693, 1530], ![-1339, -6538, 3358, 4228, -3547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![135311, -25896, -81686, 9054, 12710]] ![![71, -104, 74, 26, -30]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-517483, 146708, 358332, -43024, -56294]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-517483, 146708, 358332, -43024, -56294]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![20, 2, 5, 1, 0], ![9, 18, 20, 0, 1]] where
  M :=![![![-517483, 146708, 358332, -43024, -56294], ![-562940, 148859, 379464, -44912, -59508], ![-297540, 71628, 193771, -22496, -30316], ![129890, -42704, -95608, 11835, 15078], ![105450, -29162, -72312, 8638, 11353]]]
  hmulB := by decide  
  f := ![![![-721, 840, -412, -580, 498]], ![![4980, -5779, 2840, 3992, -3316]], ![![-16580, 19508, -9771, -13064, 11300]], ![![-1450, 1734, -881, -1129, 1046]], ![![-16333, 19268, -9688, -12822, 11167]]]
  g := ![![![36941, 54176, 73884, -43024, -56294], ![37864, 56949, 78008, -44912, -59508], ![18488, 28796, 39677, -22496, -30316], ![-10544, -14686, -19841, 11835, 15078], ![-7369, -10904, -14894, 8638, 11353]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 3, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 2, 7], [10, 20, 16], [0, 1]]
 g := ![![[3, 21, 1], [20, 16, 1], [0, 7, 1], []], ![[7, 10], [3, 5, 14, 22], [3, 22, 18, 17], [3, 3]], ![[14, 15, 13, 16], [0, 18, 12, 9], [15, 16, 17, 18], [17, 3]]]
 h' := ![![[20, 2, 7], [3, 16, 22], [0, 16, 1], [0, 0, 1], [0, 1]], ![[10, 20, 16], [18, 10], [4, 8, 17], [6, 22, 20], [20, 2, 7]], ![[0, 1], [11, 20, 1], [13, 22, 5], [14, 1, 2], [10, 20, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 17], []]
 b := ![[], [8, 18, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 3, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7993599, 23894954, -20577558, 4057426, 25274436]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13765741, -19093902, -23754496, 4057426, 25274436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 170, -150, -2, 26]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-93, 170, -150, -2, 26]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-93, 170, -150, -2, 26], ![260, -429, 344, 8, -60], ![-300, 520, -437, -8, 76], ![250, -428, 356, 7, -62], ![-560, 952, -786, -16, 137]]]
  hmulB := by decide  
  f := ![![![-71, 26, 54, -2, -6]], ![![-52, 19, 40, 0, -4]], ![![-30, 12, 23, 4, 0]], ![![2, 0, 4, 19, 6]], ![![6, 4, -6, 20, 13]]]
  g := ![![![-59, 170, -150, -2, 26], ![164, -429, 344, 8, -60], ![-190, 520, -437, -8, 76], ![158, -428, 356, 7, -62], ![-354, 952, -786, -16, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-537, 643, -416, -278, -34]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-537, 643, -416, -278, -34]] 
 ![![23, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-537, 643, -416, -278, -34], ![-340, -1271, 1842, -1796, -1044], ![-5220, 2609, 525, -6218, -2548], ![-12570, 988, 7906, -20083, -9366], ![-19570, 6629, 5924, -26356, -11469]]]
  hmulB := by decide  
  f := ![![![340061, -59471, -199886, 21766, 31038]], ![![309200, -53173, -180878, 19632, 28076]], ![![108929, -17982, -62999, 6784, 9770]], ![![172294, -29638, -100798, 10941, 15646]], ![![115446, -20251, -67918, 7400, 10547]]]
  g := ![![![-299, 643, -416, -278, -34], ![1830, -1271, 1842, -1796, -1044], ![1475, 2609, 525, -6218, -2548], ![9924, 988, 7906, -20083, -9366], ![9322, 6629, 5924, -26356, -11469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-517483, 146708, 358332, -43024, -56294]] ![![-93, 170, -150, -2, 26]]
  ![![-460961, 245182, 429458, -58490, -68596]] where
 M := ![![![-460961, 245182, 429458, -58490, -68596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-460961, 245182, 429458, -58490, -68596]] ![![-537, 643, -416, -278, -34]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![46437, -79327, 65826, 1288, -11454]]]
 hmul := by decide  
 g := ![![![![2019, -3449, 2862, 56, -498]]]]
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


lemma PB1640I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1640I0 : PrimesBelowBoundCertificateInterval O 1 23 1640 where
  m := 9
  g := ![5, 3, 5, 1, 2, 2, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1640I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
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
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![130321, 19]
    · exact ![12167, 23, 23]
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I13N1, I17N1, I19N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N0, I11N1], [I13N1], [I17N1], [I19N1], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
