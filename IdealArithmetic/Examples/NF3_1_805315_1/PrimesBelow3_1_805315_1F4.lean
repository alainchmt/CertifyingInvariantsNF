
import IdealArithmetic.Examples.NF3_1_805315_1.RI3_1_805315_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3679362660991343573521, 665277580516955843803, -235863861395660991053]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-3679362660991343573521, 665277580516955843803, -235863861395660991053]] 
 ![![197, 0, 0], ![0, 197, 0], ![104, 189, 1]] where
  M :=![![![-3679362660991343573521, 665277580516955843803, -235863861395660991053], ![51890049507045418031660, -9382409338157234488149, 3326387902584779219015], ![-156739077615139369242992, 28340504575366891389013, -10047686918674190331952]]]
  hmulB := by decide  
  f := ![![![-183382885049, 8246210189, 7034802116]], ![![-1547656465520, 14802982272, 41231050945]], ![![-1589256482116, 18114141579, 43303780816]]]
  g := ![![![105839994538870048203, 229662677077649153060, -235863861395660991053], ![-1492661382547064064700, -3238932603688733537472, 3326387902584779219015], ![4508732801659778808528, 9783519452816187127553, -10047686918674190331952]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [50, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 196], [0, 1]]
 g := ![![[39, 134], [187], [21, 97], [10], [37], [163], [20, 1]], ![[158, 63], [187], [188, 100], [10], [37], [163], [40, 196]]]
 h' := ![![[20, 196], [194, 79], [132, 160], [181, 140], [175, 73], [152, 49], [182, 153], [0, 1]], ![[0, 1], [1, 118], [180, 37], [26, 57], [59, 124], [147, 148], [90, 44], [20, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [138, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [50, 177, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4306, -2942, 614]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346, -604, 614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183382885049, 8246210189, 7034802116]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-183382885049, 8246210189, 7034802116]] 
 ![![197, 0, 0], ![40, 1, 0], ![66, 0, 1]] where
  M :=![![![-183382885049, 8246210189, 7034802116], ![-1547656465520, 14802982272, 41231050945], ![-1504634948476, -86883618001, 6556772083]]]
  hmulB := by decide  
  f := ![![![-3679362660991343573521, 665277580516955843803, -235863861395660991053]], ![![-483677446358417892940, 87455298896045681543, -31005921590059189965]], ![![-2028309711881056066474, 366745304007543030863, -130023866856790942850]]]
  g := ![![![-4962072245, 8246210189, 7034802116], ![-24675254410, 14802982272, 41231050945], ![7806917838, -86883618001, 6556772083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-3679362660991343573521, 665277580516955843803, -235863861395660991053]] ![![-183382885049, 8246210189, 7034802116]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![6, 59, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![6, 59, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![6, 59, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![6, 59, 1], ![-220, 92, 295], ![-12936, 1549, 33]]]
  hmulB := by decide  
  f := ![![![-5, -59, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -59, 199]], ![![0, 0, 1], ![-10, -87, 295], ![-66, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [90, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 198], [0, 1]]
 g := ![![[110, 157], [134, 61], [196, 1], [5], [155], [86], [50, 1]], ![[0, 42], [0, 138], [47, 198], [5], [155], [86], [100, 198]]]
 h' := ![![[50, 198], [79, 82], [71, 114], [73, 1], [181, 123], [179, 126], [77, 22], [0, 1]], ![[0, 1], [0, 117], [0, 85], [123, 198], [162, 76], [111, 73], [182, 177], [50, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [133, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [90, 149, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-982, -1630, 2357]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -707, 2357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-96, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-96, 1, 0]] 
 ![![199, 0, 0], ![103, 1, 0], ![166, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-96, 1, 0], ![0, -95, 5], ![-220, 27, -96]]]
  hmulB := by decide  
  f := ![![![10081, -105, 0], ![20895, 0, 0]], ![![5377, -56, 0], ![11145, 0, 0]], ![![8554, -70, -1], ![17730, 40, 0]]]
  g := ![![![1, 0, 0], ![-103, 199, 0], ![-166, 0, 199]], ![![-1, 1, 0], ![45, -95, 5], ![65, 27, -96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![6, 59, 1]] ![![199, 0, 0], ![-96, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-19104, 199, 0]], ![![1194, 11741, 199], ![-796, -5572, 199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-96, 1, 0]]], ![![![6, 59, 1]], ![![-4, -28, 1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1282487595, -231890771, 82213281]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![1282487595, -231890771, 82213281]] 
 ![![211, 0, 0], ![0, 211, 0], ![162, 143, 1]] where
  M :=![![![1282487595, -231890771, 82213281], ![-18086921820, 3270355411, -1159453855], ![54633353984, -9878435181, 3502246182]]]
  hmulB := by decide  
  f := ![![![-96123, -249, 2174]], ![![-478280, -37674, -1245]], ![![-397230, -26209, 648]]]
  g := ![![![-57042957, -56817014, 82213281], ![804476790, 801290316, -1159453855], ![-2430002500, -2420377437, 3502246182]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [134, 204, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 210], [0, 1]]
 g := ![![[96, 137], [161, 188], [148], [58], [124, 82], [51], [7, 1]], ![[0, 74], [0, 23], [148], [58], [65, 129], [51], [14, 210]]]
 h' := ![![[7, 210], [159, 128], [75, 140], [101, 123], [53, 67], [103, 90], [117, 126], [0, 1]], ![[0, 1], [0, 83], [0, 71], [118, 88], [100, 144], [100, 121], [155, 85], [7, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [120, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [134, 204, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8782, -44, -49]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, 33, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96123, -249, 2174]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-96123, -249, 2174]] 
 ![![211, 0, 0], ![129, 1, 0], ![22, 0, 1]] where
  M :=![![![-96123, -249, 2174], ![-478280, -37674, -1245], ![150436, -102379, -37425]]]
  hmulB := by decide  
  f := ![![![1282487595, -231890771, 82213281]], ![![698360085, -126272768, 44768054]], ![![392644934, -70995413, 25170324]]]
  g := ![![![-530, -249, 2174], ![20896, -37674, -1245], ![67207, -102379, -37425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![1282487595, -231890771, 82213281]] ![![-96123, -249, 2174]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11682511655, -632709083, -483705174]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![11682511655, -632709083, -483705174]] 
 ![![223, 0, 0], ![0, 223, 0], ![63, 17, 1]] where
  M :=![![![11682511655, -632709083, -483705174], ![106415138280, -2010237126, -3163545415], ![117912970604, 4199882415, -1377528043]]]
  hmulB := by decide  
  f := ![![![71998550545547541, -13018293090674573, 4615434169239527]], ![![-1015395517232695940, 183596980024340197, -65091465453372865]], ![![-43312607736284263, 7831494075365617, -2776534918969658]]]
  g := ![![![189040079, 34037125, -483705174], ![1370934975, 232152623, -3163545415], ![917924831, 123846902, -1377528043]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [85, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [120, 222], [0, 1]]
 g := ![![[156, 143], [216, 171], [141, 56], [122, 94], [32, 131], [65], [120, 1]], ![[145, 80], [220, 52], [171, 167], [29, 129], [142, 92], [65], [17, 222]]]
 h' := ![![[120, 222], [149, 139], [57, 174], [111, 112], [179, 142], [69, 77], [58, 43], [0, 1]], ![[0, 1], [104, 84], [198, 49], [171, 111], [48, 81], [166, 146], [89, 180], [120, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [92, 162]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [85, 103, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4167, -4342, 2132]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-621, -182, 2132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71998550545547541, -13018293090674573, 4615434169239527]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![71998550545547541, -13018293090674573, 4615434169239527]] 
 ![![223, 0, 0], ![138, 1, 0], ![133, 0, 1]] where
  M :=![![![71998550545547541, -13018293090674573, 4615434169239527], ![-1015395517232695940, 183596980024340197, -65091465453372865], ![3067103583394945248, -554573016894752659, 196615273115014770]]]
  hmulB := by decide  
  f := ![![![11682511655, -632709083, -483705174]], ![![7706734290, -400556460, -313519549]], ![![7496354353, -358522088, -294665095]]]
  g := ![![![5626324002465388, -13018293090674573, 4615434169239527], ![-79348044194139247, 183596980024340197, -65091465453372865], ![239678693231272860, -554573016894752659, 196615273115014770]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![11682511655, -632709083, -483705174]] ![![71998550545547541, -13018293090674573, 4615434169239527]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [90, 119, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 53, 104], [26, 173, 123], [0, 1]]
 g := ![![[152, 11, 81], [145, 181, 30], [180, 108], [20, 101], [207, 40], [59, 114, 21], [1]], ![[31, 97, 201, 79], [186, 185, 144, 116], [57, 195], [73, 65], [98, 11], [76, 8, 63, 16], [38, 81, 30, 79]], ![[53, 58, 40, 201], [223, 35, 95, 93], [143, 169], [89, 29], [9, 26], [2, 41, 12, 45], [89, 131, 210, 148]]]
 h' := ![![[167, 53, 104], [116, 141, 9], [192, 115, 22], [27, 129, 73], [187, 187, 76], [138, 126, 99], [137, 108, 193], [0, 1]], ![[26, 173, 123], [115, 42, 104], [173, 37, 103], [189, 211, 167], [67, 127, 135], [48, 74, 40], [89, 125, 129], [167, 53, 104]], ![[0, 1], [180, 44, 114], [153, 75, 102], [68, 114, 214], [157, 140, 16], [112, 27, 88], [32, 221, 132], [26, 173, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 116], []]
 b := ![[], [171, 176, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [90, 119, 34, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5175146, 1309336, -397250]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22798, 5768, -1750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [227, 64, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 14, 220], [159, 214, 9], [0, 1]]
 g := ![![[58, 21, 108], [202, 174], [187, 74, 70], [27, 161], [], [180, 77, 55], [1]], ![[141, 33, 126, 132], [188, 135], [46, 4, 190, 70], [29, 12], [194, 33], [121, 185, 90, 55], [8, 1, 96, 187]], ![[79, 220, 29, 33], [198, 42], [149, 115, 85, 158], [175, 153], [34, 33], [23, 172, 133, 167], [12, 95, 119, 42]]]
 h' := ![![[116, 14, 220], [132, 224, 197], [145, 71, 116], [21, 180, 191], [215, 156, 187], [131, 88], [2, 165, 46], [0, 1]], ![[159, 214, 9], [190, 223, 67], [57, 75, 140], [104, 77, 95], [170, 207, 142], [34, 87, 124], [48, 157, 115], [116, 14, 220]], ![[0, 1], [119, 11, 194], [69, 83, 202], [0, 201, 172], [197, 95, 129], [154, 54, 105], [66, 136, 68], [159, 214, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 219], []]
 b := ![[], [170, 41, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [227, 64, 183, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3349675287, -1030738160, 370717108]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14627403, -4501040, 1618852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![24, 37, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![24, 37, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![24, 37, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![24, 37, 1], ![-220, 88, 185], ![-8096, 955, 51]]]
  hmulB := by decide  
  f := ![![![-23, -37, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -37, 233]], ![![0, 0, 1], ![-20, -29, 185], ![-40, -4, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [49, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 232], [0, 1]]
 g := ![![[126, 214], [31], [128], [116, 131], [232], [133, 32], [117, 1]], ![[0, 19], [31], [128], [65, 102], [232], [149, 201], [1, 232]]]
 h' := ![![[117, 232], [50, 133], [95, 65], [141, 214], [98, 197], [7, 89], [92, 126], [0, 1]], ![[0, 1], [0, 100], [11, 168], [15, 19], [80, 36], [168, 144], [155, 107], [117, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [61, 222]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [49, 116, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4070, -1168, 2141]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-238, -345, 2141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![48, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![48, 1, 0]] 
 ![![233, 0, 0], ![48, 1, 0], ![182, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![48, 1, 0], ![0, 49, 5], ![-220, 27, 48]]]
  hmulB := by decide  
  f := ![![![961, 20, 0], ![-4660, 0, 0]], ![![144, 3, 0], ![-698, 0, 0]], ![![742, -14, -3], ![-3598, 140, 0]]]
  g := ![![![1, 0, 0], ![-48, 233, 0], ![-182, 0, 233]], ![![0, 1, 0], ![-14, 49, 5], ![-44, 27, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![24, 37, 1]] ![![233, 0, 0], ![48, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![11184, 233, 0]], ![![5592, 8621, 233], ![932, 1864, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![48, 1, 0]]], ![![![24, 37, 1]], ![![4, 8, 1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3340025757773675, -713066617760487, -157662635339666]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-3340025757773675, -713066617760487, -157662635339666]] 
 ![![239, 0, 0], ![0, 239, 0], ![74, 64, 1]] where
  M :=![![![-3340025757773675, -713066617760487, -157662635339666], ![34685779774726520, -8309983529705144, -3565333088802435], ![149937499952361836, -12315642724587845, -7596916911944657]]]
  hmulB := by decide  
  f := ![![![80422116732035756057283886247, -14541385606474962244635964051, 5155423028867655773310564619]], ![![-1134193066350884270128324216180, 205077152904987499692033166909, -72706928032374811223179820255]], ![![-264481908625904932184636674974, 47821837767343313554628558451, -16954491846963677527706517086]]]
  g := ![![![34841042917831, 39235740769783, -157662635339666], ![1249039449146890, 919963741228664, -3565333088802435], ![2979537035298186, 1982790960836277, -7596916911944657]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [68, 181, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 238], [0, 1]]
 g := ![![[203, 116], [208, 153], [55, 133], [99, 50], [34], [216, 110], [58, 1]], ![[0, 123], [0, 86], [121, 106], [131, 189], [34], [143, 129], [116, 238]]]
 h' := ![![[58, 238], [196, 112], [84, 48], [199, 33], [9, 17], [130, 89], [119, 189], [0, 1]], ![[0, 1], [0, 127], [0, 191], [201, 206], [39, 222], [34, 150], [87, 50], [58, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [28, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [68, 181, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9788, -5804, 7871]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2478, -2132, 7871]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166516985, 5046599, 5579621]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-166516985, 5046599, 5579621]] 
 ![![239, 0, 0], ![158, 1, 0], ![138, 0, 1]] where
  M :=![![![-166516985, 5046599, 5579621], ![-1227516620, -10820619, 25232995], ![-864748456, -109245151, -15867218]]]
  hmulB := by decide  
  f := ![![![-2928275469525187, 529471052176189, -187715760339404]], ![![-1763054631423894, 318783666516004, -113019811183033]], ![![-2212741170410758, 400092958426799, -141846761194673]]]
  g := ![![![-7254675, 5046599, 5579621], ![-12552352, -10820619, 25232995], ![77764274, -109245151, -15867218]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-3340025757773675, -713066617760487, -157662635339666]] ![![-166516985, 5046599, 5579621]]
  ![![239, 0, 0]] where
 M := ![![![1567810663953864854219511, 8083929947989741059694, -34127216853843205476552]]]
 hmul := by decide  
 g := ![![![![6559877255037091440249, 33823974677781343346, -142791702317335587768]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [150, 101, 176, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 225, 106], [215, 15, 135], [0, 1]]
 g := ![![[1, 211, 123], [56, 160], [134, 82], [144, 201], [107, 126, 141], [113, 10, 128], [1]], ![[128, 55, 104, 169], [89, 174], [4, 216], [118, 4], [77, 109, 219, 192], [125, 30, 5, 64], [140, 31, 122, 235]], ![[197, 62, 70, 6], [178, 159], [209, 16], [53, 187], [3, 39, 175, 150], [17, 219, 215, 162], [153, 187, 151, 6]]]
 h' := ![![[91, 225, 106], [37, 121, 169], [22, 14, 147], [100, 216, 75], [97, 70, 116], [161, 188, 83], [91, 140, 65], [0, 1]], ![[215, 15, 135], [162, 233, 178], [4, 17, 74], [107, 159, 162], [93, 85, 2], [222, 125, 206], [172, 170, 150], [91, 225, 106]], ![[0, 1], [91, 128, 135], [194, 210, 20], [148, 107, 4], [164, 86, 123], [153, 169, 193], [203, 172, 26], [215, 15, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 142], []]
 b := ![[], [220, 196, 176], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [150, 101, 176, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-176579736, 44604280, -12442830]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-732696, 185080, -51630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [145, 86, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [233, 9, 131], [111, 241, 120], [0, 1]]
 g := ![![[194, 80, 85], [124, 125, 38], [175, 58], [117, 242, 209], [95, 99, 93], [125, 221, 115], [1]], ![[112, 206, 96, 131], [5, 181, 194, 196], [53, 207], [75, 88, 126, 169], [36, 51, 107, 118], [28, 115, 230, 243], [139, 197, 6, 135]], ![[22, 6, 5, 168], [250, 4, 35, 34], [180, 144], [149, 58, 219, 234], [160, 60, 75, 170], [36, 87, 175, 54], [236, 117, 217, 116]]]
 h' := ![![[233, 9, 131], [92, 168, 218], [43, 40, 17], [103, 175, 178], [30, 113, 65], [198, 67, 131], [106, 165, 93], [0, 1]], ![[111, 241, 120], [91, 50, 250], [154, 170, 50], [73, 250, 61], [66, 10, 97], [36, 10, 188], [117, 106, 103], [233, 9, 131]], ![[0, 1], [28, 33, 34], [173, 41, 184], [238, 77, 12], [21, 128, 89], [128, 174, 183], [99, 231, 55], [111, 241, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 193], []]
 b := ![[], [226, 91, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [145, 86, 158, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49698, -11044, 10793]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![198, -44, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀



lemma PB254I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 253 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 253 (by omega)

def PB254I4 : PrimesBelowBoundCertificateInterval O 193 253 254 where
  m := 10
  g := ![2, 2, 2, 2, 1, 1, 2, 2, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB254I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
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
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![15813251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
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
  β := ![I197N1, I199N1, I211N1, I223N1, I233N1, I239N1]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N1], [], [], [I233N1], [I239N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
