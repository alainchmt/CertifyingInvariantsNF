
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![7, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![7, 1, 0]] 
 ![![197, 0, 0], ![7, 1, 0], ![126, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![7, 1, 0], ![3, 5, 6], ![-183, 19, 10]]]
  hmulB := by decide  
  f := ![![![15690, 26191, 31434], ![788, -1032083, 0]], ![![551, 929, 1116], ![198, -36642, 0]], ![![10031, 16751, 20105], ![623, -660114, 0]]]
  g := ![![![1, 0, 0], ![-7, 197, 0], ![-126, 0, 197]], ![![0, 1, 0], ![-4, 5, 6], ![-8, 19, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![83, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![83, 1, 0]] 
 ![![197, 0, 0], ![83, 1, 0], ![62, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![83, 1, 0], ![3, 81, 6], ![-183, 19, 86]]]
  hmulB := by decide  
  f := ![![![7067, 240062, 17784], ![4334, -583908, 0]], ![![2914, 101078, 7488], ![1971, -245856, 0]], ![![2182, 75552, 5597], ![1464, -183768, 0]]]
  g := ![![![1, 0, 0], ![-83, 197, 0], ![-62, 0, 197]], ![![0, 1, 0], ![-36, 81, 6], ![-36, 19, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3101531225736685592452, 534901071195856805867, 394792972354313799852]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-3101531225736685592452, 534901071195856805867, 394792972354313799852]] 
 ![![197, 0, 0], ![106, 1, 0], ![166, 0, 1]] where
  M :=![![![-3101531225736685592452, 534901071195856805867, 394792972354313799852], ![-70642410727251854955315, 3329733106603562993002, 4393785344238082234758], ![-154342291075508668852497, 1872467933280689514581, 6793824407291474622041]]]
  hmulB := by decide  
  f := ![![![-14394399886605287056315003781440609971950684, 2894786771958744380320051151106433866672535, -1035685256935022780255647685342794421089482]], ![![-6739043785000888457064196553104842519631369, 1355255860483952769909203096000585878991334, -484878032356167597796676603023989790348824]], ![![-14066565323366597032336560250596949496086759, 2828857579736056795657756671811619026280701, -1012097373693290933112492220747329264546529]]]
  g := ![![![-636226792808698465938, 534901071195856805867, 394792972354313799852], ![-5852601457719549153215, 3329733106603562993002, 4393785344238082234758], ![-7515729663013434236837, 1872467933280689514581, 6793824407291474622041]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![7, 1, 0]] ![![197, 0, 0], ![83, 1, 0]]
  ![![14394399886605287056315003781440609971950684, -2894786771958744380320051151106433866672535, 1035685256935022780255647685342794421089482]] where
 M := ![![![38809, 0, 0], ![16351, 197, 0]], ![![1379, 197, 0], ![584, 88, 6]]]
 hmul := by decide  
 g := ![![![![611001651470127061713044, -105375511025583790755799, -77774215553799818570844]], ![![328069502463396759128831, -47726522015859677879963, -37161602049646127622474]]], ![![![92353129307408654102479, -7074040604974560634071, -7157336150718278833722]], ![![45451168153712891549110, -3130119525681106878670, -3339975393866088038094]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![14394399886605287056315003781440609971950684, -2894786771958744380320051151106433866672535, 1035685256935022780255647685342794421089482]] ![![-3101531225736685592452, 534901071195856805867, 394792972354313799852]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [145, 188, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 172, 76], [1, 26, 123], [0, 1]]
 g := ![![[55, 166, 16], [135, 178, 2], [27, 164, 177], [197, 14], [119, 182], [132, 196], [1]], ![[131, 95, 183, 83], [177, 148, 148, 22], [103, 5, 0, 6], [165, 2], [12, 28], [36, 103], [109, 174, 46, 181]], ![[130, 102, 141, 184], [37, 116, 64, 46], [71, 62, 45, 178], [23, 165], [144, 33], [72, 18], [73, 169, 138, 18]]]
 h' := ![![[184, 172, 76], [126, 198, 4], [65, 164, 179], [31, 182, 133], [138, 197, 51], [94, 90, 111], [54, 11, 185], [0, 1]], ![[1, 26, 123], [131, 189, 28], [43, 135, 4], [53, 174, 176], [140, 30, 179], [158, 175, 174], [123, 131, 74], [184, 172, 76]], ![[0, 1], [12, 11, 167], [197, 99, 16], [187, 42, 89], [138, 171, 168], [83, 133, 113], [162, 57, 139], [1, 26, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190, 63], []]
 b := ![[], [165, 29, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [145, 188, 14, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4249645, 1159374, -327952]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21355, 5826, -1648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-96, 84, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-96, 84, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![115, 84, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-96, 84, 1], ![69, -245, 507], ![-15515, 1575, 177]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-115, -84, 211]], ![![-1, 0, 1], ![-276, -203, 507], ![-170, -63, 177]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [117, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 210], [0, 1]]
 g := ![![[116, 101], [146, 58], [24], [47], [148, 43], [79], [143, 1]], ![[0, 110], [0, 153], [24], [47], [178, 168], [79], [75, 210]]]
 h' := ![![[143, 210], [9, 177], [86, 144], [183, 119], [197, 70], [87, 185], [149, 76], [0, 1]], ![[0, 1], [0, 34], [0, 67], [109, 92], [79, 141], [167, 26], [45, 135], [143, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [67, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [117, 68, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1036, -2067, 1475]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-799, -597, 1475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-85, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-85, 1, 0]] 
 ![![211, 0, 0], ![126, 1, 0], ![34, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-85, 1, 0], ![3, -87, 6], ![-183, 19, -82]]]
  hmulB := by decide  
  f := ![![![6147, -217658, 15012], ![-3376, -527922, 0]], ![![3718, -129969, 8964], ![-1898, -315234, 0]], ![![1003, -35073, 2419], ![-513, -85068, 0]]]
  g := ![![![1, 0, 0], ![-126, 211, 0], ![-34, 0, 211]], ![![-1, 1, 0], ![51, -87, 6], ![1, 19, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-96, 84, 1]] ![![211, 0, 0], ![-85, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-17935, 211, 0]], ![![-20256, 17724, 211], ![8229, -7385, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-85, 1, 0]]], ![![![-96, 84, 1]], ![![39, -35, 2]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [114, 150, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [180, 61, 178], [212, 161, 45], [0, 1]]
 g := ![![[151, 66, 126], [188, 15, 143], [158, 118, 17], [132, 108, 36], [140, 4, 38], [118, 17], [1]], ![[38, 195, 165, 152], [140, 196, 11, 200], [151, 105, 50, 18], [89, 48, 89, 16], [66, 107, 103, 7], [37, 178], [113, 91, 204, 82]], ![[95, 9, 59, 87], [112, 222, 181, 54], [54, 166, 97, 77], [38, 27, 51, 168], [119, 118, 170, 185], [198, 81], [125, 12, 188, 141]]]
 h' := ![![[180, 61, 178], [199, 120, 168], [51, 165, 139], [116, 73, 169], [96, 52, 217], [213, 67, 22], [109, 73, 169], [0, 1]], ![[212, 161, 45], [68, 169, 17], [142, 149, 13], [163, 181, 63], [221, 170, 39], [48, 79, 81], [156, 181, 63], [180, 61, 178]], ![[0, 1], [49, 157, 38], [104, 132, 71], [36, 192, 214], [199, 1, 190], [123, 77, 120], [29, 192, 214], [212, 161, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1], []]
 b := ![[], [16, 84, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [114, 150, 54, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33642938262, 9184606448, -2732433272]
  a := ![-129, 65, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-150865194, 41186576, -12253064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45862810875325248618430, 9223243712318974419453, -3299855321469441870960]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-45862810875325248618430, 9223243712318974419453, -3299855321469441870960]] 
 ![![227, 0, 0], ![0, 227, 0], ![198, 216, 1]] where
  M :=![![![-45862810875325248618430, 9223243712318974419453, -3299855321469441870960], ![631543254965864785644039, -127006549407882593005576, 45439896309505520903838], ![-1215974288384242131212619, 244538592284918793259767, -87490041489226604650231]]]
  hmulB := by decide  
  f := ![![![470483033470, -19055390649, -27642013602]], ![![5001322317219, -16604443670, -197258384700]], ![![5202119848371, -31458578493, -212546674945]]]
  g := ![![![2676249087117287408950, 3180581467619904927519, -3299855321469441870960], ![-36852670547648583054255, -43797463225819714133192, 45439896309505520903838], ![70956184698161346209397, 84327698475585310122069, -87490041489226604650231]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [83, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 226], [0, 1]]
 g := ![![[57, 12], [146, 209], [181], [75], [175], [99, 182], [36, 1]], ![[35, 215], [179, 18], [181], [75], [175], [68, 45], [72, 226]]]
 h' := ![![[36, 226], [140, 100], [29, 45], [129, 194], [212, 23], [182, 42], [190, 78], [0, 1]], ![[0, 1], [108, 127], [60, 182], [76, 33], [132, 204], [105, 185], [47, 149], [36, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [179, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [83, 191, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1998, -3521, 382]
  a := ![-5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-342, -379, 382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![470483033470, -19055390649, -27642013602]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![470483033470, -19055390649, -27642013602]] 
 ![![227, 0, 0], ![63, 1, 0], ![41, 0, 1]] where
  M :=![![![470483033470, -19055390649, -27642013602], ![5001322317219, -16604443670, -197258384700], ![7439944433853, 218429863311, -167165424119]]]
  hmulB := by decide  
  f := ![![![-45862810875325248618430, 9223243712318974419453, -3299855321469441870960]], ![![-9946316432509365098313, 2000254645234417600969, -715643123097221660646]], ![![-13640306318381397905587, 2743134733436109006420, -981427795900765292333]]]
  g := ![![![12353723357, -19055390649, -27642013602], ![62268705027, -16604443670, -197258384700], ![2346455657, 218429863311, -167165424119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-45862810875325248618430, 9223243712318974419453, -3299855321469441870960]] ![![470483033470, -19055390649, -27642013602]]
  ![![227, 0, 0]] where
 M := ![![![227, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)


lemma PB228I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 227 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 227 (by omega)

def PB228I4 : PrimesBelowBoundCertificateInterval O 193 227 228 where
  m := 5
  g := ![3, 1, 2, 1, 2]
  P := ![197, 199, 211, 223, 227]
  hP := PB228I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
  β := ![I197N0, I197N1, I197N2, I211N1, I227N1]
  Il := ![[I197N0, I197N1, I197N2], [], [I211N1], [], [I227N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
