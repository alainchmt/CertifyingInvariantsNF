
import IdealArithmetic.Examples.NF3_1_470372_1.RI3_1_470372_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451634301248123914857474936431813, -18400240629231931218910969995217, -24016285457386535465873048224738]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-451634301248123914857474936431813, -18400240629231931218910969995217, -24016285457386535465873048224738]] 
 ![![83, 0, 0], ![0, 83, 0], ![58, 58, 1]] where
  M :=![![![-451634301248123914857474936431813, -18400240629231931218910969995217, -24016285457386535465873048224738], ![-2556958348139281967876467268281270, -104174215188403209841328104826439, -135969835377546241257363603502694], ![-1026574569661587153007462830493916, -41824146335700597019647155222860, -54589538128862020431557273070309]]]
  hmulB := by decide  
  f := ![![![-4338147601309817, 321844637103631, 1106897601561848]], ![![118901251694472322, -21404819952092123, 1004651167912614]], ![![79941486194555946, -14608018265555720, 1215476237717759]]]
  g := ![![![11341087413015604122447733260277, 16560774890351652118093082253489, -24016285457386535465873048224738], ![64208338599498795482537611263554, 93759954659147937145611577088311, -135969835377546241257363603502694], ![25778537853161566650877819368482, 37643000784798754072417767263314, -54589538128862020431557273070309]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [65, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 82], [0, 1]]
 g := ![![[25, 23], [79, 41], [21], [78], [62, 63], [1]], ![[0, 60], [20, 42], [21], [78], [26, 20], [1]]]
 h' := ![![[35, 82], [11, 40], [40, 37], [34, 41], [37, 59], [18, 35], [0, 1]], ![[0, 1], [0, 43], [7, 46], [58, 42], [27, 24], [81, 48], [35, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [31, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [65, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1266, -62, -625]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![452, 436, -625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4338147601309817, -321844637103631, -1106897601561848]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![4338147601309817, -321844637103631, -1106897601561848]] 
 ![![83, 0, 0], ![3, 1, 0], ![73, 0, 1]] where
  M :=![![![4338147601309817, -321844637103631, -1106897601561848], ![-118901251694472322, 21404819952092123, -1004651167912614], ![9516683255281772, -10347052228207776, 21585300898944799]]]
  hmulB := by decide  
  f := ![![![451634301248123914857474936431813, 18400240629231931218910969995217, 24016285457386535465873048224738]], ![![47130858456429562800589061175623, 1920179964772277150579048371230, 2506249298189227080180515038276]], ![![409588898322585939007266664939955, 16687249545417247903616240540647, 21780462367687700113738431246701]]]
  g := ![![![1037436222007658, -321844637103631, -1106897601561848], ![-1322604533652143, 21404819952092123, -1004651167912614], ![-18496013562446569, -10347052228207776, 21585300898944799]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-451634301248123914857474936431813, -18400240629231931218910969995217, -24016285457386535465873048224738]] ![![4338147601309817, -321844637103631, -1106897601561848]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![822717073721051985931, 33518694404763807037, 43749130742607837088]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![822717073721051985931, 33518694404763807037, 43749130742607837088]] 
 ![![89, 0, 0], ![0, 89, 0], ![44, 83, 1]] where
  M :=![![![822717073721051985931, 33518694404763807037, 43749130742607837088], ![4657868731392118791430, 189768370648854206597, 247688682562422396194], ![1870053766010177676476, 76188719920288806640, 99442723772406815537]]]
  hmulB := by decide  
  f := ![![![-6854723939, 1630686859, -1045973622]], ![![-116226524894, 13142227731, 18398815834]], ![![-109330969594, 12604724753, 16703959343]]]
  g := ![![![-12384771673636998269, -40423136598108839003, 43749130742607837088], ![-70117228105106366754, -228858340247552861545, 247688682562422396194], ![-28150854831187889968, -91882666889769403179, 99442723772406815537]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [36, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 88], [0, 1]]
 g := ![![[43, 47], [20], [85], [], [51, 68], [1]], ![[0, 42], [20], [85], [], [74, 21], [1]]]
 h' := ![![[54, 88], [80, 15], [55, 51], [0, 21], [33], [53, 54], [0, 1]], ![[0, 1], [0, 74], [50, 38], [66, 68], [33], [32, 35], [54, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [11, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [36, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7900, 2744, -2534]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1164, 2394, -2534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6854723939, 1630686859, -1045973622]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-6854723939, 1630686859, -1045973622]] 
 ![![89, 0, 0], ![62, 1, 0], ![48, 0, 1]] where
  M :=![![![-6854723939, 1630686859, -1045973622], ![-116226524894, 13142227731, 18398815834], ![217953125652, -40734620452, 5573506673]]]
  hmulB := by decide  
  f := ![![![822717073721051985931, 33518694404763807037, 43749130742607837088]], ![![625464351708958897968, 25482330603867530819, 33259941444989980850]], ![![464724419153041269676, 18933551138752264544, 24712370779972842649]]]
  g := ![![![-648882869, 1630686859, -1045973622], ![-20384132632, 13142227731, 18398815834], ![27819901948, -40734620452, 5573506673]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![822717073721051985931, 33518694404763807037, 43749130742607837088]] ![![-6854723939, 1630686859, -1045973622]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![699, -52, -178]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![699, -52, -178]] 
 ![![97, 0, 0], ![0, 97, 0], ![74, 21, 1]] where
  M :=![![![699, -52, -178], ![-19120, 3443, -164], ![1504, -1660, 3473]]]
  hmulB := by decide  
  f := ![![![120467, 4908, 6406]], ![![682032, 27787, 36268]], ![![242382, 9875, 12889]]]
  g := ![![![143, 38, -178], ![-72, 71, -164], ![-2634, -769, 3473]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [86, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 96], [0, 1]]
 g := ![![[30, 44], [2], [88], [64], [12], [39, 1]], ![[0, 53], [2], [88], [64], [12], [78, 96]]]
 h' := ![![[39, 96], [24, 74], [83, 14], [52, 66], [67, 89], [41, 77], [0, 1]], ![[0, 1], [0, 23], [47, 83], [7, 31], [46, 8], [37, 20], [39, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [3, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [86, 58, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![755369, -70306, -52259]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47655, 10589, -52259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120467, 4908, 6406]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![120467, 4908, 6406]] 
 ![![97, 0, 0], ![83, 1, 0], ![80, 0, 1]] where
  M :=![![![120467, 4908, 6406], ![682032, 27787, 36268], ![273824, 11156, 14561]]]
  hmulB := by decide  
  f := ![![![699, -52, -178]], ![![401, -9, -154]], ![![592, -60, -111]]]
  g := ![![![-8241, 4908, 6406], ![-46657, 27787, 36268], ![-18732, 11156, 14561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![699, -52, -178]] ![![120467, 4908, 6406]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3496174039085, -669572767070, 129632626012]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![3496174039085, -669572767070, 129632626012]] 
 ![![101, 0, 0], ![0, 101, 0], ![71, 50, 1]] where
  M :=![![![3496174039085, -669572767070, 129632626012], ![15339469143436, 82906488753, -6954992922724], ![-77499163884040, 12528021037288, 2890830183045]]]
  hmulB := by decide  
  f := ![![![865068972575573054755697, 35244172580080582763006, 46001252181882075531244]], ![![4897646890483102991848340, 199537282825621011781805, 260439221437041676567572]], ![![3052163981469250063338875, 124349615482493383153396, 162303087341117742053049]]]
  g := ![![![-56512301067, -70804000670, 129632626012], ![5041029372840, 3443886659653, -6954992922724], ![-2799486206735, -1307064238762, 2890830183045]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [5, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 100], [0, 1]]
 g := ![![[77, 81], [30], [36, 23], [77], [82], [19, 1]], ![[0, 20], [30], [69, 78], [77], [82], [38, 100]]]
 h' := ![![[19, 100], [31, 9], [22, 63], [10, 86], [30, 73], [6, 53], [0, 1]], ![[0, 1], [0, 92], [7, 38], [28, 15], [3, 28], [3, 48], [19, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [51, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [5, 82, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4558, 2210, -4218]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2920, 2110, -4218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![865068972575573054755697, 35244172580080582763006, 46001252181882075531244]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![865068972575573054755697, 35244172580080582763006, 46001252181882075531244]] 
 ![![101, 0, 0], ![7, 1, 0], ![44, 0, 1]] where
  M :=![![![865068972575573054755697, 35244172580080582763006, 46001252181882075531244], ![4897646890483102991848340, 199537282825621011781805, 260439221437041676567572], ![1966320551373419917154888, 80110769265059733229320, 104561844687180756261025]]]
  hmulB := by decide  
  f := ![![![3496174039085, -669572767070, 129632626012]], ![![394185023931, -45585177037, -59876876640]], ![![755767265700, -167655254592, 85095700273]]]
  g := ![![![-13917775559285171761981, 35244172580080582763006, 46001252181882075531244], ![-78796433985406711481163, 199537282825621011781805, 260439221437041676567572], ![-31635405937801499910252, 80110769265059733229320, 104561844687180756261025]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![3496174039085, -669572767070, 129632626012]] ![![865068972575573054755697, 35244172580080582763006, 46001252181882075531244]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [16, 47, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 56], [102, 46], [0, 1]]
 g := ![![[48, 93, 82], [30, 45, 66], [32, 50, 46], [8, 30], [10, 38], [1]], ![[67, 83, 64], [24, 43, 49], [4, 28, 56], [40, 32], [78, 68], [1]], ![[37, 30, 60], [51, 15, 91], [28, 25, 1], [81, 41], [75, 100], [1]]]
 h' := ![![[56, 56], [35, 42, 59], [3, 23, 90], [24, 81, 47], [96, 14, 37], [87, 56, 55], [0, 1]], ![[102, 46], [54, 55, 36], [75, 92, 20], [27, 2, 102], [7, 68, 54], [88, 59, 58], [56, 56]], ![[0, 1], [52, 6, 8], [70, 91, 96], [93, 20, 57], [16, 21, 12], [86, 91, 93], [102, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85], []]
 b := ![[], [7, 91, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [16, 47, 48, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44496, 16480, -55620]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![432, 160, -540]
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


def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4111, -553, 3186]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-4111, -553, 3186]] 
 ![![107, 0, 0], ![25, 1, 0], ![50, 0, 1]] where
  M :=![![![-4111, -553, 3186], ![345194, -56193, -11902], ![-187164, 53452, -50795]]]
  hmulB := by decide  
  f := ![![![-3490509139, -142208437, -185612704]], ![![-1000228819, -40750782, -53188566]], ![![-1705228598, -69473502, -90677915]]]
  g := ![![![-1398, -553, 3186], ![21917, -56193, -11902], ![9498, 53452, -50795]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153893402989668773, -6269841857528816, -8183496882310510]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-153893402989668773, -6269841857528816, -8183496882310510]] 
 ![![107, 0, 0], ![57, 1, 0], ![38, 0, 1]] where
  M :=![![![-153893402989668773, -6269841857528816, -8183496882310510], ![-871277979574477448, -35497136587758245, -46331424810667140], ![-349803045320691728, -14251486631886084, -18601266039953491]]]
  hmulB := by decide  
  f := ![![![770296465, -203646184, 168348710]], ![![584073379, -130265493, 67502030]], ![![5079714, -19844244, 47192609]]]
  g := ![![![4808041723525917, -6269841857528816, -8183496882310510], ![27221055595636391, -35497136587758245, -46331424810667140], ![10928783198271474, -14251486631886084, -18601266039953491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-4111, -553, 3186]] ![![-4111, -553, 3186]]
  ![![-770296465, 203646184, -168348710]] where
 M := ![![![-770296465, 203646184, -168348710]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-770296465, 203646184, -168348710]] ![![-153893402989668773, -6269841857528816, -8183496882310510]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1279458056724835882788397425555, -52126988702331769180498711671, -68036971142665962706806400280]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1279458056724835882788397425555, -52126988702331769180498711671, -68036971142665962706806400280]] 
 ![![109, 0, 0], ![0, 109, 0], ![44, 69, 1]] where
  M :=![![![-1279458056724835882788397425555, -52126988702331769180498711671, -68036971142665962706806400280], ![-7243738906003260433974093806898, -295120495846844017840492444417, -385195944737985766391374316150], ![-2908235934145192563221604849268, -118485776760015171007310217184, -154649512180182903825303998013]]]
  hmulB := by decide  
  f := ![![![278864465117231, -26539596279833, -56580512803210]], ![![-6057616190187014, 1131073477408925, -152234937191910]], ![![-3727601252695774, 701915908863629, -108377081466587]]]
  g := ![![![15726318105985930975331047585, 42591046056345134473294889061, -68036971142665962706806400280], ![89035620756588195295838312878, 241132107257561228102425095137, -385195944737985766391374316150], ![35746262401677570688915330856, 96810372143785368742556565557, -154649512180182903825303998013]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [49, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 108], [0, 1]]
 g := ![![[54, 89], [36], [74, 89], [87, 48], [5], [79, 1]], ![[0, 20], [36], [20, 20], [64, 61], [5], [49, 108]]]
 h' := ![![[79, 108], [58, 31], [80, 103], [97, 31], [57, 22], [53, 88], [0, 1]], ![[0, 1], [0, 78], [42, 6], [39, 78], [51, 87], [29, 21], [79, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [43, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [49, 30, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24914, -2058, 3534]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1198, -2256, 3534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-278864465117231, 26539596279833, 56580512803210]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-278864465117231, 26539596279833, 56580512803210]] 
 ![![109, 0, 0], ![75, 1, 0], ![0, 0, 1]] where
  M :=![![![-278864465117231, 26539596279833, 56580512803210], ![6057616190187014, -1131073477408925, 152234937191910], ![603055886093564, 367493638767612, -1180651349725047]]]
  hmulB := by decide  
  f := ![![![1279458056724835882788397425555, 52126988702331769180498711671, 68036971142665962706806400280]], ![![946817368443724327000953217647, 38574721546070887214476108438, 50348337435210394214695911350]], ![![26681063616010940946987200452, 1087025474862524504654222176, 1418802864038375264452330257]]]
  g := ![![![-20819579689034, 26539596279833, 56580512803210], ![833836027484921, -1131073477408925, 152234937191910], ![-247329972674104, 367493638767612, -1180651349725047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1279458056724835882788397425555, -52126988702331769180498711671, -68036971142665962706806400280]] ![![-278864465117231, 26539596279833, 56580512803210]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21514810201936983019, 3123503713522403797, 1685369409523761288]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-21514810201936983019, 3123503713522403797, 1685369409523761288]] 
 ![![113, 0, 0], ![0, 113, 0], ![66, 98, 1]] where
  M :=![![![-21514810201936983019, 3123503713522403797, 1685369409523761288], ![175772888801521411510, -42233713327272356033, 27864298316176515394], ![269923624679469158556, -26380887683025802720, -53042358771838209933]]]
  hmulB := by decide  
  f := ![![![-26329740697500201901328404869605842013, -1072712066378499416033996425821426657, -1400120776616409092003200931908789394]], ![![-149067619741815183104277707794506401238, -6073232404394655261345182810708065023, -7926879110552175976333562394396687782]], ![![-145187944184399317194322421787327215906, -5915168759488769147801526989267121740, -7720571938108790375593918355718465933]]]
  g := ![![![-1174771603809780779, -1434006180706249579, 1685369409523761288], ![-14719210620054235438, -24539247330199742165, 27864298316176515394], ![33369197377175141718, 45767878512894856378, -53042358771838209933]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [72, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 112], [0, 1]]
 g := ![![[67, 11], [2], [69], [91], [1, 77], [35, 1]], ![[0, 102], [2], [69], [91], [97, 36], [70, 112]]]
 h' := ![![[35, 112], [64, 24], [35, 51], [101, 42], [41, 54], [79, 23], [0, 1]], ![[0, 1], [0, 89], [12, 62], [102, 71], [10, 59], [93, 90], [35, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [49, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [72, 78, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2587, 778, -986]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![553, 862, -986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26329740697500201901328404869605842013, 1072712066378499416033996425821426657, 1400120776616409092003200931908789394]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![26329740697500201901328404869605842013, 1072712066378499416033996425821426657, 1400120776616409092003200931908789394]] 
 ![![113, 0, 0], ![39, 1, 0], ![32, 0, 1]] where
  M :=![![![26329740697500201901328404869605842013, 1072712066378499416033996425821426657, 1400120776616409092003200931908789394], ![149067619741815183104277707794506401238, 6073232404394655261345182810708065023, 7926879110552175976333562394396687782], ![59848072104221573251543576712362503196, 2438297810573736631500870233580225004, 3182504915497066689212398039331147789]]]
  hmulB := by decide  
  f := ![![![21514810201936983019, -3123503713522403797, -1685369409523761288]], ![![5869953177646202887, -704273730089392850, -828262878651355802]], ![![3703984971526675204, -651072842032664768, -7871348078957091]]]
  g := ![![![-533715882681295276708848544765584586, 1072712066378499416033996425821426657, 1400120776616409092003200931908789394], ![-3021668810329610648945649720741611891, 6073232404394655261345182810708065023, 7926879110552175976333562394396687782], ![-1213147785876639729484841589874893816, 2438297810573736631500870233580225004, 3182504915497066689212398039331147789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-21514810201936983019, 3123503713522403797, 1685369409523761288]] ![![26329740697500201901328404869605842013, 1072712066378499416033996425821426657, 1400120776616409092003200931908789394]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4690263405437325102213, -191088176952073533536, -249411314649973335234]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-4690263405437325102213, -191088176952073533536, -249411314649973335234]] 
 ![![127, 0, 0], ![69, 1, 0], ![56, 0, 1]] where
  M :=![![![-4690263405437325102213, -191088176952073533536, -249411314649973335234], ![-26554245628292973138200, -1081858724941898805541, -1412059140220788664892], ![-10661070524825008212528, -434347573866450156700, -566917331783578006631]]]
  hmulB := by decide  
  f := ![![![320511034029, -49522290584, -17658086518]], ![![159899469175, -22937340261, -13215076398]], ![![104775858136, -17544132556, -2397054583]]]
  g := ![![![176864995469718547125, -191088176952073533536, -249411314649973335234], ![1001333214528048895103, -1081858724941898805541, -1412059140220788664892], ![402017973636538747804, -434347573866450156700, -566917331783578006631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24439151783522566645413332837312112317622933, -995686714557325574352370630537334797508309, -1299586067637977846330970452302179887834728]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-24439151783522566645413332837312112317622933, -995686714557325574352370630537334797508309, -1299586067637977846330970452302179887834728]] 
 ![![127, 0, 0], ![71, 1, 0], ![53, 0, 1]] where
  M :=![![![-24439151783522566645413332837312112317622933, -995686714557325574352370630537334797508309, -1299586067637977846330970452302179887834728], ![-138363921875786956255040067587560758291134006, -5637148130429572252822546861551903707283903, -7357695010297300050861765400768988199413634], ![-55550722466672048176817210005944962617508252, -2263217514014480658995656243633161669553248, -2953987339838247801744034791704744405085395]]]
  hmulB := by decide  
  f := ![![![-22674841694751883713453, 3407093818568547450511, 1489360196154595898478]], ![![-11463598793541925051343, 1592230267104555478726, 1077455052916162137796]], ![![-7034447915453783843283, 1156799323096067702737, 213438252929020988407]]]
  g := ![![![906556429408349409363357605534284979218170, -995686714557325574352370630537334797508309, -1299586067637977846330970452302179887834728], ![5132530952208421861346726974987250232243667, -5637148130429572252822546861551903707283903, -7357695010297300050861765400768988199413634], ![2060622441258135528380379742144574562128333, -2263217514014480658995656243633161669553248, -2953987339838247801744034791704744405085395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-501379426943723265539155, -20426929657060104284918, -26661552071364852497884]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-501379426943723265539155, -20426929657060104284918, -26661552071364852497884]] 
 ![![127, 0, 0], ![114, 1, 0], ![49, 0, 1]] where
  M :=![![![-501379426943723265539155, -20426929657060104284918, -26661552071364852497884], ![-2838593764393283861201636, -115648453116005834142847, -150946192427871337853412], ![-1139646320107897162855784, -46430854486146266411688, -60602286559130269501059]]]
  hmulB := by decide  
  f := ![![![-287836295517, -120454140030, 426654795532]], ![![106348728414, -166039317067, 366777918892]], ![![-347867853739, 15733704854, 113853031753]]]
  g := ![![![24674855161086664530219, -20426929657060104284918, -26661552071364852497884], ![139698372596827376266930, -115648453116005834142847, -150946192427871337853412], ![56086481359922522941957, -46430854486146266411688, -60602286559130269501059]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-4690263405437325102213, -191088176952073533536, -249411314649973335234]] ![![-24439151783522566645413332837312112317622933, -995686714557325574352370630537334797508309, -1299586067637977846330970452302179887834728]]
  ![![154920747577535972029103139105389761510134253319105285803286226913, 6311697375530116380259136171556510152436604511869124034802798857, 8238127367234117797493330498412717746734400291107569362217990318]] where
 M := ![![![154920747577535972029103139105389761510134253319105285803286226913, 6311697375530116380259136171556510152436604511869124034802798857, 8238127367234117797493330498412717746734400291107569362217990318]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![154920747577535972029103139105389761510134253319105285803286226913, 6311697375530116380259136171556510152436604511869124034802798857, 8238127367234117797493330498412717746734400291107569362217990318]] ![![-501379426943723265539155, -20426929657060104284918, -26661552071364852497884]]
  ![![127, 0, 0]] where
 M := ![![![-104978971993683954716254654180130083243881743158604118308995830621651242726838898785907879, -4276996544228290157049267063794094024039791196873890594090111574407724542376743883960797, -5582403620486240509715177178933909624020374551013614199788995225394489201450129216248938]]]
 hmul := by decide  
 g := ![![![![-826606078690424840285469717953780183022690891012630852826738823792529470290070069180377, -33677138143529843756293441447197590740470796825778666095197728932344287735249951842211, -43955934019576696926891158889243382866302161819004836218810986026728261428741174931094]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5185544415, 894570021, 53178256]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-5185544415, 894570021, 53178256]] 
 ![![131, 0, 0], ![43, 1, 0], ![29, 0, 1]] where
  M :=![![![-5185544415, 894570021, 53178256], ![3954111606, -4247256469, 8839343698], ![94486432028, -13568624752, -7772358297]]]
  hmulB := by decide  
  f := ![![![152948936748437086189, 6231362924337021725, 8133273569352215722]], ![![56814771754382900463, 2314716726976852002, 3021204928143595892]], ![![36512789456175459671, 1487584335781009943, 1941618632600718037]]]
  g := ![![![-344994082, 894570021, 53178256], ![-532479599, -4247256469, 8839343698], ![6895692267, -13568624752, -7772358297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1417, 390, -348]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-1417, 390, -348]] 
 ![![131, 0, 0], ![89, 1, 0], ![120, 0, 1]] where
  M :=![![![-1417, 390, -348], ![-38364, 4931, 4596], ![56040, -11112, 3023]]]
  hmulB := by decide  
  f := ![![![65977165, 2688006, 3508428]], ![![47675587, 1942373, 2535216]], ![![61581888, 2508936, 3274703]]]
  g := ![![![43, 390, -348], ![-7853, 4931, 4596], ![5208, -11112, 3023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104110621433571988650661871, -4241618674982237459700241, -5536227865298697404895878]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-104110621433571988650661871, -4241618674982237459700241, -5536227865298697404895878]] 
 ![![131, 0, 0], ![130, 1, 0], ![13, 0, 1]] where
  M :=![![![-104110621433571988650661871, -4241618674982237459700241, -5536227865298697404895878], ![-589429372102294844809354342, -24014212938757305091728305, -31343731019224979787210654], ![-236645702286133749451790908, -9641291314465964313338436, -12583966104127052657823219]]]
  hmulB := by decide  
  f := ![![![23991258383349, -1797845671029, -6076771140824]], ![![18825709908156, -886229251445, -6074848570502]], ![![2754121161415, -608253885179, 303362534405]]]
  g := ![![![3963898996664137002855083, -4241618674982237459700241, -5536227865298697404895878], ![22441884070122744689687510, -24014212938757305091728305, -31343731019224979787210654], ![9010028457619032792625249, -9641291314465964313338436, -12583966104127052657823219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-5185544415, 894570021, 53178256]] ![![-1417, 390, -348]]
  ![![-23991258383349, 1797845671029, 6076771140824]] where
 M := ![![![-23991258383349, 1797845671029, 6076771140824]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-23991258383349, 1797845671029, 6076771140824]] ![![-104110621433571988650661871, -4241618674982237459700241, -5536227865298697404895878]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71554344421, 2915228431, 3805002314]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![71554344421, 2915228431, 3805002314]] 
 ![![137, 0, 0], ![0, 137, 0], ![100, 90, 1]] where
  M :=![![![71554344421, 2915228431, 3805002314], ![405109793050, 16504764259, 21542279682], ![162644577988, 6626377500, 8648852849]]]
  hmulB := by decide  
  f := ![![![99043, -19087, 3968]], ![![466718, -2619, -198806]], ![![362692, -13018, -127139]]]
  g := ![![![-2255079467, -2478357517, 3805002314], ![-12767285950, -14031389833, 21542279682], ![-5125844576, -5633360430, 8648852849]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [131, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 136], [0, 1]]
 g := ![![[68, 56], [88], [4], [16, 68], [133], [9], [1]], ![[37, 81], [88], [4], [86, 69], [133], [9], [1]]]
 h' := ![![[134, 136], [2, 59], [61, 15], [96, 135], [130, 43], [90, 74], [6, 134], [0, 1]], ![[0, 1], [99, 78], [16, 122], [102, 2], [1, 94], [5, 63], [15, 3], [134, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [112, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [131, 3, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2591, 455, -1540]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1143, 1015, -1540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99043, -19087, 3968]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![99043, -19087, 3968]] 
 ![![137, 0, 0], ![61, 1, 0], ![95, 0, 1]] where
  M :=![![![99043, -19087, 3968], ![466718, -2619, -198806], ![-2220116, 360944, 77697]]]
  hmulB := by decide  
  f := ![![![71554344421, 2915228431, 3805002314]], ![![34816969363, 1418494150, 1851441028]], ![![50805162759, 2069876485, 2701635567]]]
  g := ![![![6470, -19087, 3968], ![142431, -2619, -198806], ![-230795, 360944, 77697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![71554344421, 2915228431, 3805002314]] ![![99043, -19087, 3968]]
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


lemma PB195I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB195I2 : PrimesBelowBoundCertificateInterval O 79 137 195 where
  m := 11
  g := ![2, 2, 2, 2, 1, 3, 2, 2, 3, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB195I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![131, 131, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I107N0, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [], [I107N0, I107N0, I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
