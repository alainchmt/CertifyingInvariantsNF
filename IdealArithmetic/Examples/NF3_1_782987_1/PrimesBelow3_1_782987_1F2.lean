
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-668995104373265833751221, 43854121186123032209385, -13186024493107311751688]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-668995104373265833751221, 43854121186123032209385, -13186024493107311751688]] 
 ![![83, 0, 0], ![0, 83, 0], ![50, 73, 1]] where
  M :=![![![-668995104373265833751221, 43854121186123032209385, -13186024493107311751688], ![1555950890186662786699184, -101996051169651428428637, 30668096693015720457697], ![-3618835409775855014008246, 237222732386986807018213, -71327954476635707970940]]]
  hmulB := by decide  
  f := ![![![-211321503293, -107884647932, -7320079483]], ![![863769378994, 103441914476, -115204727415]], ![![796183702854, 96079518289, -105876046848]]]
  g := ![![![-116793731540966821287, 12125709749192250482923, -13186024493107311751688], ![271639223323816431498, -28202013370599988214946, 30668096693015720457697], ![-631779348723730306762, 65592330231101126372251, -71327954476635707970940]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [62, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 82], [0, 1]]
 g := ![![[43, 70], [44, 28], [41], [44], [74, 17], [1]], ![[7, 13], [13, 55], [41], [44], [70, 66], [1]]]
 h' := ![![[73, 82], [11, 30], [52, 51], [42, 46], [60, 58], [21, 73], [0, 1]], ![[0, 1], [43, 53], [40, 32], [80, 37], [61, 25], [38, 10], [73, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [64, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [62, 10, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-292, -257, -49]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 40, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-211321503293, -107884647932, -7320079483]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-211321503293, -107884647932, -7320079483]] 
 ![![83, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![-211321503293, -107884647932, -7320079483], ![863769378994, 103441914476, -115204727415], ![13594157834970, 5817572657839, -11762812939]]]
  hmulB := by decide  
  f := ![![![-668995104373265833751221, 43854121186123032209385, -13186024493107311751688]], ![![-53795241556297948398335, 3526398066330793511516, -1060314743915061268765]], ![![-59720790584607068451936, 3914831021195576764301, -1177108475456028090052]]]
  g := ![![![9328680567, -107884647932, -7320079483], ![1966284380, 103441914476, -115204727415], ![-466752656141, 5817572657839, -11762812939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-668995104373265833751221, 43854121186123032209385, -13186024493107311751688]] ![![-211321503293, -107884647932, -7320079483]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1262479806185316560293562751, 82758367069593859994263812, -24883724167172248740951841]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-1262479806185316560293562751, 82758367069593859994263812, -24883724167172248740951841]] 
 ![![89, 0, 0], ![0, 89, 0], ![25, 37, 1]] where
  M :=![![![-1262479806185316560293562751, 82758367069593859994263812, -24883724167172248740951841], ![2936279451726325351432317238, -192479666996909864432633588, 57874642902421611253311971], ![-6829207862485750127890812578, 447669806922196067539902485, -134605024094488253179321617]]]
  hmulB := by decide  
  f := ![![![11603910724451, 4988019424729, -510164696]], ![![60199434128, 11625847806379, 4987509260033]], ![![-3328100511347, 3825327592213, 2259982534497]]]
  g := ![![![-7195356202314722941233334, 11274788328707495094488561, -24883724167172248740951841], ![16734981788379607529208067, -26222937689736061582080635, 57874642902421611253311971], ![-38922272585657795487727777, 60989389869868106013200026, -134605024094488253179321617]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [36, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 88], [0, 1]]
 g := ![![[29, 47], [68], [17], [56, 34], [81, 42], [1]], ![[0, 42], [68], [17], [71, 55], [21, 47], [1]]]
 h' := ![![[24, 88], [4, 74], [82, 35], [31, 27], [21, 37], [53, 24], [0, 1]], ![[0, 1], [0, 15], [32, 54], [56, 62], [19, 52], [6, 65], [24, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [36, 65, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![326, -1059, -197]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, 70, -197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11603910724451, -4988019424729, 510164696]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-11603910724451, -4988019424729, 510164696]] 
 ![![89, 0, 0], ![51, 1, 0], ![69, 0, 1]] where
  M :=![![![-11603910724451, -4988019424729, 510164696], ![-60199434128, -11625847806379, -4987509260033], ![588526092683894, 214402698747291, -16613357066412]]]
  hmulB := by decide  
  f := ![![![1262479806185316560293562751, -82758367069593859994263812, 24883724167172248740951841]], ![![690451580491290103635273967, -45260641051150303317694616, 13608935838464753646463280]], ![![1055509151564860593125243173, -69190979041844633788136017, 20804292040779476587696614]]]
  g := ![![![2727526725536, -4988019424729, 510164696], ![10528046939702, -11625847806379, -4987509260033], ![-103367302312871, 214402698747291, -16613357066412]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-1262479806185316560293562751, 82758367069593859994263812, -24883724167172248740951841]] ![![-11603910724451, -4988019424729, 510164696]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [94, 4, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 28, 10], [24, 68, 87], [0, 1]]
 g := ![![[86, 39, 79], [35, 70], [91, 22], [50, 96], [22, 81], [1]], ![[81, 83, 62, 45], [8, 47], [19, 4], [0, 49], [92, 50], [80, 82, 79, 30]], ![[35, 33, 4, 55], [8, 88], [57, 88], [87, 31], [82, 33], [5, 51, 9, 67]]]
 h' := ![![[64, 28, 10], [35, 53, 51], [67, 31, 78], [52, 47, 33], [75, 34, 22], [3, 93, 88], [0, 1]], ![[24, 68, 87], [59, 44, 21], [61, 75, 85], [2, 59, 95], [83, 17, 90], [96, 28, 27], [64, 28, 10]], ![[0, 1], [56, 0, 25], [56, 88, 31], [51, 88, 66], [9, 46, 82], [65, 73, 79], [24, 68, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 38], []]
 b := ![[], [63, 15, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [94, 4, 9, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255886, 16684, -5238]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2638, 172, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191136697658076888415, -12529436833570386698, 3767341734454350880]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![191136697658076888415, -12529436833570386698, 3767341734454350880]] 
 ![![101, 0, 0], ![0, 101, 0], ![81, 15, 1]] where
  M :=![![![191136697658076888415, -12529436833570386698, 3767341734454350880], ![-444546324665613403840, 29141003076539800575, -8762095099116035818], ![1033927221695692226524, -67776235403623863666, 20378907977423764757]]]
  hmulB := by decide  
  f := ![![![-3488232213, -1803694294, -130663436]], ![![15418285448, 2130295535, -1934357730]], ![![1752293907, -153951851, -390130361]]]
  g := ![![![-1128890919135896365, -683560028221640098, 3767341734454350880], ![2625578003591935618, 1589826035280003345, -8762095099116035818], ![-6106577470055769493, -3697622327376042921, 20378907977423764757]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [53, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 100], [0, 1]]
 g := ![![[], [97], [], [], [82], [0, 1]], ![[], [97], [], [], [82], [0, 100]]]
 h' := ![![[0, 100], [10], [0, 81], [9], [98], [0, 48], [0, 1]], ![[0, 1], [10], [0, 20], [9], [98], [0, 53], [0, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [0, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [53, 0, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-300, -1189, -389]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![309, 46, -389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3488232213, 1803694294, 130663436]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![3488232213, 1803694294, 130663436]] 
 ![![101, 0, 0], ![85, 1, 0], ![47, 0, 1]] where
  M :=![![![3488232213, 1803694294, 130663436], ![-15418285448, -2130295535, 1934357730], ![-228254212140, -98595667838, -195937805]]]
  hmulB := by decide  
  f := ![![![-191136697658076888415, 12529436833570386698, -3767341734454350880]], ![![-156456168081890317935, 10256050770068743255, -3083781706232710782]], ![![-99181703085399069129, 6501581847340911272, -1954890787096814417]]]
  g := ![![![-1544227369, 1803694294, 130663436], ![740020017, -2130295535, 1934357730], ![80807788425, -98595667838, -195937805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![191136697658076888415, -12529436833570386698, 3767341734454350880]] ![![3488232213, 1803694294, 130663436]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [65, 53, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 38, 96], [10, 64, 7], [0, 1]]
 g := ![![[67, 25, 28], [54, 89, 17], [46, 15, 56], [28, 61], [99, 52], [1]], ![[14, 95, 67, 75], [55, 8, 48, 75], [33, 3, 37, 77], [54, 16], [28, 29], [79, 11, 52, 69]], ![[32, 1, 39, 79], [67, 89, 96, 32], [66, 90, 61, 92], [28, 91], [16, 55], [77, 61, 7, 34]]]
 h' := ![![[74, 38, 96], [95, 14, 53], [100, 0, 74], [80, 33, 46], [56, 14, 24], [38, 50, 84], [0, 1]], ![[10, 64, 7], [11, 92, 101], [89, 95, 101], [71, 52, 35], [64, 84, 99], [37, 23, 82], [74, 38, 96]], ![[0, 1], [38, 100, 52], [29, 8, 31], [68, 18, 22], [31, 5, 83], [12, 30, 40], [10, 64, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 83], []]
 b := ![[], [9, 75, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [65, 53, 19, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45011, -22969, -1545]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-437, -223, -15]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-898332907, -368219902, 7750624]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-898332907, -368219902, 7750624]] 
 ![![107, 0, 0], ![14, 1, 0], ![18, 0, 1]] where
  M :=![![![-898332907, -368219902, 7750624], ![-914573632, -1231609739, -360469278], ![42535374804, 14585605322, -1592079017]]]
  hmulB := by decide  
  f := ![![![7218482642209044079, -473187636952775406, 142277706220897892]], ![![787569978101501550, -51626968622695523, 15523158470660682]], ![![1579252891459105982, -103523549324721266, 31127383700511395]]]
  g := ![![![38478827, -368219902, 7750624], ![213237474, -1231609739, -360469278], ![-1243043714, 14585605322, -1592079017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-497132597611, 32588150554, -9798580835]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-497132597611, 32588150554, -9798580835]] 
 ![![107, 0, 0], ![16, 1, 0], ![65, 0, 1]] where
  M :=![![![-497132597611, 32588150554, -9798580835], ![1156232538530, -75793621706, 22789569719], ![-2689169226842, 176281040613, -53004051987]]]
  hmulB := by decide  
  f := ![![![-1632075, -398943, 130184]], ![![-387616, -127225, 16955]], ![![-695059, -277910, 9002]]]
  g := ![![![-3566684600, 32588150554, -9798580835], ![8295406113, -75793621706, 22789569719], ![-19293481285, 176281040613, -53004051987]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11532407, 755975, -227306]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-11532407, 755975, -227306]] 
 ![![107, 0, 0], ![76, 1, 0], ![2, 0, 1]] where
  M :=![![![-11532407, 755975, -227306], ![26822108, -1758249, 528669], ![-62382942, 4089341, -1229580]]]
  hmulB := by decide  
  f := ![![![11709, 4846, -81]], ![![8406, 3584, -13]], ![![-5036, -1735, 185]]]
  g := ![![![-640485, 755975, -227306], ![1489642, -1758249, 528669], ![-3464614, 4089341, -1229580]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-898332907, -368219902, 7750624]] ![![-497132597611, 32588150554, -9798580835]]
  ![![11709, 4846, -81]] where
 M := ![![![11709, 4846, -81]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![11709, 4846, -81]] ![![-11532407, 755975, -227306]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15653, -2246, 1928]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-15653, -2246, 1928]] 
 ![![109, 0, 0], ![0, 109, 0], ![34, 34, 1]] where
  M :=![![![-15653, -2246, 1928], ![-227504, -98557, -318], ![37524, -213830, -98875]]]
  hmulB := by decide  
  f := ![![![88778215, -5819610, 1749836]], ![![-206480648, 13535267, -4069774]], ![![-32308710, 2117908, -636811]]]
  g := ![![![-745, -622, 1928], ![-1988, -805, -318], ![31186, 28880, -98875]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [84, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 108], [0, 1]]
 g := ![![[57, 61], [66], [26, 81], [49, 16], [73], [8, 1]], ![[0, 48], [66], [20, 28], [68, 93], [73], [16, 108]]]
 h' := ![![[8, 108], [31, 37], [105, 75], [26, 9], [78, 105], [91, 89], [0, 1]], ![[0, 1], [0, 72], [51, 34], [98, 100], [46, 4], [40, 20], [8, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [16, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [84, 101, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4416, 162, 460]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-184, -142, 460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88778215, -5819610, 1749836]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![88778215, -5819610, 1749836]] 
 ![![109, 0, 0], ![74, 1, 0], ![83, 0, 1]] where
  M :=![![![88778215, -5819610, 1749836], ![-206480648, 13535267, -4069774], ![480233332, -31480366, 9465493]]]
  hmulB := by decide  
  f := ![![![-15653, -2246, 1928]], ![![-12714, -2429, 1306]], ![![-11575, -3672, 561]]]
  g := ![![![3432963, -5819610, 1749836], ![-7984396, 13535267, -4069774], ![18570133, -31480366, 9465493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-15653, -2246, 1928]] ![![88778215, -5819610, 1749836]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75203478753, -37898386970, -2392280622]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-75203478753, -37898386970, -2392280622]] 
 ![![113, 0, 0], ![0, 113, 0], ![72, 57, 1]] where
  M :=![![![-75203478753, -37898386970, -2392280622], ![282289113396, 27664587993, -40290667592], ![4754298775856, 2014787819852, -12626079599]]]
  hmulB := by decide  
  f := ![![![-715290717061895159129, 46888901853367176398, -14098520083650635822]], ![![1663625369870775026996, -109054353464917818783, 32790381769716540576]], ![![349172118631426312332, -22889011152963851219, 6882250824387573057]]]
  g := ![![![858767487, 871341668, -2392280622], ![28170063540, 20568430449, -40290667592], ![50118376168, 24198888115, -12626079599]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [64, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 112], [0, 1]]
 g := ![![[83, 83], [97], [8], [32], [58, 14], [112, 1]], ![[0, 30], [97], [8], [32], [44, 99], [111, 112]]]
 h' := ![![[112, 112], [14, 14], [81, 53], [49, 11], [17, 91], [64, 50], [0, 1]], ![[0, 1], [0, 99], [28, 60], [38, 102], [39, 22], [14, 63], [112, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [39, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [64, 1, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![654, 94, -38]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 20, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-715290717061895159129, 46888901853367176398, -14098520083650635822]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-715290717061895159129, 46888901853367176398, -14098520083650635822]] 
 ![![113, 0, 0], ![55, 1, 0], ![26, 0, 1]] where
  M :=![![![-715290717061895159129, 46888901853367176398, -14098520083650635822], ![1663625369870775026996, -109054353464917818783, 32790381769716540576], ![-3869265048826551787968, 253638953772963782228, -76263971695201278207]]]
  hmulB := by decide  
  f := ![![![-75203478753, -37898386970, -2392280622]], ![![-34105329363, -18201298189, -1520938954]], ![![24769985206, 9109997864, -662171467]]]
  g := ![![![-25908130945328967519, 46888901853367176398, -14098520083650635822], ![60257211366625000045, -109054353464917818783, 32790381769716540576], ![-140146409223578111302, 253638953772963782228, -76263971695201278207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-75203478753, -37898386970, -2392280622]] ![![-715290717061895159129, 46888901853367176398, -14098520083650635822]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70802474593, -4641260124, 1395530637]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![70802474593, -4641260124, 1395530637]] 
 ![![127, 0, 0], ![0, 127, 0], ![75, 55, 1]] where
  M :=![![![70802474593, -4641260124, 1395530637], ![-164672615166, 10794657202, -3245729487], ![382996079466, -25106247225, 7548927715]]]
  hmulB := by decide  
  f := ![![![60865, 33105, 2982]], ![![-351876, -67361, 36087]], ![![-149973, -24611, 17143]]]
  g := ![![![-266632466, -640909017, 1395530637], ![620134617, 1490628181, -3245729487], ![-1442311017, -3466907650, 7548927715]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [101, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 126], [0, 1]]
 g := ![![[9, 82], [6, 113], [50, 115], [119, 13], [76, 120], [107, 1]], ![[20, 45], [32, 14], [36, 12], [113, 114], [89, 7], [87, 126]]]
 h' := ![![[107, 126], [29, 35], [30, 42], [46, 78], [71, 93], [115, 45], [0, 1]], ![[0, 1], [91, 92], [79, 85], [10, 49], [116, 34], [104, 82], [107, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [101, 20, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-843, -796, -123]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 47, -123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-60865, -33105, -2982]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-60865, -33105, -2982]] 
 ![![127, 0, 0], ![71, 1, 0], ![39, 0, 1]] where
  M :=![![![-60865, -33105, -2982], ![351876, 67361, -36087], ![4258266, 1903617, 31274]]]
  hmulB := by decide  
  f := ![![![-70802474593, 4641260124, -1395530637]], ![![-38285851031, 2509722926, -754621620]], ![![-24758209359, 1622955843, -487989154]]]
  g := ![![![18944, -33105, -2982], ![-23806, 67361, -36087], ![-1040301, 1903617, 31274]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![70802474593, -4641260124, 1395530637]] ![![-60865, -33105, -2982]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80173, -23460, -24908]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![80173, -23460, -24908]] 
 ![![131, 0, 0], ![18, 1, 0], ![69, 0, 1]] where
  M :=![![![80173, -23460, -24908], ![2939144, 1151217, -48368], ![5707424, 5018968, 1102849]]]
  hmulB := by decide  
  f := ![![![-1512375961457, 99139617404, -29809226316]], ![![-180956325198, 11862090713, -3566684600]], ![![-859045248007, 56312331980, -16931950035]]]
  g := ![![![16955, -23460, -24908], ![-110270, 1151217, -48368], ![-1226951, 5018968, 1102849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1095981, -71844, 21602]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1095981, -71844, 21602]] 
 ![![131, 0, 0], ![56, 1, 0], ![8, 0, 1]] where
  M :=![![![1095981, -71844, 21602], ![-2549036, 167095, -50242], ![5928556, -388630, 116853]]]
  hmulB := by decide  
  f := ![![![3575, 1672, 58]], ![![1476, 723, 38]], ![![-1340, -518, 25]]]
  g := ![![![37759, -71844, 21602], ![-87820, 167095, -50242], ![204252, -388630, 116853]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![80173, -23460, -24908]] ![![1095981, -71844, 21602]]
  ![![-3575, -1672, -58]] where
 M := ![![![-3575, -1672, -58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-3575, -1672, -58]] ![![1095981, -71844, 21602]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [136, 19, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 67, 6], [30, 69, 131], [0, 1]]
 g := ![![[70, 35, 49], [57, 76], [36, 101], [131, 39, 37], [58, 126], [100, 1], []], ![[88, 48, 43, 35], [20, 17], [127, 77], [101, 39, 91, 94], [111, 130], [19, 103], [20, 36]], ![[126, 24, 64, 116], [108, 121], [130, 38], [122, 134, 29, 12], [119, 69], [70, 105], [32, 36]]]
 h' := ![![[70, 67, 6], [35, 132, 7], [72, 104, 79], [131, 114, 52], [57, 84, 41], [100, 19, 117], [0, 0, 1], [0, 1]], ![[30, 69, 131], [12, 34, 42], [102, 55, 47], [89, 65, 25], [102, 39, 45], [26, 23, 104], [125, 131, 69], [70, 67, 6]], ![[0, 1], [107, 108, 88], [100, 115, 11], [92, 95, 60], [100, 14, 51], [114, 95, 53], [110, 6, 67], [30, 69, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 28], []]
 b := ![[], [39, 86, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [136, 19, 37, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-172894, -102202, 5754]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1262, -746, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB251I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB251I2 : PrimesBelowBoundCertificateInterval O 79 137 251 where
  m := 11
  g := ![2, 2, 1, 2, 1, 3, 2, 2, 2, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB251I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N1]
    · exact ![I137N0]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I101N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1, I131N0, I131N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [I131N0, I131N1, I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
