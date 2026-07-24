
import IdealArithmetic.Examples.NF3_1_189283_1.RI3_1_189283_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3050650969387591186372, 173432076186275861171, 166872269359178937586]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![3050650969387591186372, 173432076186275861171, 166872269359178937586]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 2]] where
  M :=![![![3050650969387591186372, 173432076186275861171, 166872269359178937586], ![12682292471297599256536, 720999005186182983753, 693728304745103444684], ![10010264672332565634862, 569091975030261896569, 547566928999907122582]]]
  hmulB := by decide  
  f := ![![![-19667739475, 6063739456, -1688537647]], ![![-64164430586, 5862032343, 12127478912]], ![![492926413949, -123038307133, 5660325230]]]
  g := ![![![1525325484693795593186, 173432076186275861171, 83436134679589468793], ![6341146235648799628268, 720999005186182983753, 346864152372551722342], ![5005132336166282817431, 569091975030261896569, 273783464499953561291]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1198, 513, -726]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![599, 513, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19667739475, 6063739456, -1688537647]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-19667739475, 6063739456, -1688537647]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-19667739475, 6063739456, -1688537647], ![-128328861172, 11724064686, 24254957824], ![492926413949, -123038307133, 5660325230]]]
  hmulB := by decide  
  f := ![![![3050650969387591186372, 173432076186275861171, 166872269359178937586]], ![![7866471720342595221454, 447215540686229422462, 430300287052141191135]], ![![6530457820860078410617, 371262025608268878870, 357219599179543030084]]]
  g := ![![![-12021470642, 6063739456, -1688537647], ![-82153941841, 11724064686, 24254957824], ![305152197926, -123038307133, 5660325230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![3050650969387591186372, 173432076186275861171, 166872269359178937586]] ![![-19667739475, 6063739456, -1688537647]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-619057226, 229256470, -101792521]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-619057226, 229256470, -101792521]] 
 ![![3, 0, 0], ![0, 3, 0], ![2, 2, 1]] where
  M :=![![![-619057226, 229256470, -101792521], ![-7736231596, 1137087059, 917025880], ![19357549619, -5372904949, 907830589]]]
  hmulB := by decide  
  f := ![![![-1986458434509775957, -112931834553308533, -108660358159843113]], ![![-8258187220148076588, -469484896665437795, -451727338213234132]], ![![-9002521310110044817, -511800916391627936, -492442818286094584]]]
  g := ![![![-138490728, 144280504, -101792521], ![-3190094452, -232321567, 917025880], ![5847296147, -2396188709, 907830589]]]
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
  c := ![230, 503, -548]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![442, 533, -548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1986458434509775957, -112931834553308533, -108660358159843113]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1986458434509775957, -112931834553308533, -108660358159843113]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-1986458434509775957, -112931834553308533, -108660358159843113], ![-8258187220148076588, -469484896665437795, -451727338213234132], ![-6518272621014429361, -370569286737391152, -356553062112129262]]]
  hmulB := by decide  
  f := ![![![-619057226, 229256470, -101792521]], ![![-2785096274, 455447843, 271744453]], ![![6246164131, -1714549493, 268679356]]]
  g := ![![![-588288747265541437, -112931834553308533, -108660358159843113], ![-2445658328423134887, -469484896665437795, -451727338213234132], ![-1930383424054969649, -370569286737391152, -356553062112129262]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-619057226, 229256470, -101792521]] ![![-1986458434509775957, -112931834553308533, -108660358159843113]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471416275420507, 26800412179107, 25786726990949]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![471416275420507, 26800412179107, 25786726990949]] 
 ![![5, 0, 0], ![0, 5, 0], ![3, 3, 1]] where
  M :=![![![471416275420507, 26800412179107, 25786726990949], ![1959791251312124, 111415782735379, 107201648716428], ![1546883512784101, 87941630141426, 84615370556272]]]
  hmulB := by decide  
  f := ![![![-959848, 1148834, -1162975]], ![![-88386100, 17633611, 4595336]], ![![-31725987, 3403660, 5356372]]]
  g := ![![![78811218889532, -10111953758748, 25786726990949], ![327637261032568, -42037832682781, 107201648716428], ![258607480223057, -33180896305478, 84615370556272]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]], ![[], [1]]]
 h' := ![![[0, 4], [3], [0, 1]], ![[0, 1], [3], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4079, 19, 113]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![748, -64, 113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![959848, -1148834, 1162975]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![959848, -1148834, 1162975]] 
 ![![5, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![959848, -1148834, 1162975], ![88386100, -17633611, -4595336], ![-109407909, 39329035, -16484777]]]
  hmulB := by decide  
  f := ![![![-471416275420507, -26800412179107, -25786726990949]], ![![-674808015514729, -38363403854540, -36912365937855]], ![![-497943212725023, -28308490899928, -27237764907634]]]
  g := ![![![416080, -1148834, 1162975], ![30095521, -17633611, -4595336], ![-38885092, 39329035, -16484777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![471416275420507, 26800412179107, 25786726990949]] ![![959848, -1148834, 1162975]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [3, 2], [0, 1]]
 g := ![![[3, 2, 4], [1]], ![[2, 2, 1], [1]], ![[3, 3, 2], [1]]]
 h' := ![![[2, 4], [3, 1, 5], [0, 1]], ![[3, 2], [4, 0, 3], [2, 4]], ![[0, 1], [2, 6, 6], [3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [5, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 6, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-702835, 305053, -186774]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100405, 43579, -26682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [6, 5, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 8, 7], [5, 2, 4], [0, 1]]
 g := ![![[1, 4, 9], [7, 10, 1], []], ![[3, 9, 0, 7], [5, 5, 9, 6], [8, 5]], ![[7, 10, 1, 9], [6, 3, 2, 3], [0, 5]]]
 h' := ![![[5, 8, 7], [2, 4, 3], [0, 0, 1], [0, 1]], ![[5, 2, 4], [8, 7, 1], [10, 10, 2], [5, 8, 7]], ![[0, 1], [9, 0, 7], [3, 1, 8], [5, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 9], []]
 b := ![[], [1, 9, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [6, 5, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-259116, 125213, -88748]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23556, 11383, -8068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34085, -3617, -5805]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![34085, -3617, -5805]] 
 ![![13, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![34085, -3617, -5805], ![-441180, 117543, -14468], ![-164597, -56040, 121160]]]
  hmulB := by decide  
  f := ![![![13430723160, 763547920, 734667871]], ![![7394379052, 420376675, 404476561]], ![![13721398767, 780073073, 750567985]]]
  g := ![![![7922, -3617, -5805], ![-49933, 117543, -14468], ![-92929, -56040, 121160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112506228, -3617870, 38870113]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-112506228, -3617870, 38870113]] 
 ![![13, 0, 0], ![4, 1, 0], ![8, 0, 1]] where
  M :=![![![-112506228, -3617870, 38870113], ![2954128588, -699175793, -14471480], ![-1013490267, 792800197, -695557923]]]
  hmulB := by decide  
  f := ![![![497790254585839499, 28299795100928251, 27229398014122209]], ![![312353482108972760, 17757558452203663, 17085905573861680]], ![![431980607852995469, 24558461273986478, 23629574498998772]]]
  g := ![![![-31461204, -3617870, 38870113], ![451277200, -699175793, -14471480], ![106136333, 792800197, -695557923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365781727, -112819300, 31461204]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![365781727, -112819300, 31461204]] 
 ![![13, 0, 0], ![5, 1, 0], ![12, 0, 1]] where
  M :=![![![365781727, -112819300, 31461204], ![2391051504, -218955633, -451277200], ![-9172029676, 2290052376, -106136333]]]
  hmulB := by decide  
  f := ![![![-1056687572070940989, -60073578178393804, -57801385646722132]], ![![-744334089961968229, -42316019726190141, -40715480072860452]], ![![-1242124344547807728, -70615814827118392, -67944878086982661]]]
  g := ![![![42487983, -112819300, 31461204], ![684704313, -218955633, -451277200], ![-1488358120, 2290052376, -106136333]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![34085, -3617, -5805]] ![![-112506228, -3617870, 38870113]]
  ![![-8636546884241, -2196601399254, 5414944887780]] where
 M := ![![![-8636546884241, -2196601399254, 5414944887780]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-8636546884241, -2196601399254, 5414944887780]] ![![365781727, -112819300, 31461204]]
  ![![13, 0, 0]] where
 M := ![![![-58077313318631573001503, 13855834829889238314362, 144837571804691011896]]]
 hmul := by decide  
 g := ![![![![-4467485639894736384731, 1065833448453018331874, 11141351677283923992]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169020491, -41541019, 1120133]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![169020491, -41541019, 1120133]] 
 ![![17, 0, 0], ![0, 17, 0], ![16, 15, 1]] where
  M :=![![![169020491, -41541019, 1120133], ![85130108, 110677477, -166164076], ![-3178399971, 644397812, 152218496]]]
  hmulB := by decide  
  f := ![![![-7289583888083312, -414418981696260, -398744208464059]], ![![-30304559843268484, -1722839742818687, -1657675926785040]], ![![-35007143676850523, -1990185593223158, -1914909823430763]]]
  g := ![![![8888139, -3431942, 1120133], ![161397372, 153125801, -166164076], ![-330229171, -96404684, 152218496]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16], [0, 1]]
 g := ![![[6, 15], [8], [13], [1]], ![[7, 2], [8], [13], [1]]]
 h' := ![![[8, 16], [4, 7], [4, 12], [7, 8], [0, 1]], ![[0, 1], [9, 10], [15, 5], [3, 9], [8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [10, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114761, 34719, -53544]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57145, 49287, -53544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7289583888083312, -414418981696260, -398744208464059]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-7289583888083312, -414418981696260, -398744208464059]] 
 ![![17, 0, 0], ![8, 1, 0], ![16, 0, 1]] where
  M :=![![![-7289583888083312, -414418981696260, -398744208464059], ![-30304559843268484, -1722839742818687, -1657675926785040], ![-23919702648098639, -1359855235373221, -1308420761122427]]]
  hmulB := by decide  
  f := ![![![169020491, -41541019, 1120133]], ![![84546708, -13038275, -9247236]], ![![-27886595, -1191676, 10008272]]]
  g := ![![![141510311818336, -414418981696260, -398744208464059], ![588292525167156, -1722839742818687, -1657675926785040], ![464345377226233, -1359855235373221, -1308420761122427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![169020491, -41541019, 1120133]] ![![-7289583888083312, -414418981696260, -398744208464059]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-4, 0, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![15, 0, 1]] where
  M :=![![![-4, 0, 1], ![76, -19, 0], ![-19, 19, -19]]]
  hmulB := by decide  
  f := ![![![-19, -1, -1]], ![![-76, -5, -4]], ![![-18, -1, -1]]]
  g := ![![![-1, 0, 1], ![4, -1, 0], ![14, 1, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [12, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[3, 1], [4, 4], [4], [1]], ![[5, 18], [12, 15], [4], [1]]]
 h' := ![![[2, 18], [9, 18], [1, 17], [7, 2], [0, 1]], ![[0, 1], [7, 1], [16, 2], [11, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [12, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1041, 209, -284]
  a := ![-1, 2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![279, 11, -284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 1, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 1, 1]] 
 ![![19, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![19, 1, 1], ![76, 5, 4], ![57, 4, 4]]]
  hmulB := by decide  
  f := ![![![4, 0, -1]], ![![-4, 1, 0]], ![![1, -1, 1]]]
  g := ![![![1, 1, 1], ![4, 5, 4], ![3, 4, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-4, 0, 1]] ![![19, 1, 1]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8209824564577, -466735438976, -449081874616]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-8209824564577, -466735438976, -449081874616]] 
 ![![23, 0, 0], ![0, 23, 0], ![3, 14, 1]] where
  M :=![![![-8209824564577, -466735438976, -449081874616], ![-34130222470816, -1940331884313, -1866941755904], ![-26939337744472, -1531524033064, -1473596445337]]]
  hmulB := by decide  
  f := ![![![39625, -132544, 155848]], ![![11844448, -2430639, -530176]], ![![6648117, -1281622, -402305]]]
  g := ![![![-298372997423, 253061339376, -449081874616], ![-1240408574048, 1052037073841, -1866941755904], ![-979067322107, 830383747898, -1473596445337]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [15, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22], [0, 1]]
 g := ![![[15, 12], [19, 1], [21, 2], [1]], ![[6, 11], [1, 22], [8, 21], [1]]]
 h' := ![![[5, 22], [14, 14], [7, 1], [8, 5], [0, 1]], ![[0, 1], [15, 9], [12, 22], [10, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [13, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [15, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2732, 1372, -1581]
  a := ![0, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![325, 1022, -1581]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39625, -132544, 155848]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![39625, -132544, 155848]] 
 ![![23, 0, 0], ![13, 1, 0], ![12, 0, 1]] where
  M :=![![![39625, -132544, 155848], ![11844448, -2430639, -530176], ![-13034456, 4949272, -2298095]]]
  hmulB := by decide  
  f := ![![![-8209824564577, -466735438976, -449081874616]], ![![-6124258339579, -348169243087, -335000266344]], ![![-5454662283452, -310102143512, -298372997423]]]
  g := ![![![-4673, -132544, 155848], ![2165429, -2430639, -530176], ![-2165124, 4949272, -2298095]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-8209824564577, -466735438976, -449081874616]] ![![39625, -132544, 155848]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-282, 26, 53]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-282, 26, 53]] 
 ![![29, 0, 0], ![5, 1, 0], ![7, 0, 1]] where
  M :=![![![-282, 26, 53], ![4028, -1051, 104], ![969, 617, -1077]]]
  hmulB := by decide  
  f := ![![![1067759, 60703, 58407]], ![![337163, 19168, 18443]], ![![378552, 21521, 20707]]]
  g := ![![![-27, 26, 53], ![295, -1051, 104], ![187, 617, -1077]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55662278798, -3164447416, -3044756963]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-55662278798, -3164447416, -3044756963]] 
 ![![29, 0, 0], ![18, 1, 0], ![16, 0, 1]] where
  M :=![![![-55662278798, -3164447416, -3044756963], ![-231401529188, -13155371769, -12657789664], ![-182647621319, -10383671057, -9990924353]]]
  hmulB := by decide  
  f := ![![![-235609, 1957, 69323]], ![![35434, -42699, 43298]], ![![-170281, 45486, -5734]]]
  g := ![![![1724616762, -3164447416, -3044756963], ![7169648182, -13155371769, -12657789664], ![5659077495, -10383671057, -9990924353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-282, 26, 53]] ![![-282, 26, 53]]
  ![![235609, -1957, -69323]] where
 M := ![![![235609, -1957, -69323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![235609, -1957, -69323]] ![![-55662278798, -3164447416, -3044756963]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5637, 1101, 323]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-5637, 1101, 323]] 
 ![![31, 0, 0], ![0, 31, 0], ![29, 6, 1]] where
  M :=![![![-5637, 1101, 323], ![24548, -9381, 4404], ![77539, -10378, -10482]]]
  hmulB := by decide  
  f := ![![![-4646334, -264148, -254157]], ![![-19315932, -1098127, -1056592]], ![![-8576953, -487607, -469164]]]
  g := ![![![-484, -27, 323], ![-3328, -1155, 4404], ![12307, 1694, -10482]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [23, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[21, 19], [29, 28], [18, 19], [13, 1]], ![[20, 12], [21, 3], [17, 12], [26, 30]]]
 h' := ![![[13, 30], [15, 9], [20, 11], [11, 22], [0, 1]], ![[0, 1], [8, 22], [8, 20], [18, 9], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [23, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![407, 19, 29]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -5, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4646334, 264148, 254157]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![4646334, 264148, 254157]] 
 ![![31, 0, 0], ![7, 1, 0], ![17, 0, 1]] where
  M :=![![![4646334, 264148, 254157], ![19315932, 1098127, 1056592], ![15246265, 866763, 833979]]]
  hmulB := by decide  
  f := ![![![5637, -1101, -323]], ![![481, 54, -215]], ![![590, -269, 161]]]
  g := ![![![-49141, 264148, 254157], ![-204291, 1098127, 1056592], ![-161249, 866763, 833979]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-5637, 1101, 323]] ![![4646334, 264148, 254157]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB124I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB124I0 : PrimesBelowBoundCertificateInterval O 1 31 124 where
  m := 11
  g := ![2, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB124I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
    · exact ![I31N0, I31N1]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I13N0, I13N1, I13N2, I17N1, I19N1, I23N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [], [], [I13N0, I13N1, I13N2], [I17N1], [I19N1], [I23N1], [I29N0, I29N0, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
